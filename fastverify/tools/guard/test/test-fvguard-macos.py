#!/usr/bin/python3 -I
"""test-fvguard-macos.py: the macOS backend of tools/guard/fvguard.py. Every probe is bounded: it ends by itself
within seconds and uses at most 48 MB.
  - an honest command: its exit status is passed through, no violation
  - memory (physical footprint), processes, the last bytes of output: the right violation, exit 125
  - options that macOS cannot enforce (--cgroup, --nproc, the per-process limits, a Linux memory metric): refused,
    exit 2, no report
  - a command that cannot be started: violation "guard", exit 125, a report
  - a read or write failure forwarding the command's output: violation "guard" and the affected stream
  - --owner-pid: the command's workers die when the owner, the guard or the command itself is killed; a worker whose
    parent exited still counts for --mem; thousands of short-lived children are no violation
  - library run(): a child of the command is gone after a wall-time violation
Prints PASS/FAIL rows and a RESULT line; SKIP on other systems."""
import importlib.util
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tempfile
import time

GUARD = Path(__file__).resolve().parents[1] / "fvguard.py"
npass = nfail = 0


def row(name, ok, detail):
    global npass, nfail
    npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
    print(("PASS " if ok else "FAIL ") + f"{name}: {detail}", flush=True)


def cli(limits, command):
    with tempfile.TemporaryDirectory() as directory:
        report = Path(directory) / "result.json"
        p = subprocess.run([sys.executable, "-I", str(GUARD), "--grace", "0", "--poll", ".025", "--json", str(report),
                            *limits, "--", *command], capture_output=True, text=True, timeout=10)
        return p.returncode, json.loads(report.read_text()) if report.exists() else {}


def startup_diagnostics(fvguard):
    """The same subprocess error must identify which launch failed, even when logs truncate the exception."""
    import errno
    import io
    from contextlib import redirect_stderr
    from unittest.mock import patch

    def unavailable(*args, **kwargs):
        raise OSError(errno.EBADF, os.strerror(errno.EBADF))

    with tempfile.TemporaryDirectory() as directory:
        report = Path(directory) / "result.json"
        for options, site in (([], "_run_cli"), (["--owner-pid", str(os.getpid())], "_darwin_owner_group")):
            with patch.object(subprocess, "Popen", unavailable), redirect_stderr(io.StringIO()):
                rc = fvguard.main([*options, "--json", str(report), "--", "/usr/bin/true"])
            result = json.loads(report.read_text())
            detail = result["detail"].partition("[Errno 9]")
            row(f"injected startup error identifies {site}", (rc, result["violation"], result["returncode"]) ==
                (125, "guard", None) and site in detail[0] and "unavailable" in detail[0] and bool(detail[1]),
                result["detail"])


def output_cases(fvguard):
    import threading
    from contextlib import redirect_stdout
    from unittest.mock import patch

    command = ["/bin/sh", "-c", "printf out; printf err >&2; exit 1"]
    with tempfile.TemporaryDirectory() as directory, open(os.devnull, "rb") as unwritable:
        path = Path(directory) / "report"
        args = ["--json", str(path), "--violation-exit", "79", "--", *command]
        for failed in (None, "stdout", "stderr"):
            destinations = {name: unwritable if name == failed else subprocess.PIPE for name in ("stdout", "stderr")}
            p = subprocess.run([sys.executable, "-I", str(GUARD), *args], **destinations, timeout=10)
            report = json.loads(path.read_text())
            if failed is None:
                ok = (p.returncode, p.stdout, p.stderr, report["violation"], report["returncode"]) == (
                    1, b"out", b"err", None, 1)
            else:
                ok = (p.returncode, report["violation"], report["returncode"], report.get("incomplete_output")) == (
                    79, "guard", 1, [failed])
            row("forwarded output" if not failed else f"unwritable {failed}", ok,
                f"rc={p.returncode} detail={report['detail']}")

        write = os.write
        with (path.parent / "output").open("w+") as output:
            def short_write(fd, data):
                return write(fd, data[:2] if fd == output.fileno() else data)

            with redirect_stdout(output), patch.object(os, "write", short_write):
                rc = fvguard.main(["--json", str(path), "--", "/bin/echo", "abcdef"])
            output.seek(0)
            received = output.read()
        report = json.loads(path.read_text())
        row("partial output writes complete", (rc, report["violation"], received) == (0, None, "abcdef\n"),
            f"rc={rc} bytes={len(received)}")

        popen = subprocess.Popen

        def failed_read(size):
            raise OSError("test input read failed")

        def broken_pipe(*args, **kwargs):
            child = popen(*args, **kwargs)
            child.stdout.read1 = failed_read
            return child

        with patch.object(subprocess, "Popen", broken_pipe):
            rc = fvguard.main(["--json", str(path), "--", "/usr/bin/true"])
        report = json.loads(path.read_text())
        row("unreadable stdout pipe", (rc, report["violation"], report["returncode"],
                                      report.get("incomplete_output")) == (125, "guard", 0, ["stdout"]),
            f"rc={rc} detail={report['detail']}")

        release, drained = threading.Event(), threading.Event()

        def slow_pipe(*args, **kwargs):
            child = popen(*args, **kwargs)
            read = child.stdout.read1

            def delayed_eof(size):
                release.wait(10)  # longer than the guard's bounded pump join
                data = read(size)
                drained.set()
                return data

            child.stdout.read1 = delayed_eof
            return child

        try:
            with patch.object(subprocess, "Popen", slow_pipe):
                rc = fvguard.main(["--json", str(path), "--", "/usr/bin/true"])
        finally:
            release.set()
        report = json.loads(path.read_text())
        row("uncompleted stdout pump", drained.wait(2) and (rc, report["violation"], report["returncode"],
            report.get("incomplete_output")) == (125, "guard", 0, ["stdout"]),
            f"rc={rc} detail={report['detail']}")


def descendant_cases(guard):
    from unittest.mock import patch

    # Pure snapshots. Two group layouts exercise the standalone command and the separate owner watcher's group.
    root, worker, helper = 50, 51, 52
    for group in (root, 49):
        table = {root: (1, 0, group), worker: (2, root, group)}
        if group != root:
            table[group] = (4, 0, group)
        watch = guard.Watch(root, guard.Limits(mem=15, grace=0), process_group=group)

        def members(flavor, parent):
            field = 2 if flavor == 2 else 1  # PROC_PGRP_ONLY or PROC_PPID_ONLY
            return [pid for pid, info in table.items() if info[field] == parent]

        with patch.object(guard, "_darwin_member", side_effect=table.get), \
             patch.object(guard, "_darwin_pids", side_effect=members), \
             patch.object(guard, "_darwin_sample", return_value=(10, 1, 0)), \
             patch.object(guard.os, "killpg") as group_signal, patch.object(guard, "_darwin_signal") as deliver:
            started = watch.pids()
            del table[root]
            table[worker] = (2, 1, 80)
            table[helper] = (3, worker, 80)
            violation = watch.check_once()
            watch._darwin_kill_known()
            targets = {call.args[:2] for call in deliver.call_args_list}
            row(f"group {group}: remembered worker and its new child count and receive cleanup",
                sorted(started) == [root, worker] and violation and violation[0] == "mem" and watch.peak["mem"] == 20
                and targets == {(worker, 2), (helper, 3)} and group_signal.called, f"targets={sorted(targets)}")
            table[worker] = (22, 1, 80)  # the PID has since been reused by an unrelated process
            deliver.reset_mock()
            remaining = watch.pids()
            watch._darwin_kill_known()
            row(f"group {group}: reused worker PID excluded", remaining == [helper]
                and [call.args[0] for call in deliver.call_args_list] == [helper], str(remaining))

    with subprocess.Popen(["/bin/sleep", "2"]) as child:
        born = guard._darwin_member(child.pid)[0]
        ignored = not guard._darwin_signal(child.pid, (-1, 0), signal.SIGTERM)
        delivered = guard._darwin_signal(child.pid, born, signal.SIGTERM)
        rc = child.wait(timeout=3)
        row("kernel generation check for individual signal", ignored and delivered and rc == -signal.SIGTERM,
            f"mismatched birth ignored={ignored}, matching birth delivered={delivered}, status={rc}")

    # Start both fixtures ourselves. Seed the remembered identity to exercise real cleanup independently of poll timing.
    with subprocess.Popen(["/usr/bin/true"], start_new_session=True) as command, \
            subprocess.Popen(["/bin/sleep", "4"]) as worker:
        watch = guard.Watch(command.pid, guard.Limits(grace=0), process_group=command.pid)
        watch._darwin_birth[worker.pid] = guard._darwin_member(worker.pid)[0]
        guard._wait_exit(command.pid)  # hold the exited group leader's PID throughout cleanup
        watch.kill_tree()
        rc, worker_rc = command.wait(), worker.wait()
        row("successful command cleanup ends a remembered worker outside its group",
            rc == 0 and worker_rc == -signal.SIGKILL, f"command={rc} worker={worker_rc}")

    watch = guard.Watch(root, guard.Limits(), process_group=root)
    with patch.object(watch, "check_once", side_effect=RuntimeError("monitor fixture")), \
         patch.object(watch, "_darwin_kill_known", return_value=None) as cleanup:
        watch.run()
        row("unexpected monitor error gives no verdict", watch.violation == "guard" and cleanup.called, watch.detail)


def owner_case(fvguard, terminate):
    """A worker of the command must be gone after `terminate` (the owner, the guard or the command) is killed."""
    child = ("import os, subprocess, sys; p = subprocess.Popen(['/bin/sleep', '6']); "
             "open(sys.argv[1], 'w').write(f'{os.getpid()} {p.pid}'); p.wait()")
    with subprocess.Popen(["/bin/sleep", "8"]) as owner, tempfile.TemporaryDirectory() as directory:
        try:
            marker = Path(directory) / "workers"   # a file: the guard's line buffering must not delay the fixture
            with subprocess.Popen([sys.executable, "-I", str(GUARD), "--owner-pid", str(owner.pid), "--",
                                   sys.executable, "-c", child, str(marker)],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.PIPE) as guard:
                deadline = time.monotonic() + 3
                while not marker.exists() or not marker.stat().st_size:
                    if guard.poll() is not None or time.monotonic() > deadline:
                        return False, "the command did not start"
                    time.sleep(.02)
                command, worker = map(int, marker.read_text().split())
                os.kill({"owner": owner.pid, "guard": guard.pid, "command": command}[terminate], signal.SIGKILL)
                status = guard.wait(timeout=3)
                while fvguard.alive(worker) and time.monotonic() < deadline:
                    time.sleep(.02)
                gone, quiet = not fvguard.alive(worker), guard.stderr.read() == b""
                return (status == (-9 if terminate == "guard" else 137) and gone and quiet,
                        f"guard status {status}, worker gone {gone}, no message {quiet}")
        finally:
            if owner.poll() is None:
                owner.terminate()


def cases(fvguard):
    descendant_cases(fvguard)
    startup_diagnostics(fvguard)
    output_cases(fvguard)
    rc, report = cli([], ["/bin/sh", "-c", "exit 3"])
    row("exit-status", (rc, report.get("violation", "")) == (3, None), f"rc={rc} violation={report.get('violation')}")
    rc, report = cli(["--mem", "36M"], [sys.executable, "-c", "import time; b=bytearray(48<<20); time.sleep(1.5)"])
    peak, metric = report.get("peak", {}).get("mem", 0), report.get("limits", {}).get("mem_metric")
    row("memory", (rc, report.get("violation"), metric) == (125, "mem", "footprint") and peak > 36 << 20,
        f"rc={rc} violation={report.get('violation')} peak={peak} metric={metric}")
    rc, report = cli(["--procs", "1"], [sys.executable, "-c", "import subprocess; subprocess.run(['/bin/sleep','2'])"])
    row("processes", (rc, report.get("violation")) == (125, "procs"), f"rc={rc} violation={report.get('violation')}")
    rc, report = cli(["--out", "2"], ["/bin/echo", "abc"])
    row("last-output-counted", (rc, report.get("violation")) == (125, "output"),
        f"rc={rc} violation={report.get('violation')}")
    for limits in (["--data", "128M"], ["--cgroup", "systemd-user"], ["--nproc", "7"], ["--mem-metric", "pss"],
                   ["--cpu", "5"], ["--fsize", "1M"], ["--nofile", "64"]):
        rc, report = cli(limits, ["/usr/bin/true"])
        row("refused " + " ".join(limits), (rc, report) == (2, {}),
            f"rc={rc} report={'none' if not report else 'written'}")
    rc, report = cli([], ["/nonexistent/command"])
    row("command that cannot be started", (rc, report.get("violation"), report.get("returncode", 0))
        == (125, "guard", None), f"rc={rc} violation={report.get('violation')}")
    for terminate in ("owner", "guard", "command"):
        row(f"owner-pid: {terminate} killed", *owner_case(fvguard, terminate))
    owned = ["--owner-pid", str(os.getpid())]
    # the subshell starts the worker and exits: the worker is a child of launchd then, and still in the command's group
    worker = shlex.quote(sys.executable) + " -c 'import time; b = bytearray(48 << 20); time.sleep(4)'"
    rc, report = cli(owned + ["--mem", "36M"], ["/bin/sh", "-c", f"({worker} &)\nsleep 3"])
    row("owner-pid: a worker whose parent exited still counts", (rc, report.get("violation")) == (125, "mem"),
        f"rc={rc} violation={report.get('violation')} peak={report.get('peak', {}).get('mem')}")
    forks = "import os\nfor i in range(1500):\n    os.waitpid(os.fork() or os._exit(0), 0)"
    runs = [cli(owned + ["--poll", ".001"], [sys.executable, "-c", forks]) for _ in range(2)]
    row("owner-pid: short-lived children are no violation", all((rc, report.get("violation", "")) == (0, None)
                                                                for rc, report in runs),
        "; ".join(f"rc={rc} violation={report.get('violation')}" for rc, report in runs))
    with tempfile.TemporaryDirectory() as directory:
        marker = Path(directory) / "child.pid"
        script = ("import subprocess, sys, time; p=subprocess.Popen(['/bin/sleep','4']); "
                  "open(sys.argv[1],'w').write(str(p.pid)); time.sleep(2)")
        r = fvguard.run([sys.executable, "-c", script, str(marker)], fvguard.Limits(wall=.5, poll=.025))
        gone = not fvguard.alive(int(marker.read_text()))
        row("library run(): wall", (r.returncode, r.violation) == (None, "wall") and gone,
            f"returncode={r.returncode} violation={r.violation} child gone {gone}")
    status_cases(fvguard)


def status_cases(fvguard):
    from unittest.mock import patch
    rc, report = cli([], ["/bin/sh", "-c", "exit 1"])
    row("command exit 1 has matching report", rc == 1 and report.get("returncode") == 1 and
        report.get("violation", "") is None, f"rc={rc} violation={report.get('violation')}")
    for code in (0, 1, -255, 257):
        rc, report = cli(["--violation-exit", str(code)], ["/usr/bin/true"])
        row(f"reserved or out-of-range violation exit {code}", (rc, report) == (2, {}), f"rc={rc}")

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        occupied = root / "occupied"
        occupied.mkdir()
        for where, dest in (("open", root / "missing-dir/report"), ("replace", occupied)):
            p = subprocess.run([sys.executable, "-I", str(GUARD), "--json", str(dest), "--violation-exit", "79",
                                "--", "/bin/sh", "-c", "exit 1"], capture_output=True, text=True, timeout=10)
            row(f"report {where} failure gives no verdict", p.returncode == 79 and "cannot publish" in p.stderr
                and list(root.iterdir()) == [occupied], f"rc={p.returncode}")

    # Exercise the standalone CLI before it can start a child. Importing fvguard as a library keeps caller hooks.
    inject = """import ctypes, runpy, sys
from unittest.mock import patch
sys.argv = sys.argv[1:]
with patch.object(ctypes, 'CDLL', side_effect=MemoryError('injected')):
    runpy.run_path(sys.argv[0], run_name='__main__')
"""
    p = subprocess.run([sys.executable, "-I", "-c", inject, str(GUARD), "--", "/usr/bin/true"],
                       capture_output=True, text=True, timeout=10)
    row("unexpected initialization failure gives no verdict", p.returncode == 125 and "MemoryError" in p.stderr
        and "Traceback" not in p.stderr, f"rc={p.returncode}")

    for ownership in ([], ["--owner-pid", str(os.getpid())]):
        with tempfile.TemporaryDirectory() as directory:
            report, completed = Path(directory) / "result", Path(directory) / "completed"
            children = []

            def injected_start(watch):
                children.append(watch.root)
                raise OSError(9, "injected supervision error")

            sleeper = "import sys,time; time.sleep(3); open(sys.argv[1], 'w').close()"
            with patch.object(fvguard.Watch, "start", injected_start):
                rc = fvguard.main([*ownership, "--json", str(report), "--", sys.executable, "-c", sleeper,
                                   str(completed)])
            reaped = False
            if children:
                try:
                    os.waitpid(children[0], 0)  # a finite fixture; success here means the guard left a child
                except ChildProcessError:
                    reaped = True
            record = json.loads(report.read_text())
            detail = record.get("detail", "")
            row(f"injected supervision failure reaps child (owner={bool(ownership)})", rc == 125 and reaped
                and not completed.exists() and record.get("violation") == "guard" and record["returncode"] is None
                and 0 <= detail.find("injected_start") < detail.find("injected supervision error"),
                f"rc={rc} reaped={reaped} detail={detail}")


def main():
    if sys.platform != "darwin":
        print("SKIP test-fvguard-macos: needs macOS")
        return 0
    spec = importlib.util.spec_from_file_location("fvguard", GUARD)
    fvguard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fvguard)
    try:
        cases(fvguard)
    except subprocess.TimeoutExpired as late:
        row("every probe ends in time", False, str(late))
    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
