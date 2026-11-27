#!/usr/bin/python3 -I
"""tests/macos-sandbox/run.py: the macOS sandbox launcher lib/macos/sandbox-run.py and the macOS branch of
lib/budget.py. Exercises the profile with private fixtures, kernel-spelled grants, command startup and exit statuses.
Prints PASS/FAIL rows and a RESULT line; SKIP on other systems."""
import ctypes
import errno
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tempfile
import time

FV = Path(__file__).resolve().parents[2]


def denied(operation):
    try:
        operation()
    except OSError as error:
        return error.errno in (errno.EACCES, errno.EPERM)
    return False


def inside(root, outside):
    """Runs in the sandbox; one line per probe: 1 or 0, then its name. outside = a process that is not in it."""
    lib = ctypes.CDLL(None, use_errno=True)
    buffer = ctypes.create_string_buffer(1 << 16)

    def sysctl(name, *numbers):   # query the required size without retrieving the contents
        size, none = ctypes.c_size_t(), ctypes.c_size_t(0)
        if name:
            failed = lib.sysctlbyname(name.encode(), None, ctypes.byref(size), None, none)
        else:
            mib = (ctypes.c_int * len(numbers))(*numbers)
            failed = lib.sysctl(mib, len(mib), None, ctypes.byref(size), None, none)
        if failed:
            raise OSError(ctypes.get_errno(), "sysctl")

    def child_signalled():
        child = os.fork()
        if child == 0:
            time.sleep(10)   # ends by itself where the signal is refused
            os._exit(0)
        try:
            os.kill(child, signal.SIGTERM)
        except OSError:
            return False
        return os.WTERMSIG(os.waitpid(child, 0)[1]) == signal.SIGTERM

    def bind(kind):
        with socket.socket(socket.AF_INET, kind) as s:
            s.bind(("127.0.0.1", 0))

    def connect():
        with socket.socket() as s:
            s.connect(("127.0.0.1", 9))

    def send():
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.sendto(b"probe", ("127.0.0.1", 9))

    def ipc():
        with socket.socket(socket.AF_UNIX) as s:
            s.connect(str(root / "write/socket"))

    def open_dir(path):   # check permission to open for reading without collecting directory contents
        os.close(os.open(path, os.O_RDONLY | os.O_DIRECTORY))

    def random_byte(path):
        with open(path, "rb", buffering=0) as device:
            return len(device.read(1)) == 1

    def directory_chmod():
        path = root / "write/mode"
        path.mkdir(mode=0o700)
        path.chmod(0o750)
        return stat.S_IMODE(path.stat().st_mode) == 0o750

    def immutable_flag():
        path = root / "write/immutable"
        os.chflags(path, path.stat().st_flags | stat.UF_IMMUTABLE)
        return bool(path.stat().st_flags & stat.UF_IMMUTABLE)

    def copy_tree():
        src = root / "write/source"
        src.mkdir()
        (src / "member").write_text("member")
        dst = shutil.copytree(src, root / "write/copied-tree")
        return (dst / "member").read_text() == "member"

    def copy_file():
        dst = root / "write/copied-file"
        shutil.copy2(root / "input", dst)
        return dst.read_text() == "input"

    def clone():
        if lib.clonefile(os.fsencode(root / "home/.ssh/marker"), os.fsencode(root / "write/cloned"), 0):
            raise OSError(ctypes.get_errno(), "clonefile")

    def by_number():   # the same file as /.vol/DEVICE/INODE
        st = (root / "home/.ssh/marker").stat()
        Path(f"/.vol/{st.st_dev}/{st.st_ino}").read_bytes()

    probes = [
        ("granted file is readable", lambda: (root / "input").read_text() == "input"),
        ("granted directory is writable", lambda: (root / "write/result").write_text("allowed") == 7),
        ("metadata is visible outside grants", lambda: (root / "home/.ssh/marker").stat().st_size == 14),
        ("root directory is readable", lambda: open_dir("/") is None),
        ("system runtime directories are readable", lambda: all(open_dir(p) is None for p in
            ("/bin", "/usr/bin", "/usr/lib", "/System/Library/Frameworks"))),
        ("random devices are readable", lambda: random_byte("/dev/random") and random_byte("/dev/urandom")),
        ("/dev/null is readable and writable", lambda: Path("/dev/null").read_bytes() == b""
         and Path("/dev/null").write_bytes(b"x") == 1),
        ("file outside the grants is not readable", lambda: denied((root / "home/.ssh/marker").read_bytes)),
        ("no write outside the grants", lambda: denied(lambda: (root / "outside").write_text("x"))),
        ("no write into a read-only grant", lambda: denied(lambda: (root / "input").write_text("x"))),
        ("no hard link from a read-only grant into a writable one",
         lambda: denied(lambda: os.link(root / "input", root / "write/linked"))),
        ("no clone of a file outside the grants", lambda: denied(clone)),
        ("no rename of a file outside the grants into a writable grant",
         lambda: denied(lambda: os.rename(root / "home/.ssh/marker", root / "write/renamed"))),
        ("a file outside the grants is not readable by its number either (/.vol)", lambda: denied(by_number)),
        ("the text of a symbolic link outside the grants is readable (metadata)",
         lambda: os.readlink(root / "home/.ssh/link") == "where it leads"),
        ("no document opened through LaunchServices",
         lambda: subprocess.run(["/usr/bin/open", "-g", str(root / "input")], capture_output=True).returncode != 0),
        ("writable file accepts the user-immutable flag", immutable_flag),
        ("shutil.copy2 copies into a writable grant", copy_file),
        ("shutil.copytree copies into a writable grant", copy_tree),
        ("writable regular file can change mode", lambda: (root / "write/result").chmod(0o700) is None),
        ("writable directory can change mode", directory_chmod),
        ("no TCP bind", lambda: denied(lambda: bind(socket.SOCK_STREAM))),
        ("no UDP bind", lambda: denied(lambda: bind(socket.SOCK_DGRAM))),
        ("no connect", lambda: denied(connect)),
        ("no datagram sent", lambda: denied(send)),
        ("no connection to a host Unix socket", lambda: denied(ipc)),
        ("no signal to a process outside", lambda: denied(lambda: os.kill(outside, 0))),
        ("no arguments or environment of a process outside", lambda: denied(lambda: sysctl(None, 1, 49, outside))),
        ("no process table", lambda: denied(lambda: sysctl("kern.proc.all"))
         and lib.proc_listallpids(buffer, len(buffer)) <= 0),
        ("no connections of the host", lambda: denied(lambda: sysctl("net.inet.tcp.pcblist_n"))),
        ("a signal to its own child", child_signalled),
    ]
    dyld = Path("/System/Volumes/Preboot/Cryptexes/OS/System/Library/dyld")
    if dyld.is_dir():
        probes.append(("Cryptex dyld cache is readable", lambda: open_dir(dyld) is None))
    for name in ("Data", "Hardware", "Preboot", "Update", "VM", "xarts"):
        path = Path("/System/Volumes") / name
        if path.is_dir():
            probes.append((f"no directory read on {path}", lambda p=path: denied(lambda: open_dir(p))))
    for name, probe in probes:
        try:
            print(int(bool(probe())), name)
        except OSError as error:
            print(0, name, error)
    print("DONE")


def main():
    if sys.platform != "darwin":
        print("SKIP macos-sandbox: needs macOS")
        return 0
    import fcntl
    import resource

    if sys.argv[1:2] == ["--inside"]:
        inside(Path(sys.argv[2]), int(sys.argv[3]))
        return 0
    if sys.argv[1:2] == ["--fd-state"]:
        for fd in sys.argv[2:]:
            try:
                os.fstat(int(fd))
                print("open")
            except OSError as error:
                if error.errno != errno.EBADF:
                    raise
                print("closed")
        return 0
    npass = nfail = 0

    def row(name, ok, detail=""):
        nonlocal npass, nfail
        npass, nfail = (npass + 1, nfail) if ok else (npass, nfail + 1)
        print(("PASS " if ok else "FAIL ") + name + (": " + detail if detail else ""), flush=True)
    script = Path(__file__).resolve()
    developer = Path(subprocess.check_output(["/usr/bin/xcode-select", "-p"], text=True).strip())
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp).resolve()
        (work / "write").mkdir()
        (work / "home/.ssh").mkdir(parents=True)
        (work / "home/.ssh/marker").write_text("test data only")
        (work / "home/.ssh/link").symlink_to("where it leads")
        (work / "input").write_text("input")
        common = [str(FV / "lib/macos/sandbox-run.py"), "--read", str(work / "input"), "--read", str(work / "write"),
                  "--write", str(work / "write"), "--read", str(developer), "--read", str(script), "--"]
        env = {"HOME": str(work / "home"), "TMPDIR": str(work / "write"), "PATH": "/usr/bin:/bin"}
        probes = [str(developer / "usr/bin/python3"), "-I", str(script), "--inside", str(work), str(os.getpid())]

        def run(cmd, **kwargs):
            return subprocess.run(cmd, cwd=work / "write", env=env, capture_output=True, text=True,
                                  timeout=60, **kwargs)

        with socket.socket(socket.AF_UNIX) as listener:
            listener.bind(str(work / "write/socket"))
            listener.listen(1)
            flag_file = work / "write/immutable"
            flag_file.touch()
            original_flags = flag_file.stat().st_flags
            try:
                p = run(common + probes)
            finally:
                os.chflags(flag_file, original_flags)
        lines = p.stdout.splitlines()
        row("probes ran inside the sandbox", p.returncode == 0 and lines[-1:] == ["DONE"], p.stderr.strip()[-200:])
        for line in lines:
            if line != "DONE":
                row(line[2:], line.startswith("1 "))
        row("what the sandbox wrote is on the host, nothing else", (work / "write/result").is_file()
            and not (work / "outside").exists() and (work / "input").read_text() == "input")
        statuses = [0, 1, 2, 19, 126, 127]
        codes = [run(common + ["/bin/sh", "-c", 'exit "$1"', "sh", str(code)]).returncode for code in statuses]
        row("command exit status passed through", codes == statuses, str(codes))
        launcher = common[0]
        p = run([launcher, "--", "/usr/bin/env"])
        row("the default command environment is empty", p.returncode == 0 and p.stdout == "" and not p.stderr)
        assigned = {"LEANC_OPTS": "a b=c", "EMPTY": "", "PATH": "/usr/bin:/bin", "PWD": "as given",
                    "SHLVL": "7", "_": "literal"}
        opts = [launcher, "--setenv", "EMPTY", "old", "--read", str(work / "input")]
        for name, value in assigned.items():
            opts.extend(["--setenv", name, value])
        p = run(opts + ["--", "env"])
        row("the command receives exactly the explicit environment",
            p.returncode == 0 and sorted(p.stdout.splitlines()) == sorted(f"{k}={v}" for k, v in assigned.items())
            and not p.stderr)
        for name in ("", "bad=name"):
            p = run([launcher, "--setenv", name, "value", "--", "/usr/bin/true"])
            row(f"invalid environment name {name!r} refused", p.returncode == 126 and "invalid --setenv" in p.stderr)

        ordered = ["/bin/sh", "-c", "printf one; printf two >&2; printf three"]
        p = run(common + ordered)
        row("the default command output streams remain separate",
            p.returncode == 0 and p.stdout == "onethree" and p.stderr == "two")
        p = run([*common[:-1], "--stderr-to-stdout", "--", *ordered])
        row("stderr merged before the command writes preserves order",
            p.returncode == 0 and p.stdout == "onetwothree" and p.stderr == "")
        p = run(common + ["/bin/sh", "-c", "kill -TERM $$"])
        row("command signal reported as 128 plus the signal number", p.returncode == 128 + signal.SIGTERM)

        equals_tool = work / "tool=argument"
        equals_tool.symlink_to("/usr/bin/printf")
        p = run([launcher, "--read", equals_tool, "--", equals_tool, "%s", "value=literal"])
        row("a program path containing equals executes directly", p.returncode == 0 and p.stdout == "value=literal")

        missing = str(work / "missing")
        for option in ("--read", "--write"):
            p = run([launcher, option, missing, "--", "/usr/bin/true"])
            row(f"missing {option} path refused during setup", p.returncode == 126 and missing in p.stderr)
        row("missing command argument returns 126", run([launcher, "--read", str(work)]).returncode == 126)
        (work / "abin").mkdir()   # (written as \b into the profile, a backspace would be read there as the letter b)
        for char in "\b\n\x1b\x7f":
            (work / f"a{char}in").mkdir()
            p = run([launcher, "--write", str(work / f"a{char}in"), "--", "/usr/bin/touch", str(work / "abin/made")])
            row(f"a granted path with the control character {char!r} is refused, and nothing is written beside it",
                p.returncode == 126 and "control character" in p.stderr and not (work / "abin/made").exists(), p.stderr)
        p = run([launcher, "--", "absent-macos-sandbox-program"])
        row("missing command on PATH returns 127", p.returncode == 127 and "sandbox-run:" in p.stderr)
        p = run(common + [missing])
        row("missing command returns 126 with a launcher diagnostic",
            p.returncode == 126 and "sandbox-run: could not start command" in p.stderr)
        row("non-executable granted input returns 126", run(common + [str(work / "input")]).returncode == 126)

        malformed = work / "non-executable-format"
        malformed.write_text("exit 1\n")
        malformed.chmod(0o700)
        p = run([launcher, "--read", str(malformed), "--", str(malformed)])
        row("an unrecognized executable format is a startup failure",
            p.returncode == 126 and "sandbox-run: could not start command" in p.stderr)

        p = run(["/usr/bin/sandbox-exec", "-p", "(version 1)(allow default)", launcher,
                 "--stderr-to-stdout", "--", "/usr/bin/printf", "started"])
        row("failure to apply a profile stops before the command starts",
            p.returncode == 126 and p.stdout == "" and "sandbox-run:" in p.stderr)

        binary = str(work / "Tool")
        shutil.copy("/usr/bin/true", binary)
        row("ungranted executable is refused", run([launcher, "--", binary]).returncode == 126)
        p = run([launcher, "--write", binary, "--", binary])
        row("write grant alone does not allow execution", p.returncode == 126)
        aliases = [("literal file", binary), ("Data volume alias", "/System/Volumes/Data" + binary)]
        alternate = str(work / "tOOL")
        if os.path.exists(alternate) and os.path.samefile(alternate, binary):
            aliases.append(("alternate case", alternate))
        else:
            print("SKIP alternate-case grant: temporary filesystem is case-sensitive")
        for label, alias in aliases:
            p = run([launcher, "--read", alias, "--", binary])
            row(f"read grant permits execution via {label}", p.returncode == 0)
        directory = str(work / "write")
        p = run([launcher, "--write", "/System/Volumes/Data" + directory, "--", "/usr/bin/touch", directory + "/alias"])
        row("Data volume alias grants writes below the directory",
            p.returncode == 0 and (work / "write/alias").exists())
        soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        for limit in (1048576, resource.RLIM_INFINITY):
            label = "unlimited" if limit == resource.RLIM_INFINITY else str(limit)
            if hard != resource.RLIM_INFINITY and (limit == resource.RLIM_INFINITY or limit > hard):
                print(f"SKIP soft descriptor limit {label}: hard limit is {hard}")
                continue
            p = run(["/bin/bash", "-c", 'ulimit -Sn "$1" && shift && exec "$@"', "bash", label,
                     *common, "/usr/bin/printf", "started"])
            row(f"command starts with soft descriptor limit {label}", p.returncode == 0 and p.stdout == "started",
                p.stderr.strip())

        fds = []
        try:
            for _ in range(12):
                fds.append(os.open("/dev/null", os.O_RDONLY))
            sampled = [fds[-1]]
            if hard == resource.RLIM_INFINITY or hard > 256:
                if soft != resource.RLIM_INFINITY and soft <= 256:
                    resource.setrlimit(resource.RLIMIT_NOFILE, (257, hard))
                fds.append(fcntl.fcntl(fds[0], fcntl.F_DUPFD, 256))
                sampled.append(fds[-1])
            else:
                print(f"SKIP descriptor above 255: hard limit is {hard}")
            python = str(developer / "usr/bin/python3")
            probe = [python, "-I", str(script), "--fd-state", *map(str, sampled)]
            before = run(probe, pass_fds=fds)
            after = run([python, "-I", *common, *probe], pass_fds=fds)
            for index, fd in enumerate(sampled):
                row(f"inherited descriptor {fd} is closed for the command", before.returncode == after.returncode == 0
                    and before.stdout.splitlines()[index:index + 1] == ["open"]
                    and after.stdout.splitlines()[index:index + 1] == ["closed"])
        finally:
            for fd in fds:
                os.close(fd)
            if resource.getrlimit(resource.RLIMIT_NOFILE)[0] != soft:
                resource.setrlimit(resource.RLIMIT_NOFILE, (soft, hard))

        # Exercise the real CLI boundary in a disposable interpreter, with an error before COMMAND can start.
        inject = """import builtins, runpy, subprocess, sys
from unittest.mock import patch
kind = getattr(builtins, sys.argv[1])
sys.argv = sys.argv[2:]
with patch.object(subprocess, "Popen", side_effect=kind("injected")):
    runpy.run_path(sys.argv[0], run_name="__main__")
"""
        for kind in ("OverflowError", "MemoryError", "KeyboardInterrupt"):
            p = run([sys.executable, "-I", "-c", inject, kind, launcher, "--", "/usr/bin/true"])
            row(f"launcher {kind} gives no verdict", p.returncode == 126 and f"sandbox-run: {kind}" in p.stderr
                and "Traceback" not in p.stderr)
    host = json.loads(subprocess.check_output(["/usr/bin/python3", "-I", str(FV / "lib/budget.py"), "host"]))
    row("budget.py host", host["build_jobs"] >= 1 and 0 < host["memory_budget"] <= host["mem_total"]
        and host["cpu_budget"] >= 1 and "limited_by" in host,
        f"build_jobs={host['build_jobs']} memory_budget={host['memory_budget']} cpu_budget={host['cpu_budget']}")
    print(f"RESULT pass={npass} fail={nfail}")
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
