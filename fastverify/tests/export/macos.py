#!/usr/bin/python3 -I
"""tests/export/macos.py [WORK]: the export stage on macOS; no Mathlib, about 1 min.

run.sh runs on macOS as it is, without its two cases that copy the stage script. Here, in a copy of the tree, so that
the record of this machine is not touched: the recipe export/build-macos.sh, and with the programs it records the
native exporter in the macOS sandbox (lib/macos/stage.sh) on a project with a dependency package, the closure guard,
the rules of the record, a missing option and a toolchain path through a link, and the official exporter as the
fallback.
Prints one PASS/FAIL row per case and a final RESULT line; exit 0 iff all pass. SKIP off macOS, without a toolchain or
without the pinned official exporter.
"""
import hashlib, json, os, shutil, subprocess, sys

FV = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
sys.path.insert(0, FV + "/build/test")
import macos as build   # the project with a dependency package, the stage runner and the rows   # noqa: E402


def export(stage, out, lp, targets, proj, *args):   # export.sh -> (exit status, its JSON record, OUT was written)
    p = build.run([stage, "--lean-path", lp, "--module", "Main", "--targets-nl", targets, "--toolchain", build.TC,
                   "--project", proj, "--out", out, *args])
    try:
        return p.returncode, json.loads(p.stdout.strip().splitlines()[-1]), os.path.exists(out)
    except (ValueError, IndexError):
        return p.returncode, {"native": {"decline_reason": p.stdout + p.stderr}}, os.path.exists(out)


def cases(work):
    pins = json.load(open(FV + "/config/components.json"))["lean_toolchains"].values()
    exporter = [t["official_lean4export"]["path"] for t in pins if t["prefix"] == build.TC][0]
    if not os.path.exists(exporter):
        print(f"SKIP export-macos: no official exporter at {exporter}"); return
    tree = work + "/tree/fastverify"; stage = tree + "/export/export.sh"
    record = tree + "/config/export-macos.env"; judge = tree + "/config/pins-macos.env"
    for part in ("build", "export", "lib", "config", "tools/guard/fvguard.py"):
        os.makedirs(os.path.dirname(f"{tree}/{part}"), exist_ok=True)
        (shutil.copytree if os.path.isdir(f"{FV}/{part}") else shutil.copy)(f"{FV}/{part}", f"{tree}/{part}")
    shutil.copytree(FV + "/../sources/lean4export-native", work + "/tree/sources/lean4export-native",
                    ignore=shutil.ignore_patterns(".lake"))
    if os.path.exists(record):
        os.unlink(record)
    build.write(judge, "PIN gruszka 00 /the/record/of/the/judge\n")   # another stage's file: never the recipe's
    made = build.workspace(work)
    if not made:
        return
    ws, dep, require, manifest, uses = made
    proj = build.project(work + "/proj", uses, require, manifest)
    rc, rec = build.stage("official-build.sh", proj, ws, "--lean-path-out", proj + ".lp")
    if rc != 0:
        build.row("official build of the test project", False, rec.get("detail")); return
    lp = open(proj + ".lp").read(); binds = proj + "-log/binds.tsv"; targets = work + "/targets"
    build.write(targets, "usesDep\n")
    build.write(work + "/missing", "noSuchTheorem\n")

    # without a record: the official exporter, in the sandbox
    pre = build.run([stage, "--preflight", build.TC])
    build.row("no record: --preflight fails and names the recipe", pre.returncode == 1
              and "build-macos.sh" in pre.stderr, pre.stderr)
    official = work + "/official/solution.export"
    rc, rec, written = export(stage, official, lp, targets, proj, "--binds", binds, "--official-fallback")
    build.row("no record: the official exporter writes the export", rc == 0 and rec.get("exporter") == "official"
              and written, rec)
    direct = subprocess.run([exporter, "Main", "--", "usesDep"], cwd=proj, capture_output=True,
                            env={"PATH": build.TC + "/bin:/usr/bin:/bin", "LEAN_PATH": lp, "LEAN_ABORT_ON_PANIC": "1"})
    build.row("the same bytes as the official exporter outside the sandbox", written and direct.returncode == 0
              and open(official, "rb").read() == direct.stdout, f"{len(direct.stdout)} bytes")

    # the recipe, then the native exporter
    made = build.run([tree + "/export/build-macos.sh", work + "/built"])
    lines = open(record).read().splitlines() if made.returncode == 0 and os.path.exists(record) else []
    build.row("the recipe builds and records the native exporter and the closure guard",
              [ln.split()[0] for ln in lines] == ["#", "SRC", "PIN", "SRC", "PIN"], made.stdout + made.stderr)
    build.row("the recipe leaves the judge's record as it was",
              open(judge).read() == "PIN gruszka 00 /the/record/of/the/judge\n", open(judge).read())
    if not lines:
        return
    pre = build.run([stage, "--preflight", build.TC])
    build.row("--preflight passes with the record", pre.returncode == 0, pre.stderr)
    os.symlink(build.TC, work + "/toolchain")   # (the pins are looked up by the canonical path)
    pre = [build.run([stage, "--preflight", tc]) for tc in (work + "/toolchain", build.TC + "/")]
    build.row("--preflight passes with the toolchain through a link and with a trailing slash",
              [p.returncode for p in pre] == [0, 0], [p.stderr for p in pre])
    native = work + "/native/solution.export"
    rc, rec, written = export(stage, native, lp, targets, proj, "--binds", binds, "--verify")
    build.row("the native exporter writes the export: the official exporter's bytes", rc == 0 and written
              and (rec.get("exporter"), rec.get("verify")) == ("native", "identical")
              and open(native, "rb").read() == direct.stdout, rec)
    one = work + "/one/solution.export"
    rc, rec, written = export(stage, one, lp, targets, proj, "--binds", binds, "--threads", "1")
    build.row("the same bytes with one thread", rc == 0 and written and rec.get("exporter") == "native"
              and open(one, "rb").read() == direct.stdout, rec)
    fallback = ("--binds", binds, "--official-fallback")
    rc, rec, written = export(stage, work + "/nobinds/solution.export", lp, targets, proj, "--official-fallback")
    build.row("without --binds the dependency's checkout is not readable: no export", rc == 2 and not written, rec)
    rc, rec, written = export(stage, work + "/missing-out/solution.export", lp, work + "/missing", proj, *fallback)
    build.row("a failing exporter is exit 2, never exit 1", rc == 2 and not written, rec.get("official"))
    rc, rec, written = export(stage, work + "/ro/solution.export", lp, targets, proj, *fallback, "--ro", ws)
    why = str(rec["native"]["decline_reason"])
    build.row("--ro is refused", rc == 2 and not written and "macOS" in why, why)
    p = build.run([stage, "--lean-path", lp, "--module", "Main", "--targets-nl", targets, "--toolchain", build.TC,
                   "--project", proj])   # (the release's test of the options spells the name with ${v,,})
    build.row("a missing required option is named under bash 3.2, exit 2", p.returncode == 2
              and "export: --out missing" in p.stderr and '"decline_reason": "usage"' in p.stdout, p.stderr)

    # --verify compares nothing when the official exporter cannot run
    config = tree + "/config/components.json"; good = open(config).read()
    build.write(config, good.replace(hashlib.sha256(open(exporter, "rb").read()).hexdigest(), "0" * 64))
    rc, rec, written = export(stage, work + "/verify/solution.export", lp, targets, proj, "--binds", binds, "--verify")
    why = str(rec["native"]["decline_reason"])
    build.row("--verify without the official exporter is exit 2, not a difference", rc == 2 and not written
              and "did not finish" in why, why)
    build.write(config, good)

    # two recorded programs that are not the exporter: one leaves out a declaration of the complete export, one
    # fails after the log line that ends a run of the exporter
    out = open(native).read().splitlines(keepends=True)
    drop = [i for i, ln in enumerate(out) if ln.startswith('{"def":')][0]
    build.write(proj + "/incomplete.export", "".join(out[:drop] + out[drop + 1:]))
    shutil.copy(native, proj + "/complete.export")
    real = [ln for ln in lines if ln.startswith("PIN lean4export_native ")][0]

    def fake(name, run):   # export.sh with this shell script recorded as the native exporter
        script = f"{work}/{name}.sh"   # its first line answers the preflight, which looks for a definition
        build.write(script, f"""#!/bin/sh\n[ "$*" != "Init -- Nat.add" ] || exec echo '{{"def":0}}'\n{run}\n""")
        os.chmod(script, 0o755)
        faked = f"PIN lean4export_native {hashlib.sha256(open(script, 'rb').read()).hexdigest()} {script}"
        build.write(record, "\n".join(lines).replace(real, faked) + "\n")
        return export(stage, f"{work}/{name}/solution.export", lp, targets, proj, "--binds", binds)
    rc, rec, written = fake("incomplete", "exec cat incomplete.export")
    why = str(rec["native"]["decline_reason"])
    build.row("the closure guard declines an export with a declaration left out", rc == 2 and not written
              and why.startswith("closure guard:"), why)
    done = "lean4export (native) [0.10s wall, 0.10s cpu, 0.10s thread] done: names 1"
    rc, rec, written = fake("late", f"cat complete.export; echo '{done}' >&2; sleep 2; exit 1")
    build.row("an exporter that fails after its last log line gives no export", rc == 2 and not written, rec)

    # a program built from other sources is not used
    source = [ln for ln in lines if ln.startswith("SRC lean4export_native ")][0]
    build.write(record, "\n".join(lines).replace(source, source[:-1] + ("0" if source[-1] != "0" else "1")) + "\n")
    pre = build.run([stage, "--preflight", build.TC])
    rc, rec, written = export(stage, work + "/stale/solution.export", lp, targets, proj, *fallback)
    build.row("a program recorded with another source fingerprint is not used", pre.returncode == 1
              and "build-macos.sh" in pre.stderr and rc == 0 and rec.get("exporter") == "official", pre.stderr)
    build.write(record, "\n".join(lines) + "\n")

    # run.sh's case of an internal error, on the copy: exit 2, never 1
    text = open(stage).read(); line = "T0=$(date +%s.%N)\n"
    build.write(stage, text.replace(line, line[:-1] + '; echo "$FV_INJECTED_UNBOUND"\n'))
    rc, rec, written = export(stage, work + "/internal/solution.export", lp, targets, proj, "--binds", binds)
    build.row("an internal error of the stage script is exit 2", text.count(line) == 1 and rc == 2 and not written
              and "internal error" in str(rec.get("detail")), rec)

    stray = [os.path.join(d, f) for d, _, fs in os.walk(work) for f in fs if ".export.partial." in f]
    build.row("no partial output is left", not stray, stray)
    build.row("no process and no private directory of these tests is left", not build.left(work + "/"),
              build.left(work + "/"))


def main():
    work = build.start("export-macos")
    if work:
        cases(work)
    print(f"RESULT pass={build.counts['PASS']} fail={build.counts['FAIL']}")
    return 1 if build.counts["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
