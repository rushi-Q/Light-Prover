#!/usr/bin/python3 -I
"""build/test/macos.py [WORK]: the macOS parts of the build stage (lib/macos/stage.sh); no Mathlib, about 2 min.

run.sh, merge.sh, premiseoff.sh and crash-retry.sh run on macOS as they are; their projects have no dependency.
Here: a project with a dependency package (a link on macOS, a bind mount on Linux), the LEAN_PATH rule for such links,
what the guard does in place of timeout and of bwrap --die-with-parent, the private directory of a sandbox start, and
the options and helpers that differ on macOS.
Prints one PASS/FAIL row per case and a final RESULT line; exit 0 iff all pass. SKIP off macOS or without a toolchain.
"""
import glob, json, os, runpy, shutil, signal, subprocess, sys, tempfile, time

FV = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
TC = os.path.realpath(os.environ.get("FV_TC") or os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1"))
ENV = {"PATH": "/usr/bin:/bin", "HOME": os.path.expanduser("~")}
URL = "https://example.invalid/dep"
counts = {"PASS": 0, "FAIL": 0}


def row(name, ok, detail=""):
    counts["PASS" if ok else "FAIL"] += 1
    print(("PASS " if ok else "FAIL ") + name + (": " + " ".join(str(detail).split())[:300] if detail else ""),
          flush=True)


def run(cmd, **kw):
    return subprocess.run(cmd, env=ENV, capture_output=True, text=True, **kw)


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)


def project(path, main, require="", manifest=None):
    write(path + "/lean-toolchain", "leanprover/lean4:v4.33.1\n")
    write(path + "/lakefile.toml", f'name = "p"\ndefaultTargets = ["Main"]\n{require}[[lean_lib]]\nname = "Main"\n')
    write(path + "/Main.lean", main)
    if manifest:
        write(path + "/lake-manifest.json", json.dumps(manifest))
    return path


def stage(script, proj, ws, *args):   # one build stage -> (exit status, its JSON record)
    p = run([FV + "/build/" + script, proj, ws, TC, "--log", proj + "-log", "--json", proj + ".json", *args])
    try:
        return p.returncode, json.load(open(proj + ".json"))
    except (OSError, ValueError):
        return p.returncode, {"detail": p.stdout + p.stderr}


def no_verdict(name, script, status, why, proj, ws, *args):   # the stage ends with exit 2, this status and this reason
    rc, rec = stage(script, proj, ws, *args)
    row(name, rc == 2 and rec.get("status") == status and why in str(rec.get("detail")), rec.get("detail"))


def helpers(script, *args):   # a shell with the helpers loaded as official-build.sh loads them, and its bindok
    pre = ('D=$1 PY=/usr/bin/python3 STAGE_OS=Darwin STAGE_PID=$$ STAGE_WALL=0; shift\n'
           'export D PY STAGE_OS STAGE_PID STAGE_WALL; . "$D/lib/macos/stage.sh"\n'
           'eval "$(sed -n "/^bindok()/,/^}/p" "$D/build/official-build.sh")"\n')
    return run(["/bin/bash", "-c", pre + script, "_", FV, *args]).returncode


def left(work):   # processes that still name the work directory, and private directories of a sandbox start in it
    return ([ln for ln in run(["/bin/ps", "-axo", "pid=,command="]).stdout.splitlines() if work in ln]
            + glob.glob(work + "/**/.fv-sandbox.*", recursive=True))


def workspace(work):
    """A packages workspace with one git dependency, built once (the stages' trusted input), and what a project that
    uses it consists of -> (workspace, dependency checkout, [[require]] text, manifest, Main.lean) or None."""
    ws = work + "/ws"; dep = ws + "/.lake/packages/dep"
    write(dep + "/lean-toolchain", "leanprover/lean4:v4.33.1\n")
    write(dep + "/lakefile.toml", 'name = "dep"\ndefaultTargets = ["Dep"]\n[[lean_lib]]\nname = "Dep"\n')
    write(dep + "/Dep.lean", "def depValue : Nat := 41\n")
    write(dep + "/.gitignore", ".lake\n")
    git = ["/usr/bin/git", "-c", "user.name=t", "-c", "user.email=t@example.invalid", "-C", dep]
    for c in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "x"]):
        subprocess.run(git + c, env=dict(ENV, GIT_CONFIG_GLOBAL="/dev/null"), check=True, capture_output=True)
    rev = run(git + ["rev-parse", "HEAD"]).stdout.strip()
    require = f'[[require]]\nname = "dep"\ngit = "{URL}"\nrev = "{rev}"\n'
    entry = {"type": "git", "name": "dep", "url": URL, "rev": rev, "inputRev": rev, "subDir": None, "scope": "",
             "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml", "inherited": False}
    manifest = {"version": "1.1.0", "packagesDir": ".lake/packages", "name": "p", "lakeDir": ".lake",
                "packages": [entry]}
    uses = "import Dep\ntheorem usesDep : depValue + 1 = 42 := rfl\n"
    project(ws, uses, require, manifest)
    built = subprocess.run([TC + "/bin/lake", "build"], cwd=ws, capture_output=True, text=True,
                           env={"PATH": TC + "/bin:/usr/bin:/bin", "HOME": work})
    if built.returncode != 0:
        row("test workspace builds", False, built.stdout + built.stderr)
        return None
    return ws, os.path.realpath(dep), require, manifest, uses


def start(name):   # the work directory, or None after a SKIP line
    if sys.platform != "darwin":
        print(f"SKIP {name}: needs macOS"); return None
    if run([FV + "/build/official-build.sh", "--preflight", TC]).returncode != 0:
        print(f"SKIP {name}: no pinned toolchain at {TC} (tools/configure.py)"); return None
    work = os.path.realpath(sys.argv[1] if len(sys.argv) > 1 else tempfile.mkdtemp(prefix=f"fv-{name}."))
    os.makedirs(work, exist_ok=True)
    return work


def cases(work):
    made = workspace(work)
    if not made:
        return
    ws, dep, require, manifest, uses = made

    # both builds of a project with the dependency: the same artifacts, the same LEAN_PATH
    src = project(work + "/src", uses, require, manifest)
    cmp_ = run([FV + "/build/test/cmp_official.sh", src, work + "/cmp", ws, TC]).stdout.strip().splitlines()[-1:]
    row("dependency as a link: official and fast build agree", cmp_ and cmp_[0].startswith("CMP: SAME"), cmp_)
    lp = {}
    for script in ("official-build.sh", "build.sh"):
        proj = project(f"{work}/{script}/proj", uses, require, manifest)
        rc, rec = stage(script, proj, ws, "--lean-path-out", proj + ".lp")
        lp[script] = open(proj + ".lp").read().replace(script, "") if rc == 0 else ""
    libdir = dep + "/.lake/build/lib/lean"
    row("LEAN_PATH names the dependency's checkout", libdir in lp["build.sh"].split(":"), lp["build.sh"])
    row("LEAN_PATH of the fast build is the official one's", "" != lp["build.sh"] == lp["official-build.sh"])
    if os.path.exists(work + "/WS"):   # a volume that ignores letter case, where Lake prints the spelling on disk
        both = [stage(script, project(f"{work}/case/{script}/proj", uses, require, manifest), work + "/WS",
                      "--lean-path-out", f"{work}/case/{script}/lp") for script in ("official-build.sh", "build.sh")]
        row("the packages workspace spelled in another letter case", [rc for rc, _ in both] == [0, 0], both)
    else:
        print("SKIP the packages workspace spelled in another letter case: this volume distinguishes case")

    # the rules of the links
    proj = work + "/build.sh/proj"; binds = proj + "-log/binds.tsv"; link = proj + "/.lake/packages/dep"
    check = 'printf %s "$1" > "$2/lp.txt"; macos_lpconfined "$2/lp.txt" "$3" "$4" "$5"'
    for name, entry, want in (("the checkout", libdir, 0), ("the link", link + "/.lake/build/lib/lean", 0),
                              ("the project", proj + "/.lake/build/lib/lean", 0),
                              ("another workspace directory", ws + "/.lake/build/lib/lean", 1),
                              ("a path with ..", proj + "/../ws", 1)):
        row(f"LEAN_PATH rule: {name} is {'accepted' if want == 0 else 'refused'}",
            helpers(check, entry, work, proj, TC, binds) == want)
    sandbox = 'macos_sandbox "$1" "$2" "$3" "" "" /usr/bin/true'
    row("sandbox starts with the dependency link in place", helpers(sandbox, proj, TC, binds) == 0)
    os.unlink(link); os.symlink(ws, link)
    row("LEAN_PATH rule: the checkout is refused once the link leads elsewhere",
        helpers(check, libdir, work, proj, TC, binds) == 1)
    row("no sandbox once the link leads elsewhere", helpers(sandbox, proj, TC, binds) == 126)
    fresh = project(work + "/deps/proj", uses, require, manifest)
    os.symlink(work, fresh + "/.lake")   # the binds line of this project: its destination is reached through a link
    moved = 'sed "s|$3/|$2/|" "$1" > "$2.tsv"; macos_deps "$2.tsv" "$2"'
    row("no dependency link through a symlink", helpers(moved, binds, fresh, proj) == 2)

    # the guard in place of timeout and of bwrap --die-with-parent; what is not Lake's own failure is no verdict
    sleeps = "#eval (IO.sleep 60000 : IO Unit)\n"
    # /tmp is a tmpfs in the Linux sandbox. Here the write is refused, and the project reports it in a second line
    refused = ('#eval show IO Unit from do\n  try IO.FS.writeFile "/tmp/fv-build-macos-refused" "x"\n'
               '  catch e => throw (IO.userError s!"cannot write the cache:\\n{e}")\n')
    no_verdict("--timeout ends the official build without a verdict", "official-build.sh", "ERROR", "(exit 125)",
               project(work + "/wall/proj", sleeps), ws, "--timeout", "3s")
    no_verdict("--timeout ends the fast build without a verdict", "build.sh", "DECLINED",
               "scheduler exit 125: fvguard: wall", project(work + "/wall2/proj", sleeps), ws, "--timeout", "0.05m")
    no_verdict("a guard that cannot start is not a failed build", "official-build.sh", "ERROR", "(exit 126)",
               project(work + "/guard/proj", uses, require, manifest), ws, "--timeout", "x")
    row("a guard that ends without its report is exit 126, whatever its status",
        helpers('PY=/usr/bin/false; macos_guarded "" "$1" "$2" -- /usr/bin/true', work, TC) == 126)
    no_verdict("a refused access is no verdict of the official build", "official-build.sh", "ERROR",
               "the sandbox refused an access", project(work + "/refused/proj", refused), ws)
    no_verdict("a refused access is no verdict of the fast build", "build.sh", "DECLINED", "scheduler exit 3: DECLINE",
               project(work + "/refused2/proj", refused), ws)
    row("nothing was written outside the sandbox", not os.path.lexists("/tmp/fv-build-macos-refused"))
    sched = run(["/usr/bin/python3", "-I", "-c", open(FV + "/build/sched.py").read(), "1", "--macos-budget", work],
                stdin=subprocess.DEVNULL)
    row("a scheduler without the host budget declines", sched.returncode == 3 and sched.stdout.startswith("DECLINE: "),
        sched.stdout + sched.stderr)
    proj = project(work + "/kill/proj", sleeps)
    p = subprocess.Popen([FV + "/build/official-build.sh", proj, ws, TC, "--log", proj + "-log"], env=ENV,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    deadline = time.time() + 60
    while time.time() < deadline and not any("Main.lean" in ln for ln in left(work + "/kill")):
        time.sleep(0.2)
    started = any("Main.lean" in ln for ln in left(work + "/kill"))
    os.killpg(p.pid, signal.SIGKILL); p.wait()
    deadline = time.time() + 10
    while time.time() < deadline and left(work + "/kill"):
        time.sleep(0.2)
    row("the build and its private directory end when the stage is killed", started and not left(work + "/kill"),
        left(work + "/kill"))

    # what a sandbox start hands to the guard (here a stand-in for the guard that notes its arguments)
    stub = work + "/stub"; os.makedirs(stub + "/tools/guard"); os.symlink(FV + "/lib", stub + "/lib")
    write(stub + "/tools/guard/fvguard.py", "import json, sys\na = sys.argv\n"
          "json.dump(a, open(__file__ + '.args', 'w'))\nopen(a[a.index('--json') + 1], 'w').write('{}')\n")
    rc = helpers('D=$1; macos_guarded "" "$2" "$3" -- /usr/bin/python3 -I -c pass', stub, work, TC)
    given = json.load(open(stub + "/tools/guard/fvguard.py.args")) if rc == 0 else []
    total = json.loads(run(["/usr/bin/python3", "-I", FV + "/lib/budget.py", "host"]).stdout)["mem_total"]
    row("the memory limit of a sandbox start is the machine's memory",
        ["--mem", str(total)] in [given[i:i + 2] for i in range(len(given))], total)
    # (with Xcode as the developer directory the launcher /usr/bin/python3 cannot start inside the sandbox)
    developer = run(["/usr/bin/xcode-select", "-p"]).stdout.strip()
    row("/usr/bin/python3 is started as the interpreter of the developer directory",
        developer + "/usr/bin/python3" in given and "/usr/bin/python3" not in given, given[-5:])
    row("/usr/bin/python3 starts inside the sandbox (without the substitution this fails, but only where Xcode is the "
        "developer directory)", helpers('macos_sandbox "" "$1" "" "" "" /usr/bin/python3 -I -c pass', TC) == 0)

    # the private directory of a sandbox start, the command line, the environment
    locks = ("import os, stat\nhome = os.environ['HOME']\nos.makedirs(home + '/d/e'); open(home + '/f', 'w').close()\n"
             "for lock in (lambda: os.chmod(home + '/d/e', 0o555), lambda: os.chmod(home + '/d', 0),\n"
             "             lambda: os.chflags(home + '/f', stat.UF_IMMUTABLE)):\n"
             "    try:\n        lock()\n    except OSError:\n        pass\n")
    os.makedirs(work + "/a=b/proj")
    rc = helpers('macos_sandbox "$1" "$2" "" "" "" /usr/bin/python3 -I -c "$3"', work + "/a=b/proj", TC, locks)
    row("the private directory goes with files that a build made unremovable", rc == 0 and not left(work + "/a=b"),
        left(work + "/a=b"))
    write(work + "/a=b/proj/run", '#!/bin/sh\n[ "$LEAN_NUM_THREADS" = 3 ] && exit 7\n')
    os.chmod(work + "/a=b/proj/run", 0o755)
    row("a command path with an equals sign starts, with the thread count in its environment",
        helpers('macos_sandbox "$1" "$2" "" "" 3 "$1/run"', work + "/a=b/proj", TC) == 7)
    shutil.copy("/usr/bin/true", work + "/a=b/true")   # a program outside the grants
    row("a command that the sandbox does not let start is exit 126, not a status of the command",
        helpers('macos_sandbox "$1" "$2" "" "" "" "$3"', work + "/a=b/proj", TC, work + "/a=b/true") == 126)

    # the premise-off helper, which the stage itself copies into the project: BSD cp writes through a link that leads
    # nowhere (GNU cp refuses one), and here the project ships such a link at the helper's name
    proj = project(work + "/helper/proj", "theorem t : True := trivial\n")
    write(proj + "/lakefile.toml", 'name = "p"\nbuildDir = "b"\ndefaultTargets = ["Main"]\n[[lean_lib]]\n'
                                   'name = "Main"\n')
    os.makedirs(proj + "/b/lib/lean")
    os.symlink("../../../../written", proj + "/b/lib/lean/FastverifyPremiseOff.olean")
    rc, rec = stage("build.sh", proj, ws, "--preset", "B3", "--unsafe", "sound-fast-path,premise-off")
    row("the stage does not copy its premise-off helper through a link that the project ships",
        rc == 2 and "is a symbolic link" in str(rec.get("detail")) and not os.path.lexists(work + "/helper/written"),
        (rec.get("detail"), os.path.lexists(work + "/helper/written")))

    # the options and helpers that differ
    no_verdict("--require-modules is refused in one line", "build.sh", "DECLINED", "not available on macOS",
               project(work + "/modules/proj", "theorem t : True := trivial\n"), ws, "--require-modules", "Main")
    two = project(work + "/targets/proj", "theorem t : True := trivial\n")   # its second library does not build
    write(two + "/lakefile.toml", 'name = "p"\ndefaultTargets = ["Main", "Other"]\n[[lean_lib]]\nname = "Main"\n'
                                  '[[lean_lib]]\nname = "Other"\n')
    write(two + "/Other.lean", "theorem broken : False := trivial\n")
    if "leanprover/lean4:v4.36.0" in json.load(open(FV + "/config/components.json"))["lean_toolchains"]:
        rc, rec = stage("official-build.sh", two, ws, "--targets", "«Main»")
        row("--targets builds the named module, spelled as Lean 4.36 spells it", rc == 0, rec.get("detail"))
    else:
        no_verdict("--targets without the pinned Lean 4.36 is no verdict", "official-build.sh", "ERROR",
                   "the pinned Lean 4.36 is not available", two, ws, "--targets", "«Main»")
    forms = ('nproc 2 2> /dev/null && exit 1; realpath -q -- / 2> /dev/null && exit 2\n'
             'mapfile -n 1 A 2> /dev/null && exit 3\n'
             'mapfile -t A < <(printf "a\\n\\nb"); [ "${#A[@]}${A[1]}${A[2]}" = 3b ] || exit 4\n'
             'mkdir "$1/moved" "$1/there" && mv -T "$1/moved" "$1/there" && [ ! -e "$1/moved" ] || exit 5\n'
             '[ ! -e "$1/there/moved" ]')
    row("the stand-ins for GNU commands: the forms in use, and no other", helpers(forms, work) == 0)
    reader = runpy.run_path(FV + "/build/mergeplan.py")["read_source"]
    os.symlink(two + "/Main.lean", two + "/Link.lean")
    reads = []
    for name in ("Main.lean", "Link.lean", "."):
        try:
            reads.append(reader(f"{two}/{name}"))
        except OSError:
            reads.append(None)
    row("the merge planner reads a source file, and neither a link nor a directory",
        reads == ["theorem t : True := trivial\n", None, None], reads)
    row("no process and no private directory of these tests is left", not left(work + "/"), left(work + "/"))


def main():
    work = start("build-macos")
    if work:
        cases(work)
    print(f"RESULT pass={counts['PASS']} fail={counts['FAIL']}")
    return 1 if counts["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
