#!/usr/bin/env python3
"""tests/sound-auto/unit.py PKGROOT : unit rows of lib/autotune.py (header parser, project scan, decisions on synthetic
projects and mocked hosts). Prints PASS/FAIL rows and RESULT; exit 0 iff all PASS. No Lean needed, < 5 s."""
import importlib.util, json, os, shutil, sys, tempfile

root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), "..", ".."))
spec = importlib.util.spec_from_file_location("autotune", os.path.join(root, "lib", "autotune.py"))
at = importlib.util.module_from_spec(spec); spec.loader.exec_module(at)
npass = nfail = 0


def row(name, ok, info=""):
    global npass, nfail
    print(("PASS " if ok else "FAIL ") + name + (f": {info}" if info else ""))
    npass += ok; nfail += (not ok)


# ---- header parser
cases = [
    ("plain", "import Mathlib\nimport Foo.Bar\n\ntheorem x : True := trivial", (False, False, ["Mathlib", "Foo.Bar"])),
    ("comments", "/- a /- nested -/ comment -/\n-- line\nimport Mathlib -- trailing\n/-! doc -/\nimport A", (False, False, ["Mathlib", "A"])),
    ("module", "module\n\npublic import Mathlib.Order\nimport all Foo\nmeta import Bar\n\n@[expose] public section", (True, False, ["Mathlib.Order", "Foo", "Bar"])),
    ("prelude", "prelude\nimport Init.Core\ndef x := 1", (False, True, ["Init.Core"])),
    ("escaped", "import «My Lib».«a b».C\nimport D", (False, False, ["«My Lib».«a b».C", "D"])),
    ("no-imports", "theorem t : 1 = 1 := rfl", (False, False, [])),
    ("module-word-later", "import A\nmodule\n", (False, False, ["A"])),
]
for n, src, want in cases:
    got = at.parse_header(src)
    row(f"header {n}", got == want, f"{got}")


# ---- synthetic projects
def mkproj(d, files, lakefile=None, toolchain="leanprover/lean4:v4.33.1"):
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "lean-toolchain"), "w") as f:
        f.write(toolchain + "\n")
    if lakefile is not None:
        with open(os.path.join(d, "lakefile.toml"), "w") as f:
            f.write(lakefile)
    for rel, txt in files.items():
        p = os.path.join(d, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w") as f:
            f.write(txt)


def host(cpus=64, mem_gb=256, glibc=(2, 39), zy=True, shm_gb=128):
    trees = {t: {"present": True, "starts": (glibc >= (2, 38)) or t.endswith("nopgo")} for t in at.T1_ORDER}
    if not zy:
        trees[at.ZYGOTE_TREE] = {"present": False}
    return {"cpus": cpus, "mem_budget": mem_gb << 30, "shm_free": shm_gb << 30, "glibc": "%d.%d" % glibc, "t1_trees": trees}


tmp = tempfile.mkdtemp(prefix="sound-auto-unit.")
try:
    LF = 'name = "p"\ndefaultTargets = ["P"]\n\n[[lean_lib]]\nname = "P"\n'
    # one module -> B0
    mkproj(f"{tmp}/one", {"P.lean": "import Mathlib\ntheorem t : 1 + 1 = 2 := by norm_num\n"}, LF)
    f = at.scan_project(f"{tmp}/one"); d = at.decide(f, host(), pkgroot=root)
    row("one-module -> B0", d["build"] == "B0" and f["modules"] == 1, f"build={d['build']} modules={f['modules']}")
    # 20 tiny modules (< 64 KiB) -> B0; 20 modules with 100 KiB of source -> B3
    files = {f"T/M{i}.lean": "import Mathlib.Logic.Basic\ntheorem t : True := trivial\n" for i in range(20)}
    files["T.lean"] = "".join(f"import T.M{i}\n" for i in range(20))
    mkproj(f"{tmp}/tiny", files, 'name = "t"\ndefaultTargets = ["T"]\n[[lean_lib]]\nname = "T"\n')
    d = at.decide(at.scan_project(f"{tmp}/tiny"), host(), pkgroot=root)
    row("21 tiny modules -> B0", d["build"] == "B0", d["build"])
    files = {k: v + "-- " + "x" * 5000 + "\n" for k, v in files.items()}
    mkproj(f"{tmp}/mid", files, 'name = "t"\ndefaultTargets = ["T"]\n[[lean_lib]]\nname = "T"\n')
    d = at.decide(at.scan_project(f"{tmp}/mid"), host(), pkgroot=root)
    row("21 modules with 100 KiB of source -> B3", d["build"] == "B3", d["build"])
    # a file symlink leaving the project is never read (prepare refuses it anyway)
    mkproj(f"{tmp}/lnk", {"P.lean": "import P.A\n", "P/B.lean": ""}, LF)
    os.symlink("/etc/hostname", f"{tmp}/lnk/P/A.lean")
    f = at.scan_project(f"{tmp}/lnk")
    row("symlink leaving the project is not read", f["modules"] == 1, f"modules={f['modules']}")
    # one module but kernel-heavy -> B3 with skip-kernel-tc
    mkproj(f"{tmp}/kh", {"P.lean": "theorem t : (List.range 300).length = 300 := by decide +kernel\n"}, LF)
    f = at.scan_project(f"{tmp}/kh"); d = at.decide(f, host(), pkgroot=root)
    row("kernel-heavy one-module -> B3 + skip-kernel-tc", d["build"] == "B3" and "skip-kernel-tc" in d["unsafe"], d["build"])
    # default-target closure: 1 root importing 6 of 8 files, 2 stray files not built
    files = {"P.lean": "import P.A\nimport P.B\n", "P/A.lean": "import P.C\n", "P/B.lean": "import P.C\nimport Mathlib.Order\n",
             "P/C.lean": "import P.D\n", "P/D.lean": "import P.E\n", "P/E.lean": "import Mathlib\n",
             "P/Stray.lean": "import Mathlib\n", "P/Stray2.lean": "import P.Stray\n"}
    mkproj(f"{tmp}/clo", files, LF)
    f = at.scan_project(f"{tmp}/clo")
    row("default-target import closure", f["modules"] == 6 and f["import_depth"] == 5, f"modules={f['modules']} depth={f['import_depth']}")
    # globs: X.+ excludes X, X.* includes it
    mkproj(f"{tmp}/glob", {"Q.lean": "", "Q/A.lean": "import Q\n", "Q/B/C.lean": ""},
           'name = "q"\ndefaultTargets = ["Q"]\n[[lean_lib]]\nname = "Q"\nglobs = ["Q.+"]\n')
    f = at.scan_project(f"{tmp}/glob")
    row("glob Q.+ (closure adds Q via import)", f["modules"] == 3, f"modules={f['modules']}")
    # package-level srcDir + lib globs (RH layout)
    mkproj(f"{tmp}/src", {"src/R/A.lean": "import Mathlib\n", "src/R/B.lean": "import R.A\n", "src/R/C.lean": "import R.B\n"},
           'name = "r"\nsrcDir = "src"\ndefaultTargets = ["R"]\n\n[[lean_lib]]\nname = "R"\nglobs = ["R.+"]\n')
    f = at.scan_project(f"{tmp}/src")
    row("package srcDir + globs", f["modules"] == 3 and f["import_depth"] == 3, f"modules={f['modules']} depth={f['import_depth']}")
    # RH-like: 300 modules all `import Mathlib` first, zygote-capable host -> zygote + merge off (n < 2000)
    files = {f"Z/M{i}.lean": "import Mathlib\n" for i in range(300)}
    files["Z.lean"] = "".join(f"import Z.M{i}\n" for i in range(300))
    mkproj(f"{tmp}/rhl", files, 'name = "z"\ndefaultTargets = ["Z"]\n[[lean_lib]]\nname = "Z"\n')
    f = at.scan_project(f"{tmp}/rhl")
    d = at.decide(f, host(), pkgroot=root)
    row("RH-like + zygote host -> zygote, zygote-prefix", "zygote" in d["unsafe"] and "zygote-prefix" in d["unsafe"], ",".join(d["unsafe"]))
    d2 = at.decide(f, host(glibc=(2, 35)), pkgroot=root)
    row("RH-like on glibc 2.35 -> no zygote, only the nopgo tree",
        "zygote" not in d2["unsafe"] and "toolchain-T1=lean4-7586a50cec-nopgo" in d2["unsafe"], ",".join(d2["unsafe"])[:120])
    # compressed-like: import reduction leaves `import Mathlib` in ONE module, the others reach it through
    # their first import (prefix-zygote hits); C.X reaches all of Mathlib only through its 2nd import (closure, prefix miss)
    files = {"C/Base.lean": "import Mathlib\n", "C/X.lean": "import Mathlib.Order.Basic\nimport C.Base\n"}
    files.update({f"C/M{i}.lean": (f"import C.M{i - 1}\n" if i % 2 else "import C.Base\n") for i in range(300)})
    files["C.lean"] = "".join(f"import C.M{i}\n" for i in range(300)) + "import C.X\n"
    mkproj(f"{tmp}/cmp", files, 'name = "c"\ndefaultTargets = ["C"]\n[[lean_lib]]\nname = "C"\n')
    f = at.scan_project(f"{tmp}/cmp"); d = at.decide(f, host(), pkgroot=root)
    row("compressed-like (Mathlib through the first import) -> zygote, zygote-prefix",
        (f["first_import_Mathlib"], f["prefix_Mathlib"], f["closure_Mathlib"]) == (1, 302, 303)
        and "zygote" in d["unsafe"] and "zygote-prefix" in d["unsafe"],
        f"first={f['first_import_Mathlib']} prefix={f['prefix_Mathlib']} closure={f['closure_Mathlib']} {','.join(d['unsafe'])[:80]}")
    # ... but a hub reached only after a selective first import is a prefix MISS for every module: no zygote
    files = {"Y/H.lean": "import Mathlib\n"}
    files.update({f"Y/M{i}.lean": "import Mathlib.Order.Basic\nimport Y.H\n" for i in range(300)})
    files["Y.lean"] = "".join(f"import Y.M{i}\n" for i in range(300))
    mkproj(f"{tmp}/hub", files, 'name = "y"\ndefaultTargets = ["Y"]\n[[lean_lib]]\nname = "Y"\n')
    f = at.scan_project(f"{tmp}/hub"); d = at.decide(f, host(), pkgroot=root)
    row("hub after a selective first import (closure only) -> no zygote",
        f["prefix_Mathlib"] == 1 and f["closure_Mathlib"] == 302 and "zygote" not in d["unsafe"],
        f"prefix={f['prefix_Mathlib']} closure={f['closure_Mathlib']} {d['dropped'].get('zygote', '')[:70]}")
    # real-project-like: selective imports -> no zygote; module-system -> importarts-empty; translate -> per-module gate
    files = {f"W/M{i}.lean": ("module\npublic import Mathlib.Order.Basic\n" if i % 2 else "import Mathlib.Algebra.Group.Defs\n")
             + ("@[to_additive] theorem foo : True := trivial\n" if i == 3 else "") for i in range(40)}
    files["W.lean"] = "".join(f"import W.M{i}\n" for i in range(40))
    mkproj(f"{tmp}/real", files, 'name = "w"\ndefaultTargets = ["W"]\n[[lean_lib]]\nname = "W"\n')
    f = at.scan_project(f"{tmp}/real"); d = at.decide(f, host(), pkgroot=root)
    row("real-like: no zygote", "zygote" not in d["unsafe"], f"first_import_Mathlib={f['first_import_Mathlib']}")
    row("real-like: module-system -> importarts-empty", "sound-fast-path=importarts-empty" in d["unsafe"], f"module_system={f['module_system']}")
    gate = "skip-kernel-tc=except-translate" in open(os.path.join(root, "build", "build.sh")).read()
    want = "skip-kernel-tc=except-translate" if gate else None
    got = [u for u in d["unsafe"] if u.startswith("skip-kernel-tc")]
    row("real-like: translate module -> per-module skip-kernel-tc gate" if gate else "real-like: translate -> no skip-kernel-tc",
        got == ([want] if want else []) and f["translate_modules"] == 1, f"{got}")
    row("real-like: no RH hints/overlap/merge/native", not any(u in d["unsafe"] for u in ("cost-hints", "check-tail", "merge", "native-pkg"))
        and d["options"]["overlap_targets"] == "none", ",".join(d["unsafe"])[:150])
    # busy shared node: threads leave the busy cores alone (never below min(cpus, 8)); explicit threads win
    hb = dict(host(cpus=200), load1=180.0, online_cpus=200)
    d = at.decide(at.scan_project(f"{tmp}/real"), hb, pkgroot=root)
    row("busy node (load 180/200) -> 20 threads", d["threads"] == 20, f"threads={d['threads']}")
    hb["load1"] = 199.0
    d = at.decide(at.scan_project(f"{tmp}/real"), hb, pkgroot=root)
    row("fully busy node -> at least 8 threads", d["threads"] == 8, f"threads={d['threads']}")
    d = at.decide(at.scan_project(f"{tmp}/real"), hb, threads_given=64, pkgroot=root)
    row("busy node + explicit --threads 64 -> 64", d["threads"] == 64, f"threads={d['threads']}")
    # long chain of cheap plain modules -> merge; the same chain as module-system files -> no merge
    files = {f"K/M{i}.lean": (f"import K.M{i-1}\n" if i else "import Mathlib.Logic.Basic\n") + f"theorem t{i} : True := trivial\n"
             for i in range(40)}
    mkproj(f"{tmp}/chain", files, 'name = "k"\ndefaultTargets = ["K"]\n[[lean_lib]]\nname = "K"\nglobs = ["K.+"]\n')
    fc = at.scan_project(f"{tmp}/chain"); d = at.decide(fc, host(), pkgroot=root)
    row("chain of 40 cheap plain modules -> merge", "merge" in d["unsafe"] and fc["import_depth"] == 40, f"depth={fc['import_depth']} single={fc['single_importer_modules']}")
    files = {k: "module\npublic " + v for k, v in files.items()}
    mkproj(f"{tmp}/chainm", files, 'name = "k"\ndefaultTargets = ["K"]\n[[lean_lib]]\nname = "K"\nglobs = ["K.+"]\n')
    d = at.decide(at.scan_project(f"{tmp}/chainm"), host(), pkgroot=root)
    row("the same chain as module-system files -> no merge", "merge" not in d["unsafe"], "")
    # memory budget caps threads (no explicit --threads); explicit threads win
    d = at.decide(f, host(cpus=64, mem_gb=16), pkgroot=root)
    row("16 GB budget caps threads (selective imports: ~1 GB per lean)", d["threads"] == 12, f"threads={d['threads']}")
    d = at.decide(at.scan_project(f"{tmp}/rhl"), host(cpus=64, mem_gb=16), pkgroot=root)
    row("16 GB budget, whole-Mathlib importers: ~2 GB per lean, no zygote (< 96 GB)", d["threads"] == 6 and "zygote" not in d["unsafe"], f"threads={d['threads']} {d['dropped'].get('zygote','')[:80]}")
    d = at.decide(f, host(cpus=64, mem_gb=16), threads_given=64, pkgroot=root)
    row("explicit --threads wins over the memory cap", d["threads"] == 64, f"threads={d['threads']}")
    d8 = at.decide(f, host(cpus=8, mem_gb=8), pkgroot=root)
    row("export: low-memory exporter first below 16 GB, fallback otherwise",
        d8["options"].get("export_lowmem") == "prefer" and d["options"].get("export_lowmem") == "fallback", f"{d8['options'].get('export_lowmem')} / {d['options'].get('export_lowmem')}")
    # other toolchain / root lakefile.lean -> B0
    mkproj(f"{tmp}/v436", {"P.lean": "import Mathlib\n", "P/A.lean": "", "P/B.lean": "", "P/C.lean": "", "P/D.lean": "",
                           "P/E.lean": ""}, LF, toolchain="leanprover/lean4:v4.36.0")
    d = at.decide(at.scan_project(f"{tmp}/v436"), host(), pkgroot=root)
    row("toolchain v4.36.0 -> B0", d["build"] == "B0", d["reasons"].get("build", "")[:60])
    mkproj(f"{tmp}/lfl", {f"L/M{i}.lean": "import Mathlib\n" for i in range(10)})
    with open(f"{tmp}/lfl/lakefile.lean", "w") as fh:
        fh.write("import Lake\nopen Lake DSL\npackage l\n@[default_target] lean_lib L\n")
    f = at.scan_project(f"{tmp}/lfl"); d = at.decide(f, host(), pkgroot=root)
    row("root lakefile.lean -> B0", d["build"] == "B0" and f["lakefile"] == "lean", d["build"])
    # check threads by export size (host memory mocked: unlimited, then a 16 GB budget)
    real_mb = at.mem_budget
    at.mem_budget = lambda: None
    ct = at.check_threads
    row("check threads: 50 MB -> 32, 1.1 GB -> ~51, 61.6 GB -> budget", ct(50 << 20, 384) == 32 and 46 <= ct(int(1.1 * (1 << 30)), 384) <= 56
        and ct(int(61.6 * (1 << 30)), 384) == 384 and ct(1 << 30, 4) == 4, f"{ct(50 << 20, 384)} {ct(int(1.1 * (1 << 30)), 384)} {ct(int(61.6 * (1 << 30)), 384)}")
    at.mem_budget = lambda: 16 << 30
    row("check threads under a 16 GB budget: 1 GB export -> 48, 3 GB export -> memory-bound (~28)",
        ct(1 << 30, 64) == 48 and 20 <= ct(3 << 30, 64) <= 32, f"{ct(1 << 30, 64)} {ct(3 << 30, 64)}")
    # which trusted check fits (normal vs the low-memory sequential check): 16 GB budget
    cp = at.check_plan(1 << 30, 16, root)
    row("check plan: 1 GB export, 16 GB budget -> the normal check", not cp["lowmem"], cp.get("why", ""))
    cp = at.check_plan(4 << 30, 16, root)
    lm_ok = os.path.isfile(os.path.join(root, at.LOWMEM_SCRIPT)) and at._pins_present(os.path.join(root, "check", "lowmem", "pins.env"))
    row("check plan: 4 GB export, 16 GB budget -> low-memory check if installed", cp["lowmem"] == lm_ok, cp.get("why", ""))
    cp = at.check_plan(6 << 30, 16, root)
    row("check plan: 6 GB export (estimate above the budget too) -> still the low-memory check if installed", cp["lowmem"] == lm_ok, cp.get("why", ""))
    at.mem_budget = real_mb
    # candidate order of unofficial trees: measured preset order first, then other pinned manifests by class (the portable trees)
    fake = os.path.join(tmp, "fakepkg", "toolchains", "unofficial"); os.makedirs(fake)
    for nm in ["lean4-7586a50cec-nopgo-portable", "lean4-d5e35ef223-pgo-portable", "lean4-s01zy-3cf5641cbd-pgo-portable"] + at.T1_ORDER:
        open(os.path.join(fake, nm + ".json"), "w").write("{}")
    order = at.t1_candidates(os.path.join(tmp, "fakepkg"))
    row("T1 candidate order (zygote > pgo > nopgo; measured before portable within a class)",
        order == ["lean4-s01zy-3cf5641cbd-pgo", "lean4-s01zy-3cf5641cbd-pgo-portable", "lean4-d5e35ef223-pgo",
                  "lean4-d5e35ef223-pgo-portable", "lean4-7586a50cec-nopgo", "lean4-7586a50cec-nopgo-portable"], str(order))
    # ELF dependency check of the unofficial trees (libuv / OpenSSL 3 / GMP come from the host)
    nd = at.elf_needed("/bin/ls") or []
    row("ELF DT_NEEDED parser + host library lookup", "libc.so.6" in nd and at.host_has_lib("libc.so.6")
        and not at.host_has_lib("libd04-definitely-not-there.so.7"), f"{nd}")
    # failed-build confirmation mode + the orchestrator's exact-retry parser (synthetic sched.out)
    d = at.decide(at.scan_project(f"{tmp}/real"), host(), pkgroot=root)
    row("real-like: failures confirmed by the exact per-module retry", d["options"].get("confirm_failure") == "exact-retry", str(d["options"]))
    d = at.decide(at.scan_project(f"{tmp}/chain"), host(), pkgroot=root)
    row("merge chosen -> full B1 confirmation", d["options"].get("confirm_failure") == "full", str(d["options"]))
    files = {f"W/M{i}.lean": "import Mathlib.Order.Basic\n" for i in range(10)}
    files["W/Meta.lean"] = "import Lean\nopen Lean in\nelab \"mk\" : command => do Lean.addDecl (Declaration.axiomDecl default)\n"
    files["W.lean"] = "".join(f"import W.M{i}\n" for i in range(10)) + "import W.Meta\n"
    mkproj(f"{tmp}/meta", files, 'name = "w"\ndefaultTargets = ["W"]\n[[lean_lib]]\nname = "W"\n')
    fm = at.scan_project(f"{tmp}/meta"); d = at.decide(fm, host(), pkgroot=root)
    row("project metaprogram calling addDecl -> full B1 confirmation", fm["adddecl_modules"] == 1 and d["options"].get("confirm_failure") == "full", str(d["options"].get("confirm_failure")))
    fvspec = importlib.util.spec_from_file_location("fvorch", os.path.join(root, "lib", "fastverify.py"))
    fv = importlib.util.module_from_spec(fvspec); fvspec.loader.exec_module(fv)
    ef = getattr(fv, "exact_retry_failures", None)
    if ef:
        so = os.path.join(tmp, "sched.out")
        err = json.dumps({"severity": "error", "fileName": "/p/A.lean", "pos": {"line": 3, "column": 2}, "data": "linarith failed"})
        mod = lambda rc: json.dumps({"event": "module", "module": "P.A", "rc": rc, "error_msg": True, "stdout_head": err})
        open(so, "w").write(mod(1) + "\n" + json.dumps({"event": "retry-exact", "module": "P.A"}) + "\n" + mod(1) + "\nBUILD FAILED: ['P.A']\n")
        r1 = ef(so)
        open(so, "w").write(mod(1) + "\nBUILD FAILED: ['P.A']\n")
        r2 = ef(so)
        modb = json.dumps({"event": "module", "module": "P.B", "rc": 1, "error_msg": True, "stdout_head": err})
        open(so, "w").write(mod(1) + "\n" + json.dumps({"event": "retry-exact", "module": "P.A"}) + "\n" + mod(1) + "\n" + modb + "\nBUILD FAILED: ['P.A']\n")
        r3 = ef(so)   # P.B failed (final record) without an exact retry, although the (truncated) BUILD FAILED line omits it
        row("exact_retry_failures: confirmed / not retried / a failed module without records",
            bool(r1) and r1[0]["error"] == "A.lean:3:2: linarith failed" and r2 is None and r3 is None, f"{r1} {r2} {r3}")
        if getattr(fv, "RETRY_SUSPECT", None):   # kernel / translation errors in the exact retry -> full B1
            outs = []
            for data in ("(kernel) application type mismatch", "@[to_dual] failed to add declaration `List.minimum_concat`.\n  The translated value is not type correct."):
                e2 = json.dumps({"severity": "error", "fileName": "/p/A.lean", "pos": {"line": 88, "column": 0}, "data": data})
                m2 = json.dumps({"event": "module", "module": "P.A", "rc": 1, "error_msg": True, "stdout_head": e2})
                open(so, "w").write(m2 + "\n" + json.dumps({"event": "retry-exact", "module": "P.A"}) + "\n" + m2 + "\nBUILD FAILED: ['P.A']\n")
                outs.append(ef(so))
            row("exact_retry_failures: kernel / to_dual error in the exact retry -> None (full B1 decides)", outs == [None, None], str(outs))
    if getattr(fv, "tree_stamp", None):   # (sound-auto fixed cost): the tree stamp, the private cache dir, private records
        import stat as stm, time as tm
        tr = os.path.join(tmp, "tree"); os.makedirs(os.path.join(tr, "lib"))
        for n in ("a", "b"):
            open(os.path.join(tr, "lib", n), "w").write(n * 10)
        os.symlink("a", os.path.join(tr, "lib", "l"))
        st0 = fv.tree_stamp(tr); seen = {st0}; okst = True
        def chg(what, fn):
            global okst
            tm.sleep(0.01); fn(); s1 = fv.tree_stamp(tr)
            if s1 is None or s1 in seen:
                okst = False; print(f"FAIL-detail stamp unchanged after {what}")
            seen.add(s1)
        fa = os.path.join(tr, "lib", "a")
        chg("same-content rewrite", lambda: open(fa, "w").write("a" * 10))
        chg("chmod", lambda: os.chmod(fa, 0o600))
        chg("touch -d back", lambda: os.utime(fa, ns=(0, 0)))
        chg("rename over", lambda: (open(fa + ".n", "w").write("a" * 10), os.replace(fa + ".n", fa)))
        chg("hard link", lambda: os.link(fa, os.path.join(tr, "h")))
        chg("symlink retarget", lambda: (os.unlink(os.path.join(tr, "lib", "l")), os.symlink("b", os.path.join(tr, "lib", "l"))))
        chg("new file", lambda: open(os.path.join(tr, "lib", "c"), "w").write(""))
        chg("delete", lambda: os.unlink(os.path.join(tr, "lib", "c")))
        same = fv.tree_stamp(tr) == fv.tree_stamp(tr)
        os.symlink(tr, tr + ".link")
        row("tree_stamp: changes on rewrite/chmod/utime/rename/link/retarget/add/delete; stable; None for a symlinked root",
            okst and same and fv.tree_stamp(tr + ".link") is None and fv.tree_stamp(os.path.join(tmp, "nope")) is None, "")
        top = os.path.join(tmp, "ic"); d1 = fv.integrity_cache_dir(top)
        good = d1 is not None and stm.S_IMODE(os.lstat(top).st_mode) == 0o700 and stm.S_IMODE(os.lstat(d1).st_mode) == 0o700
        os.chmod(top, 0o755); d2 = fv.integrity_cache_dir(top); os.chmod(top, 0o700)
        os.chmod(d1, 0o750); d3 = fv.integrity_cache_dir(top); os.chmod(d1, 0o700)
        top2 = os.path.join(tmp, "ic2"); os.symlink(top, top2); d4 = fv.integrity_cache_dir(top2)
        row("integrity_cache_dir: 0700 private dirs; group/other access or a symlink -> None (full verification)",
            good and d2 is None and d3 is None and d4 is None, f"{d1} {d2} {d3} {d4}")
        rf = os.path.join(d1, "r.record"); open(rf, "w").write("k s\n"); os.symlink(rf, rf + ".l")
        row("_read_private: own regular file read; symlinked record refused",
            fv._read_private(rf) == "k s\n" and fv._read_private(rf + ".l") is None and fv._read_private(rf + ".x") is None, "")
    if getattr(at, "fast_build_release_ok", None):   # release-generic fast build (the 4.37 port): build.sh's validated Lake list
        fk = os.path.join(tmp, "relpkg"); os.makedirs(os.path.join(fk, "build")); os.makedirs(os.path.join(fk, "toolchains", "unofficial"))
        H1, H2 = "1" * 40, "2" * 40
        open(os.path.join(fk, "build", "build.sh"), "w").write(f'  VALIDATED_LAKE="{H1}"   # 4.33.1\n  SOUND_LAKE437="{H2}"  # 4.37\n'
                                                            '  skip-kernel-tc=except-translate)\n')
        for rel, h in (("v4.33.1", H1), ("v4.37.0-rc1", H2), ("v4.36.0", "3" * 40)):
            json.dump({"lean_version": f"Lean (version {rel}, x86_64, commit {h}, Release)"},
                      open(os.path.join(fk, "toolchains", f"leanprover--lean4---{rel}.json"), "w"))
        for t in at.T1_ORDER:
            json.dump({"base": "leanprover/lean4:v4.33.1"}, open(os.path.join(fk, "toolchains", "unofficial", t + ".json"), "w"))
        oks = [at.fast_build_release_ok("leanprover/lean4:" + r, fk) for r in ("v4.33.1", "v4.37.0-rc1", "v4.36.0", "v4.99.0")]
        files = {f"Q/M{i}.lean": "import Mathlib.Order.Basic\ntheorem t%d : True := trivial\n" % i for i in range(40)}
        files["Q.lean"] = "".join(f"import Q.M{i}\n" for i in range(40))
        mkproj(f"{tmp}/r437", files, 'name = "q"\ndefaultTargets = ["Q"]\n[[lean_lib]]\nname = "Q"\n', toolchain="leanprover/lean4:v4.37.0-rc1")
        f437 = at.scan_project(f"{tmp}/r437"); d437 = at.decide(f437, host(), pkgroot=fk)
        mkproj(f"{tmp}/r436", files, 'name = "q"\ndefaultTargets = ["Q"]\n[[lean_lib]]\nname = "Q"\n', toolchain="leanprover/lean4:v4.36.0")
        d436 = at.decide(at.scan_project(f"{tmp}/r436"), host(), pkgroot=fk)
        no_t1 = not any(u.startswith("toolchain-T1") for u in d437["unsafe"])
        row("release-generic: build.sh's validated Lake commits decide B3; T1 trees only of the project's release",
            oks == [True, True, False, False] and d437["build"] == "B3" and no_t1 and d436["build"] == "B0",
            f"{oks} 437={d437['build']} t1={not no_t1} 436={d436['build']}")
    if "closure-only" in open(os.path.join(root, "lib", "autotune.py")).read():   # closure-only when build.sh offers it
        fk2 = os.path.join(tmp, "clopkg"); os.makedirs(os.path.join(fk2, "build"))
        open(os.path.join(fk2, "build", "build.sh"), "w").write("closure-only=?*) CLOSURE=x ;;\n")
        mkproj(f"{tmp}/clo", {f"C/M{i}.lean": "import Mathlib.Order.Basic\n" for i in range(40)} | {"C.lean": "".join(f"import C.M{i}\n" for i in range(40))},
               'name = "c"\ndefaultTargets = ["C"]\n[[lean_lib]]\nname = "C"\n')
        fc = at.scan_project(f"{tmp}/clo")
        d1 = at.decide(fc, host(), pkgroot=fk2); d2 = at.decide(fc, host(), pkgroot=os.path.join(tmp, "nonexist"))
        row("closure-only: added when build.sh offers it, dropped otherwise", "closure-only" in d1["unsafe"]
            and "closure-only" not in d2["unsafe"] and "closure-only" in d2["dropped"], f"{d1['unsafe']} | {list(d2['dropped'])}")
    # host probe runs here
    h = at.host_info()
    row("host_info", h["cpus"] >= 1 and "t1_trees" in h, f"cpus={h['cpus']} glibc={h['glibc']}")
finally:
    shutil.rmtree(tmp, ignore_errors=True)
print(f"RESULT pass={npass} fail={nfail}")
sys.exit(0 if nfail == 0 else 1)
