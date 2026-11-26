#!/usr/bin/python3 -I
"""tools/addrelease.py --elan-home DIR [--exporter-home DIR] [--pin-new] RELEASE...   (additive, opt-in)

Make the package accept projects pinned to further OFFICIAL Lean releases (e.g. leanprover/lean4:v4.35.0 or just 4.35.0):
the build is the official sandboxed `lake build` of that release (B0; the fast builds decline other releases unless they
support them), the export is that release's OFFICIAL exporter (E0; the native exporter declines), the checks are unchanged
(in sound mode: CS = official 4.36 judge code + official 4.36 kernel + gruszka, which reads only the export and the
challenge export). Run it after tools/configure.py (which regenerates config/components.json from the template and drops
added releases).

Per release:
  1. toolchain: DIR/toolchains/leanprover--lean4---vX (an official release tarball as installed by elan) must verify against
     the pinned whole-tree manifest fastverify/toolchains/leanprover--lean4---vX.json (lib/toolchain.py verify). Without a
     manifest: refused, unless --pin-new (an explicit decision: writes the manifest from this install; record the tarball's
     sha256 in toolchains/RELEASES.md).
  2. official exporter: releases >= 4.35 bundle bin/leanexport (inside the verified tree). Older releases: lean4export at the
     tag of the release (patch/rc releases without their own tag: the X.Y.0 tag; rc's of a line use their own tag when it
     exists) built OFFLINE in bwrap by the release's own official lake from the lean4export clone in
     $LIGHT_LEAN/env/tools/lean4export (tools/build-lean4export.sh); the binary's sha256 is pinned in the config.
  3. gate: the release's official exporter must export the 4.36 comparator's kernel-primitive targets (+ Quot builtins)
     from the release's own Init (exit 0, every name present). Releases <= 4.25 fail here (no String.ofList: their kernel
     expands string literals to String.mk) and are refused: the 4.36 judge needs every kernel primitive in the challenge.
     If check/xversion/releases.json exists (the cross-version gate table), the release (version + githash) must be
     admitted there too.
  4. config/components.json gets the entry (prefix, version line from the sandboxed `lean --version`, sha256 of bin/lean,
     bin/lake, the exporter path + sha256), written atomically.
Exit 0 iff every requested release was added."""
import argparse, hashlib, json, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
LIGHT = os.path.dirname(ROOT)
PRIMS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
         "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
         "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam",
         "autoParam", "semiOutParam", "outParam"]
ID_RE = re.compile(r"^(leanprover/lean4:)?v?([0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?)$")


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 22), b""):
            h.update(b)
    return h.hexdigest()


def sandbox(tc, extra_ro=(), rw=(), env=None, chdir="/"):
    a = ["/usr/bin/bwrap", "--ro-bind", "/", "/", "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--dir",
         "/tmp/home", "--tmpfs", "/run", "--dev", "/dev", "--proc", "/proc", "--clearenv", "--ro-bind", tc, tc]
    for p in extra_ro:
        a += ["--ro-bind", p, p]
    for p in rw:
        a += ["--bind", p, p]
    e = {"PATH": f"{tc}/bin:/usr/bin:/bin", "HOME": "/tmp/home", "LANG": "C.UTF-8"}
    e.update(env or {})
    for k, v in e.items():
        a += ["--setenv", k, v]
    return a + ["--unshare-all", "--die-with-parent", "--new-session", "--chdir", chdir, "--"]


def ver_tuple(v):
    m = re.match(r"(\d+)\.(\d+)\.(\d+)", v)
    return tuple(int(x) for x in m.groups())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elan-home", required=True)
    ap.add_argument("--exporter-home", help="where lean4export builds go (default: <elan-home>/lean4export)")
    ap.add_argument("--pin-new", action="store_true")
    ap.add_argument("releases", nargs="+")
    a = ap.parse_args()
    elan = os.path.realpath(a.elan_home)
    exph = os.path.realpath(a.exporter_home or os.path.join(elan, "lean4export"))
    cfgp = os.path.join(ROOT, "config", "components.json")
    cfg = json.load(open(cfgp))
    if "${" in json.dumps(cfg):
        sys.exit("config/components.json still has ${...}: run tools/configure.py first")
    gate = None
    gp = os.path.join(ROOT, "check", "xversion", "releases.json")   # the cross-version gate table
    if os.path.isfile(gp):
        gate = json.load(open(gp))
    bad = 0
    for r in a.releases:
        m = ID_RE.match(r)
        if not m:
            print(f"REFUSED {r}: not an official release id"); bad += 1; continue
        v = m.group(2)
        tid = f"leanprover/lean4:v{v}"
        dn = tid.replace("/", "--").replace(":", "---")
        tc = os.path.join(elan, "toolchains", dn)
        man = os.path.join(ROOT, "toolchains", dn + ".json")
        if not os.path.isdir(tc):
            print(f"REFUSED {tid}: {tc} missing (install the official release, e.g. elan toolchain install {tid})"); bad += 1
            continue
        tv = [sys.executable, "-I", os.path.join(ROOT, "lib", "toolchain.py")]
        if not os.path.isfile(man):
            if not a.pin_new:
                print(f"REFUSED {tid}: no pinned manifest {man} (use --pin-new to pin this install deliberately)")
                bad += 1; continue
            rr = subprocess.run(tv + ["pin", tc, tid, "--out", man], capture_output=True, text=True)
            if rr.returncode != 0:
                print(f"REFUSED {tid}: pin failed: {rr.stderr.strip()[-300:]}"); bad += 1; continue
        rr = subprocess.run(tv + ["verify", tc, tid], capture_output=True, text=True)
        if rr.returncode != 0:
            print(f"REFUSED {tid}: the installed tree does not verify: {rr.stderr.strip()[-300:]}"); bad += 1; continue
        gh = subprocess.run(sandbox(tc) + [f"{tc}/bin/lean", "--githash"], capture_output=True, text=True,
                            env={}).stdout.strip()
        if gate is not None and (gate.get("releases", {}).get(v, {}).get("githash") != gh):
            print(f"REFUSED {tid}: not admitted by {gp} (release {v}, githash {gh[:12]}: "
                  f"{gate.get('not_admitted', {}).get(v, 'not in the verified-release table')})"); bad += 1; continue
        # official exporter
        if os.path.isfile(os.path.join(tc, "bin", "leanexport")):
            exp = os.path.join(tc, "bin", "leanexport")
            what = f"leanexport bundled with the official Lean {v} release"
        else:
            exp = os.path.join(exph, "v" + v, ".lake", "build", "bin", "lean4export")
            if not os.path.isfile(exp):
                # the lean4export git clone = the repository of the pinned 4.33.1 official exporter (env/tools/lean4export)
                src = None
                for t in cfg["lean_toolchains"].values():
                    pth = t.get("official_lean4export", {}).get("path", "")
                    if pth.endswith("/.lake/build/bin/lean4export") and os.path.isdir(
                            os.path.join(pth[:-len("/.lake/build/bin/lean4export")], ".git")):
                        src = pth[:-len("/.lake/build/bin/lean4export")]
                        break
                if src is None:
                    print(f"REFUSED {tid}: no lean4export git clone found (config's 4.33.1 exporter repository)"); bad += 1
                    continue
                rr = subprocess.run([os.path.join(ROOT, "tools", "build-lean4export.sh"), v, tc,
                                     os.path.join(exph, "v" + v), src], capture_output=True, text=True)
                if rr.returncode != 0 or not os.path.isfile(exp):
                    print(f"REFUSED {tid}: official lean4export could not be built: {(rr.stdout + rr.stderr)[-400:]}")
                    bad += 1; continue
            what = (open(exp + ".provenance").read().strip() if os.path.isfile(exp + ".provenance") else
                    f"official lean4export built for Lean {v}")
        # gate: the 4.36 primitive targets must export from the release's own Init
        with tempfile.TemporaryDirectory(dir=os.path.join(ROOT, "config")) as w:
            open(os.path.join(w, "P.lean"), "w").write("prelude\nimport Init\n")
            r1 = subprocess.run(sandbox(tc, rw=[w], chdir=w) + ["lean", "-o", "P.olean", "P.lean"], capture_output=True,
                                env={})
            with open(os.path.join(w, "p.ndjson"), "wb") as out:
                r2 = subprocess.run(sandbox(tc, extra_ro=[exp], rw=[w], chdir=w,
                                            env={"LEAN_PATH": f"{tc}/lib/lean:{w}", "LEAN_ABORT_ON_PANIC": "1"})
                                    + [exp, "P", "--"] + PRIMS, stdout=out, stderr=subprocess.PIPE, env={})
            names = set()
            if r2.returncode == 0:
                idx = {0: ""}
                for ln in open(os.path.join(w, "p.ndjson"), encoding="utf-8"):
                    o = json.loads(ln)
                    if "in" in o and "str" in o:
                        p = idx[o["str"]["pre"]]; idx[o["in"]] = (p + "." if p else "") + o["str"]["str"]
                    elif "in" in o and "num" in o:
                        p = idx[o["num"]["pre"]]; idx[o["in"]] = (p + "." if p else "") + str(o["num"]["i"])
                    elif "il" not in o and "ie" not in o and "meta" not in o:
                        (k, d), = o.items()
                        for x in (d.get("types", []) + d.get("ctors", []) + d.get("recs", [])) if k == "inductive" else [d]:
                            names.add(idx[x["name"]])
            missing = [p for p in PRIMS if p not in names]
            if r1.returncode != 0 or r2.returncode != 0 or missing:
                why = (r2.stderr.decode("utf-8", "replace").strip().splitlines() or [""])[0][:200]
                print(f"REFUSED {tid}: the 4.36 kernel-primitive targets do not export from its Init "
                      f"(exit {r2.returncode}; missing {missing[:5]}; {why})"); bad += 1; continue
        vl = subprocess.run(sandbox(tc) + [f"{tc}/bin/lean", "--version"], capture_output=True, text=True,
                            env={}).stdout.strip()
        cfg["lean_toolchains"][tid] = {
            "prefix": tc, "lean_version": vl,
            "sha256": {"bin/lean": sha(os.path.join(tc, "bin", "lean")), "bin/lake": sha(os.path.join(tc, "bin", "lake"))},
            "official_lean4export": {"path": exp, "version": what, "sha256": sha(exp)},
            "comment": "added by tools/addrelease.py: official release; build B0 (official lake build, "
                       "sandboxed), export E0 (official exporter of the release), checks unchanged",
            "added_by": "tools/addrelease.py"}
        print(f"ADDED {tid}: {vl}; exporter {exp}")
    tmp = cfgp + ".addrelease.tmp"
    with open(tmp, "w") as f:
        json.dump(cfg, f, indent=2)
    os.replace(tmp, cfgp)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
