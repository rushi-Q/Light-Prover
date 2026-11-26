#!/usr/bin/python3 -I
"""plancheck.py PLAN.jsonl EXTMODS_OUT  (fastverify build stage)

Per-run checks that make the planner's `importArts = {}` exactly equivalent to the importArts Lake would write
(see README "importArts"), and the list of dependency modules whose up-to-dateness the official Lake must confirm.

Lake gives a NON-module importer, for every transitively imported workspace module X, the artifacts of X in X's package
build dir (X.olean [+ .olean.server, .olean.private, .ir.sig, .ir if X is a module-system file]); without importArts,
lean finds X by LEAN_PATH (= Lake's ws.leanPath, the same package lib dirs) and opportunistically loads the same parts.
The two coincide when
  (a) no olean module path exists in more than one search root (LEAN_PATH roots + the toolchain's lib/lean, + the
      modules this build will create in the root package's lib dir) - so the first LEAN_PATH hit is X's own package;
  (b) next to a non-module olean there is no .ir.sig (lean would load it, Lake would not), i.e. every X.ir.sig has an
      X.olean.server (module-system outputs come as a set).
Module-system importers are declined by the planner. Exit 0 = ok (EXTMODS_OUT written, one `+Module` per line);
exit 2 = DECLINE (reason printed).
"""
import json, os, sys


def die(msg):
    print(f"DECLINE: {msg}")
    sys.exit(2)


def main():
    plan, extout = sys.argv[1], sys.argv[2]
    with open(plan) as f:
        hdr = json.loads(f.readline())
        mods = []
        for line in f:
            r = json.loads(line)
            if "end" in r:
                break
            mods.append(r)
    roots = [p for p in hdr["leanPath"].split(":") if p]
    sysroot_lib = os.path.join(hdr["sysroot"], "lib", "lean")
    pk = {p["leanLibDir"]: p for p in hdr["packages"]}
    rootlib = [p["leanLibDir"] for p in hdr["packages"] if p["isRoot"]]
    if len(rootlib) != 1:
        die("no unique root package")
    rootlib = rootlib[0]
    if set(roots) != set(pk):
        die("LEAN_PATH roots != package lib dirs")
    owner = {}
    nmaps = 0   # every .olean/.olean.server/.olean.private/.ir/.ir.sig is one mmap when imported
    for r in roots + [sysroot_lib]:
        if not os.path.isdir(r):
            continue
        if r == rootlib:
            # fresh build dir: only what the build will create counts
            continue
        for dp, dns, fns in os.walk(r):
            for fn in fns:
                full = os.path.join(dp, fn)
                rel = os.path.relpath(full, r)
                if fn.endswith((".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")):
                    nmaps += 1
                if fn.endswith(".olean"):
                    if rel in owner and owner[rel] != r:
                        die(f"olean {rel} exists in {owner[rel]} and {r}")
                    owner[rel] = r
                elif fn.endswith(".ir.sig"):
                    base = full[: -len(".ir.sig")]
                    if not os.path.exists(base + ".olean.server"):
                        die(f"{full}: .ir.sig next to a non-module olean")
    for m in mods:
        olean = m["outputs"][0]
        if not olean.startswith(rootlib + "/"):
            die(f"{m['name']}: output {olean} not in the root lib dir")
        rel = os.path.relpath(olean, rootlib)
        if rel in owner:
            die(f"module {m['name']} ({rel}) also exists in {owner[rel]}")
        owner[rel] = rootlib
    # host limit: a lean importing the whole closure maps every artifact part (vm.max_map_count 65,530
    # on some hosts makes RH-sized imports fail with exit 1, which would look like a REJECT) -> refuse up front
    # nmaps (all parts in all roots) is an upper bound for one lean process; the project's own oleans alone are a lower
    # bound for the module that imports all of them (RH Main imports ~185k) -> refuse when even that cannot fit; host
    # resource failures inside lean are classified as DECLINE by sched.py (never REJECT).
    own = sum(1 if not m.get("isModule") else 5 for m in mods)
    nmaps += sum(len(m["outputs"]) for m in mods)
    try:
        with open("/proc/sys/vm/max_map_count") as f:
            mmc = int(f.read().split()[0])
    except (OSError, ValueError, IndexError):
        die("cannot read /proc/sys/vm/max_map_count")
    if mmc < own + 65536:
        die(f"host limit: vm.max_map_count {mmc} < {own} project olean parts + 65536 (lean must map every imported "
            "part; the official build fails on this host too)")
    if os.path.isdir(rootlib) and any(True for _ in os.scandir(rootlib)):
        die(f"root lib dir {rootlib} is not empty before the build")
    if hdr["extImports"] and not any(o != rootlib for o in owner.values()):
        die("dependency modules are imported but no dependency olean is visible")
    for x in hdr["extImports"]:
        rel = x.replace(".", "/") + ".olean"
        if rel not in owner:
            die(f"dependency module {x}: no {rel} in any search root")
    with open(extout, "w") as f:
        for x in hdr["extImports"]:
            f.write(f"+{x}\n")
    print(f"ok: {len(mods)} modules, {len(owner)} oleans checked, {len(hdr['extImports'])} dependency modules, "
          f"max_map_count {mmc} (own parts {own}, all parts {nmaps})")


if __name__ == "__main__":
    main()
