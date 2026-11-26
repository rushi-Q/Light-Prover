#!/bin/bash
# mkws.sh NAME [ROOT] : trusted dependency workspace ROOT/ws/NAME for project NAME: lake-manifest.json = the (ported) project
# manifest; packages that the trusted workspace TRUSTED_WS (default: the RH challenge workspace with Mathlib 0df444a + deps)
# has at the same revision are symlinked (read-only use); every other package is cloned at its manifest revision into the
# workspace directory Lake uses (name unescaped) and the project's imports from it are built OFFLINE in bwrap with the
# official lake (tools/wsbuild.sh). Extra packages are trusted dependencies in this benchmark (like Mathlib).
set -eu
H=$(cd "$(dirname "$0")/.." && pwd); N=$1; ROOT=${2:-/scratch/$USER/bigprojects}
TW=${TRUSTED_WS:-$LIGHT_LEAN/verify/challenge}
P=$ROOT/projects/$N; W=$ROOT/ws/$N; rm -rf "$W"; mkdir -p "$W/.lake/packages"
cp "$P/lean-toolchain" "$W/"
python3 -I - "$P" "$W" "$TW" <<'PY'
import json, os, re, sys, subprocess
P, W, TW = sys.argv[1:]
m = json.load(open(P + "/lake-manifest.json")); m["name"] = "ws"
json.dump(m, open(W + "/lake-manifest.json", "w"), indent=1)
tw = {p["name"]: p for p in json.load(open(TW + "/lake-manifest.json"))["packages"]}
reqs = re.split(r'(?m)^(?=\[)', open(P + "/lakefile.toml").read()) if os.path.exists(P + "/lakefile.toml") else []
open(W + "/lakefile.toml", "w").write('name = "ws"\n\n' + "".join(b for b in reqs if b.startswith("[[require]]")))
for p in m["packages"]:
    d = re.sub(r'«([^»]*)»', r'\1', p["name"]); dst = os.path.join(W, ".lake/packages", d)
    t = tw.get(p["name"])
    if t and t["rev"] == p["rev"]:
        os.symlink(os.path.join(TW, ".lake/packages", d), dst)
    else:
        subprocess.run(["git", "clone", "-q", p["url"], dst], check=True)
        subprocess.run(["git", "-C", dst, "checkout", "-q", p["rev"]], check=True)
        print("cloned", p["name"], p["rev"][:10])
    if d != p["name"]:                 # keep a «name» alias for package versions that use the escaped name
        os.symlink(d, os.path.join(W, ".lake/packages", p["name"]))
PY
# imports of the project from non-Mathlib dependency packages -> build them offline (else: just load the workspace once)
MODS=$(grep -rhoE '^(public )?import [A-Za-z0-9_.«»]+' --include='*.lean' "$P" | sed -E 's/^(public )?import //' | sort -u \
  | while read -r m; do r=${m%%.*}; for d in "$W"/.lake/packages/*/; do [ -L "${d%/}" ] && continue; [ -e "$d$r.lean" ] || [ -d "$d$r" ] && { echo "+$m"; break; }; done; done | tr '\n' ' ')
echo "$MODS" > "$W/build-mods.txt"
TW="$TW" "$(dirname "$0")/wsbuild.sh" "$W" lake build ${MODS:---no-build +Mathlib} 2>&1 | tail -2
