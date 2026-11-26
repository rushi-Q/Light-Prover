#!/bin/bash
# mkws.sh NAME [ROOT] : trusted dependency workspace ROOT/ws/NAME for project NAME (after fetch.sh). lake-manifest.json = the
# project's manifest; packages that the trusted workspace TRUSTED_WS (default: ROOT/../local/ws, a node-local copy of the RH
# challenge workspace with Mathlib 0df444a + deps) has at the same revision are symlinked (read-only use); every other
# package is cloned at its manifest revision (public git, no code run) into the directory Lake uses, and the project's
# imports from those packages are built OFFLINE in bwrap with the official lake (bigprojects/tools/wsbuild.sh); the
# workspace lakefile requires every manifest package by its manifest url/rev (independent of a lakefile.lean project).
set -eu
H=$(cd "$(dirname "$0")/.." && pwd); N=$1; ROOT=${2:-/scratch/$USER/codeprojects}
TW=${TRUSTED_WS:-$(dirname "$ROOT")/local/ws}
P=$ROOT/projects/$N; W=$ROOT/ws/$N; rm -rf "$W"; mkdir -p "$W/.lake/packages"
cp "$P/lean-toolchain" "$W/"
python3 -I - "$P" "$W" "$TW" <<'PY'
import json, os, re, sys, subprocess
P, W, TW = sys.argv[1:]
m = json.load(open(P + "/lake-manifest.json")); m["name"] = "ws"
json.dump(m, open(W + "/lake-manifest.json", "w"), indent=1)
tw = {p["name"]: p for p in json.load(open(TW + "/lake-manifest.json"))["packages"]}
req = ['name = "ws"\n']
for p in m["packages"]:
    if not p.get("inherited"):
        req.append('\n[[require]]\nname = %s\ngit = %s\nrev = %s\n' % (json.dumps(p["name"]), json.dumps(p["url"]), json.dumps(p["rev"])))
open(W + "/lakefile.toml", "w").write("".join(req))
for p in m["packages"]:
    d = re.sub(r'«([^»]*)»', r'\1', p["name"]); dst = os.path.join(W, ".lake/packages", d)
    t = tw.get(p["name"])
    if t and t["rev"] == p["rev"]:
        os.symlink(os.path.join(TW, ".lake/packages", d), dst)
    else:
        mirror = os.path.join(TW, ".lake/packages", d)
        src = mirror if os.path.isdir(os.path.join(mirror, ".git")) else p["url"]   # local objects first (GitHub throttles)
        subprocess.run(["git", "clone", "-q", src, dst], check=True)
        if subprocess.run(["git", "-C", dst, "checkout", "-q", p["rev"]]).returncode != 0:
            subprocess.run(["git", "-C", dst, "fetch", "-q", p["url"]], check=True)
            subprocess.run(["git", "-C", dst, "checkout", "-q", p["rev"]], check=True)
        subprocess.run(["git", "-C", dst, "remote", "set-url", "origin", p["url"]], check=True)
        print("cloned", p["name"], p["rev"][:10])
    if d != p["name"]:
        os.symlink(d, os.path.join(W, ".lake/packages", p["name"]))
PY
MODS=$(grep -rhoE '^(public )?(meta )?import (all )?[A-Za-z0-9_.«»]+' --include='*.lean' "$P" | sed -E 's/^(public )?(meta )?import (all )?//' | sort -u \
  | while read -r m; do r=${m%%.*}; for d in "$W"/.lake/packages/*/; do [ -L "${d%/}" ] && continue; [ -e "$d$r.lean" ] || [ -d "$d$r" ] && { echo "+$m"; break; }; done; done | tr '\n' ' ')
echo "$MODS" > "$W/build-mods.txt"
TC=$(dirname "$ROOT")/local/elan/toolchains/leanprover--lean4---$(sed 's/.*://' "$P/lean-toolchain")
# load the workspace once OFFLINE in bwrap: Lake elaborates the cloned packages' lakefile.lean configs and caches them in
# their .lake dirs (the package's builds bind the workspace read-only: a missing config cache = EROFS = no verdict)
TC="$TC" TW="$TW" "$H/../bigprojects/tools/wsbuild.sh" "$W" lake env true 2>&1 | tail -3
if [ -n "$MODS" ]; then
  TC="$TC" TW="$TW" "$H/../bigprojects/tools/wsbuild.sh" "$W" lake build $MODS 2>&1 | tail -3
fi
echo "workspace $W ready ($(ls "$W/.lake/packages" | wc -l) packages; built: ${MODS:-none})"
