#!/bin/bash
# check.sh WORK : builds a tiny git package "my-dep", a trusted workspace materialized by the official `lake update`
# (offline, file:// URL, bwrap), and runs bin/fastverify --preset reference|sound on x/proj (requires my-dep, does not
# import it) in two workspace layouts (Lake's own; + a «my-dep» symlink). PASS iff ACCEPTED.
set -u
D=$(cd "$(dirname "$0")" && pwd); W=${1:?work}; rm -rf "$W"; mkdir -p "$W"
. "$D/../../lib/paths.sh"
FV=${FV_ROOT:-$(cd "$D/../../.." && pwd)}
G="git -c user.name=t -c user.email=t@t -c init.defaultBranch=main"
mkdir -p "$W/dep" && printf 'name = "my-dep"\n\n[[lean_lib]]\nname = "MyDep"\n' > "$W/dep/lakefile.toml" \
  && echo 'theorem myDepFact : True := trivial' > "$W/dep/MyDep.lean" && cp "$D/proj/lean-toolchain" "$W/dep/" \
  && (cd "$W/dep" && $G init -q && $G add -A && $G commit -qm dep) || { echo "FAIL escaped/setup git package"; exit 1; }
sb() { env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc --unshare-all \
  --die-with-parent --ro-bind "$FV_T33" "$FV_T33" --bind "$1" "$1" --ro-bind "$W/dep" "$W/dep" --chdir "$1" \
  --setenv PATH "$FV_T33/bin:/usr/bin:/bin" --setenv HOME /tmp/home -- "${@:2}"; }
mkdir -p "$W/ws" && sed "s#@DEP@#file://$W/dep#" "$D/proj/lakefile.toml" | grep -v '^\[\[lean_lib\]\]\|^name = "Solution"' \
  | sed 's/^name = "escproj"/name = "ws"/; s/^defaultTargets.*//' > "$W/ws/lakefile.toml" && cp "$D/proj/lean-toolchain" "$W/ws/"
sb "$W/ws" lake update > "$W/ws-update.log" 2>&1 || { echo "FAIL escaped/setup lake update ($(tail -1 "$W/ws-update.log"))"; exit 1; }
# the dependency source must be unreachable for the judged builds, as an https URL is without network
mv "$W/dep" "$W/dep.unreachable"
echo "INFO manifest name: $(grep -o '"name": *"[^"]*my-dep[^"]*"' "$W/ws/lake-manifest.json"), dirs: $(ls "$W/ws/.lake/packages")"
for layout in lake symlink; do
  cp -a "$D/proj" "$W/proj-$layout"; sed -i "s#@DEP@#file://$W/dep#" "$W/proj-$layout/lakefile.toml"
  python3 -I - "$W/ws/lake-manifest.json" "$W/proj-$layout/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1])); m["name"] = "escproj"; json.dump(m, open(sys.argv[2], "w"), indent=1)
PY
  if [ $layout = symlink ]; then ln -sfn my-dep "$W/ws/.lake/packages/«my-dep»"; fi
  for p in reference sound; do
    env -i HOME="$HOME" PATH=/usr/bin:/bin "$FV/bin/fastverify" "$W/proj-$layout" "$D/challenge" "$W/out-$layout-$p" \
        --preset $p --packages "$W/ws" --threads "${EVAL_THREADS:-8}" > "$W/$layout-$p.log" 2>&1; rc=$?
    v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/out-$layout-$p/result.json" 2>/dev/null)
    why=$(grep -m1 -o "manifest: .*\|planner exit.*\|could not resolve host.*\|Could not resolve host.*" -r "$W/$layout-$p.log" "$W/out-$layout-$p/log" 2>/dev/null | head -1 | cut -c1-120)
    if [ "$v" = ACCEPTED ]; then echo "PASS escaped/$layout/$p verdict=$v"; else echo "FAIL escaped/$layout/$p verdict=${v:-none} exit=$rc (expected ACCEPTED) $why"; fi
  done
done
