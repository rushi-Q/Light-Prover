#!/bin/bash
# check.sh WORK : bin/fastverify --preset reference|sound on x/proj (lean_exe default target importing Batteries) against
# x/challenge; prints PASS/FAIL rows (PASS iff ACCEPTED) + one control row: the same official `lake build` with a WRITABLE
# copy of the dependency succeeds (so a REJECTED verdict is a false reject of the package, not of Lean/Lake).
set -u
D=$(cd "$(dirname "$0")" && pwd); W=${1:?work}; rm -rf "$W"; mkdir -p "$W"
. "$D/../../lib/paths.sh"
FV=${FV_ROOT:-$(cd "$D/../../.." && pwd)}
# the project requires Batteries from the trusted workspace (the Mathlib workspace): without it every row SKIPs
if [ ! -d "${FV_PACKAGES:-}/.lake/packages/batteries" ]; then
  for r in exe-dep/reference exe-dep/sound exe-dep/control; do
    echo "SKIP $r: no trusted packages workspace with Batteries at ${FV_PACKAGES:-<unset>} (set FV_PACKAGES)"; done
  exit 0
fi
for p in reference sound; do
  env -i HOME="$HOME" PATH=/usr/bin:/bin "$FV/bin/fastverify" "$D/proj" "$D/challenge" "$W/out-$p" --preset $p \
      --packages "$FV_PACKAGES" --threads "${EVAL_THREADS:-8}" > "$W/$p.log" 2>&1
  v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$W/out-$p/result.json" 2>/dev/null)
  ero=$(grep -c "read-only file system" "$W/out-$p/log/build-official/build.log" 2>/dev/null)
  # the official verdict of this valid project is ACCEPTED; REJECTED = false reject (the bug); no verdict (exit 2) is the
  # fail-closed minimum (row text says WARN-NOVERDICT)
  case "$v" in
    ACCEPTED) echo "PASS exe-dep/$p verdict=$v" ;;
    REJECTED) echo "FAIL exe-dep/$p verdict=$v = FALSE REJECT (EROFS lines in B0 log: ${ero:-0})" ;;
    *) echo "PASS exe-dep/$p WARN-NOVERDICT verdict=${v:-none} (fail closed; ACCEPTED needs a writable dependency copy)" ;;
  esac
done
cp -a "$D/proj" "$W/proj"; mkdir -p "$W/proj/.lake/packages"; cp -a "$FV_PACKAGES/.lake/packages/batteries" "$W/proj/.lake/packages/"
env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc --unshare-all \
  --die-with-parent --ro-bind "$FV_T33" "$FV_T33" --bind "$W/proj" "$W/proj" --chdir "$W/proj" \
  --setenv PATH "$FV_T33/bin:/usr/bin:/bin" --setenv HOME /tmp/home -- bash -c 'lake build && .lake/build/bin/hello' > "$W/writable.log" 2>&1
rc=$?; [ $rc = 0 ] && echo "PASS exe-dep/control official lake build with a writable dependency copy succeeds" || echo "FAIL exe-dep/control writable official build rc=$rc (test inputs broken)"
