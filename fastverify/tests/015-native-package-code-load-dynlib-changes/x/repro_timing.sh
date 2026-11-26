#!/bin/bash
# Timing dependence of 015: the SAME Main.lean, but without the `import Delay` stand-in, so the fast pipeline launches Main
# before native.sh has written native.ready -> Main is elaborated INTERPRETED -> heartbeat timeout -> fast REJECTS.
# (With repro.sh, Main starts after native.ready -> native -> fast ACCEPTS.) Only the fast flow is run here.
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-repro-015t}
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
sed -i '/^import Delay/d' "$W/proj/src/Main.lean"; rm -f "$W/proj/src/Delay.lean"
if [ ! -s "$W/challenge/challenge.export" ]; then   # build the challenge export with the official tools (as officialflow.sh)
  T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
  ( cd "$W/challenge" && PATH=$T33/bin:/usr/bin:/bin lake build > /dev/null 2>&1 && \
    LEAN_PATH=$W/challenge/.lake/build/lib/lean:$T33/lib/lean $EXP Challenge -- $(cat export-targets.txt) > challenge.export )
fi
echo "=== FAST flow (no Delay: Main races native.sh)"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
echo "=== SUMMARY fast_rc=$frc  (0 = ACCEPTED)"
