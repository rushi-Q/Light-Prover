#!/bin/bash
# trace_cs.sh EXPORT CHALLENGE_EXPORT CFG THREADS : run the trusted check-sound.sh unchanged under bash -x with timestamps
# (PS4) to attribute its fixed cost; prints the slowest gaps.
X=$(mktemp -d /tmp/v01trace.XXXX)
export PS4='+ $(date +%s.%N) '
env -i CHECK_SOUND_CLEAN_ENV=1 PATH=/usr/bin:/bin LANG=C.UTF-8 PS4="$PS4" bash -x ${FVROOT:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}/check/sound/check-sound.sh "$1" "$2" "$3" --threads "$4" > $X/out 2> $X/trace
echo "rc=$?"; tail -2 $X/out | cut -c1-200
python3 - $X/trace <<'PY'
import sys, re
L = [l.rstrip("\n") for l in open(sys.argv[1], errors="replace")]
ev = []
for l in L:
    m = re.match(r"^(\++) (\d+\.\d+) (.*)$", l)
    if m: ev.append((float(m.group(2)), len(m.group(1)), m.group(3)[:150]))
t0 = ev[0][0]
gaps = sorted(((ev[i+1][0]-ev[i][0], ev[i][0]-t0, ev[i][2]) for i in range(len(ev)-1)), reverse=True)[:15]
print("total %.2f s, events %d" % (ev[-1][0]-t0, len(ev)))
for g, t, c in gaps: print("%6.2f s at +%6.2f  %s" % (g, t, c))
PY
rm -rf $X
