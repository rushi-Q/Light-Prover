#!/bin/bash
# dhe_check.sh MODULE EDITS_TSV WORKDIR -- apply the DHE edits of MODULE to a copy of its source, elaborate original (A)
# and edited (B) against a full RH build tree (RHP, required, read-only) inside bwrap (no network, home hidden), compare
# the oleans with DeadLetCheck. Prints one RESULT line. (bwrap/setup as ../normalize/modcheck.sh)
# env: RHP, RHSRC (RH sources, default $RH_PROJECT/src or $LIGHT_LEAN/alpoge-rh/lean/src), TC, DLC.
set -u
M=$1; ED=$2; W=$3
TC=${TC:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1}
P=${RHP:?full RH build tree with its .olean files, read-only (required)}
SRC=${RHSRC:-${RH_PROJECT:-$LIGHT_LEAN/alpoge-rh/lean}/src}
DLC=${DLC:-$(cd "$(dirname "$0")" && pwd)/DeadLetCheck.lean}
rel=${M//.//}
rm -rf "$W"; mkdir -p "$W/a" "$W/b"
cp "$SRC/$rel.lean" "$W/a/M.lean"; cp "$DLC" "$W/DeadLetCheck.lean"
nl=$(python3 -I - "$M" "$ED" "$W/a/M.lean" "$W/b/M.lean" <<'PY'
import sys
m, ed, a, b = sys.argv[1:5]
def unesc(s):
    out = []; i = 0
    while i < len(s):
        if s[i] == '\\' and i + 1 < len(s):
            out.append('\n' if s[i + 1] == 'n' else s[i + 1]); i += 2
        else:
            out.append(s[i]); i += 1
    return ''.join(out)
L = open(a, encoding='utf-8').read().split('\n')
es = []
for line in open(ed, encoding='utf-8'):
    f = line.rstrip('\n').split('\t', 5)
    if f[0] == m and f[3] in ('delete', 'replace'):
        es.append((int(f[1]), int(f[2]), f[3], unesc(f[5]) if len(f) > 5 else ''))
new = list(L)
for s0, e0, act, txt in sorted(es, key=lambda t: (-t[0], -t[1])):
    new[s0 - 1:e0] = [] if act == 'delete' else txt.split('\n')
open(b, 'w', encoding='utf-8').write('\n'.join(new))
print(len(L) - len(new))
PY
)
LP=""
for pk in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible mathlib; do
  [ -d "$P/.lake/packages/$pk/.lake/build/lib/lean" ] && LP="$LP:$P/.lake/packages/$pk/.lake/build/lib/lean"
done
LP="${LP#:}:$P/.lake/build/lib/lean"
extra=""
case "$M" in GroundTheory.LocalFields.*|GroundTheory.GlobalFields.*) extra=',"synthInstance.maxHeartbeats":400000';; esac
printf '{"plugins":[],"package":"tree","options":{"relaxedAutoImplicit":false,"pp.unicode.fun":true,"maxSynthPendingDepth":3,"maxHeartbeats":4000000,"autoImplicit":false%s},"name":"%s","isModule":false,"importArts":{},"dynlibs":[]}\n' "$extra" "$M" > "$W/setup.json"
sbx() { env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home \
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --bind "$W" "$W" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --setenv LEAN_PATH "$LP" \
  --unshare-all --die-with-parent --new-session --chdir "$W" -- "$@"; }
for v in a b; do
  t0=$(date +%s.%N)
  sbx "$TC/bin/lean" --tstack=400000 "$W/$v/M.lean" -o "$W/$v/M.olean" --setup "$W/setup.json" > "$W/$v/stdout" 2> "$W/$v/stderr"
  echo $? > "$W/$v/rc"; t1=$(date +%s.%N); echo "$t1 - $t0" | bc > "$W/$v/secs"
done
ra=$(cat $W/a/rc); rb=$(cat $W/b/rc)
v=NA
if [ "$ra" = 0 ] && [ "$rb" = 0 ]; then
  sbx env LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$W/DeadLetCheck.lean" "$W/a/M.olean" "$W/b/M.olean" > "$W/dlc.txt" 2>&1
  v=$(tail -1 "$W/dlc.txt" | tr ' ' ',')
elif [ "$ra" = 0 ]; then
  v=B-FAILED:$(grep -m1 -o "error: .*" "$W/b/stdout" "$W/b/stderr" 2>/dev/null | head -1 | cut -c1-120 | tr ' \t' '__')
fi
echo "RESULT $M lines=$nl rcA=$ra rcB=$rb secsA=$(cat $W/a/secs) secsB=$(cat $W/b/secs) $v"
