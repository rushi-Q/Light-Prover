#!/bin/bash
# build/test/zygote.sh [WORK] : component test of the B3 items zygote, zygote-prefix, j1-saturated (sound preset).
# No Mathlib, ~1 min. The toy projects/zygote: Toy.A (import Lean; a simp lemma + an instance), Toy.B (uses them),
# Toy.C (prelude: NOT a continuation of the prefix), Toy.D (reaches Lean through Toy.A).
#   1. B1 reference build with the official toolchain.
#   2. B3 --unsafe zygote=Lean:1:4,zygote-prefix=Lean,j1-saturated with the official toolchain (no zygote support):
#      BUILT, the zygote items are DROPPED by build.sh's startup probe (no zygote process, no zyc, the
#      items absent from the stage's "unsafe" list), artifacts byte-identical to 1.
#   3. if a pinned zygote toolchain (toolchain-T1 lean4-s01zy-*) verifies and starts on this host (glibc >= 2.38, or the portable tree):
#      B3 + toolchain-T1=<it> without and with zygote=Lean:1:4,zygote-prefix=Lean: both BUILT, the zygote served the
#      children (4 children, exactly 1 prefix miss = Toy.C, re-run as the plain lean), .olean files byte-identical.
# Prints PASS/FAIL/SKIP per check and 'RESULT: PASS|FAIL'; exit 0 iff no FAIL.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); D=$(cd "$H/../.." && pwd)
W=${1:-/tmp/fv-zytest-$$}; rm -rf "$W"; mkdir -p "$W/no-packages"; W=$(readlink -f "$W")
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
fail=0; ok() { echo "PASS $*"; }; bad() { echo "FAIL $*"; fail=1; }
build() { # NAME ARGS... -> $W/NAME/{proj,log,b.json}
  local n=$1; shift; cp -a "$H/projects/zygote" "$W/$n"
  "$D/build/build.sh" "$W/$n" "$W/no-packages" "$TC" --log "$W/log-$n" --threads 4 "$@" > "$W/$n.json" 2>&1
  grep -q '"status": "BUILT"' "$W/$n.json"; }
oleans() { (cd "$W/$1/.lake/build/lib/lean" && find . -name '*.olean' | sort | xargs sha256sum); }
zyrec() { /usr/bin/python3 -I -c 'import json,sys
for l in open(sys.argv[1]):
    try: r=json.loads(l)
    except ValueError: continue
    if r.get("event")==sys.argv[2]: print(json.dumps({k:v for k,v in r.items() if k!="log_tail"}))' "$W/log-$1/sched.out" "$2"; }
# 1
build ref && ok "B1 reference built" || bad "B1 reference: $(tail -1 "$W/ref.json" | cut -c1-300)"
# 2
if build fb --preset B3 --unsafe zygote=Lean:1:4,zygote-prefix=Lean,j1-saturated; then
  ok "B3 zygote items with the official lean: BUILT"
  [ ! -e "$W/log-fb/zy/zyc" ] && ok "no zyc (zygote items dropped: the official lean has no zygote support)" || bad "zyc compiled although the lean has no zygote support"
  [ -z "$(zyrec fb zygote)" ] && ok "no zygote process started" || bad "a zygote was started for a lean without zygote support"
  grep -q 'zygote items dropped' "$W/fb.json" && ! grep -q '"zygote' "$W/fb.json" && ok "stage reports the drop; zygote items not in its unsafe list" || bad "drop not reported: $(grep -o '"unsafe": \[[^]]*\]' "$W/fb.json")"
  [ "$(oleans ref)" = "$(oleans fb)" ] && ok ".olean files identical to B1 (fallback = plain lean)" || bad ".olean files differ from B1"
else bad "B3 zygote items with the official lean: $(tail -1 "$W/fb.json" | cut -c1-300)"; fi
# 3
ZT=
for m in "$D"/toolchains/unofficial/lean4-s01zy-*.json; do
  [ -f "$m" ] || continue; n=$(basename "$m" .json)
  if /usr/bin/python3 -I "$D/lib/toolchain.py" verify-unofficial "/scratch/fastverify-next/tc/$n" "$n" > /dev/null 2>&1; then ZT=$n; fi
done
if [ -z "$ZT" ]; then echo "SKIP zygote toolchain not available on this host (not installed, or needs glibc >= 2.38)"
else
  build t1 --preset B3 --unsafe toolchain-T1=$ZT && ok "B3 $ZT without zygote: BUILT" || bad "B3 $ZT: $(tail -1 "$W/t1.json" | cut -c1-300)"
  if build zy --preset B3 --unsafe toolchain-T1=$ZT,zygote=Lean:1:4,zygote-prefix=Lean; then
    ok "B3 $ZT + zygote + zygote-prefix: BUILT"
    c=$(zyrec zy zygote-children); echo "  $c"
    echo "$c" | grep -q '"n": 4, ' && echo "$c" | grep -q '"misses": 1' && ok "zygote served 4 children, 1 prefix miss (Toy.C)" || bad "zygote children: $c"
    [ "$(oleans t1)" = "$(oleans zy)" ] && ok ".olean files identical with and without the zygote" || bad ".olean files differ with the zygote"
  else bad "B3 $ZT + zygote: $(tail -1 "$W/zy.json" | cut -c1-300)"; fi
fi
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"; exit $fail
