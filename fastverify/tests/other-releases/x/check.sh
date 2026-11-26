#!/bin/bash
# other-releases/x/check.sh [WORK] : projects pinned to OTHER official Lean releases (tools/addrelease.py).
# For every release R in $G14_RELEASES (default: every release in config/components.json that tools/addrelease.py added,
# at most 3 of them) the core-only small-proof cases of bench/smallproofs (gen.py WORK R) run through --preset reference
# (B0 + E0 of R + the official 4.36 lake comparator) and --preset sound (B0 + E0 of R + CS, challenge export pinned):
#   in04 (accepted), ks20 (kernel-heavy decide, accepted), dm01 (definition-style, accepted),
#   xk01 (false `decide +kernel` claim: REJECTED), xe06 (proof that does not elaborate: REJECTED).
# PASS iff both verdicts equal the expected one and both exports are byte-identical (same official exporter of R); a
# positive case whose proof does not elaborate on R (corpus written for 4.33/4.36) passes iff BOTH flows reject it.
# A sound ACCEPT of an expected REJECTED case prints 'FAIL CRITICAL'. Also: a release whose Init lacks a 4.36 kernel
# primitive (<= 4.25, if its toolchain is installed in the elan home of a configured release) must be REFUSED by
# tools/addrelease.py. Prints PASS/FAIL lines and RESULT PASS|FAIL. Skips (RESULT PASS, 'SKIP') when no extra release is
# configured.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)     # package root
W=${1:-${SCRATCH:-${TMPDIR:-/tmp}}/$USER-other-releases}; rm -rf "$W"; mkdir -p "$W"
T=${EVAL_THREADS:-8}
REL=${G14_RELEASES:-$(python3 -I -c '
import json, sys
c = json.load(open(sys.argv[1]))
print(" ".join([k.split(":v")[1] for k, v in c["lean_toolchains"].items() if v.get("added_by") == "tools/addrelease.py"][:3]))' \
  "$H/config/components.json")}
if [ -z "$REL" ]; then echo "PASS other-releases SKIP: no extra release configured (tools/addrelease.py)"; echo "RESULT PASS"; exit 0; fi
bad=0
for r in $REL; do
  C=$W/v$r
  python3 -I "$H/bench/smallproofs/gen.py" "$C" "leanprover/lean4:v$r" > /dev/null || { echo "FAIL other-releases $r: gen.py"; bad=1; continue; }
  for c in in04 ks20 dm01 xk01 xe06; do
    exp=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]].get("expected","ACCEPTED"))' "$C/cases.json" "$c")
    FASTVERIFY=$H "$H/bench/smallproofs/run1.sh" "$C" "$c" reference "$C" "$T" src
    vr=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$C/runs/$c.reference/result.json" 2>/dev/null)
    if [ -s "$C/runs/$c.reference/challenge.export" ]; then
      "$H/bench/smallproofs/mkgiven.sh" "$C" "$C" "$c" > /dev/null 2>&1
      FASTVERIFY=$H "$H/bench/smallproofs/run1.sh" "$C" "$c" sound "$C" "$T" given
    else   # the challenge itself did not build/export: sound from sources (challenge built officially in the run)
      FASTVERIFY=$H "$H/bench/smallproofs/run1.sh" "$C" "$c" sound "$C" "$T" src
    fi
    vs=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict"))' "$C/runs/$c.sound/result.json" 2>/dev/null)
    se=$(python3 -I -c 'import json,sys
a=json.load(open(sys.argv[1])).get("export") or {}; b=json.load(open(sys.argv[2])).get("export") or {}
print("same" if a.get("sha256") and a.get("sha256")==b.get("sha256") else "n/a" if not a.get("sha256") and not b.get("sha256") else "DIFF")' \
      "$C/runs/$c.reference/result.json" "$C/runs/$c.sound/result.json" 2>/dev/null)
    if [ "$exp" = REJECTED ] && [ "$vs" = ACCEPTED ]; then echo "FAIL CRITICAL other-releases $r $c: sound ACCEPTED an expected-REJECTED case"; bad=1
    elif [ "$vr" = "$exp" ] && [ "$vs" = "$exp" ] && [ "$se" != DIFF ]; then echo "PASS other-releases $r $c: reference=$vr sound=$vs export=$se"
    elif [ "$exp" = ACCEPTED ] && [ "$vr" = REJECTED ] && [ "$vs" = REJECTED ]; then
      # the corpus was written for 4.33/4.36: on an older release a proof may not elaborate (renamed library lemma);
      # the official flow rejects it and so must the package (verdict equality is what this test checks)
      echo "PASS other-releases $r $c: reference=$vr sound=$vs (the proof does not elaborate on this release; verdicts equal)"
    else echo "FAIL other-releases $r $c: expected $exp, reference=$vr sound=$vs export=$se"; bad=1; fi
  done
done
# a release without the 4.36 kernel primitives must be refused by tools/addrelease.py (only if such a toolchain is installed)
EH=$(python3 -I -c '
import json, os, sys
c = json.load(open(sys.argv[1]))
for k, v in c["lean_toolchains"].items():
    if v.get("added_by") == "tools/addrelease.py":
        print(os.path.dirname(os.path.dirname(v["prefix"]))); break' "$H/config/components.json")
for old in 4.24.0 4.21.0 4.20.0-rc5; do
  if [ -n "$EH" ] && [ -x "$EH/toolchains/leanprover--lean4---v$old/bin/lean" ]; then
    cp -a "$H" "$W/pkgcopy" 2>/dev/null; rm -rf "$W/pkgcopy/tests/results"
    out=$(python3 -I "$W/pkgcopy/tools/addrelease.py" --elan-home "$EH" --exporter-home "$W/l4e" --pin-new "$old" 2>&1)
    if echo "$out" | grep -q "REFUSED leanprover/lean4:v$old"; then
      # refused either by the gate table (check/xversion/releases.json) or by the primitive-export check (no String.ofList)
      echo "PASS other-releases addrelease refuses v$old: $(echo "$out" | grep -o "REFUSED leanprover/lean4:v$old: [^(]*" | head -1)"
    else echo "FAIL other-releases addrelease v$old: $out"; bad=1; fi
    rm -rf "$W/pkgcopy"
    break
  fi
done
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
