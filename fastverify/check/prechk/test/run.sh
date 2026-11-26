#!/bin/bash
# prechk component regression test. Runs check/prechk/prechk.sh on the regression exports (read-only, from
# the tests/NNN-*/x snapshots), on generated exports (deep level chain 044, deep definition chain 051) and on mutations of an honest
# export (non-canonical JSON, dangling references, ...). Prints one PASS/FAIL line per case and 'RESULT: PASS|FAIL'.
#   test/run.sh [--quick] [--bench]     --quick: skip the 16.7M-line level chain; --bench: also rh-mid + Mathlib (node-local)
set -u
H=$(cd "$(dirname "$0")/.." && pwd)
P=$H/prechk.sh
X=${XFIND:-$(cd "$H/../.." && pwd)/tests}   # the package's per-case test dirs (inputs under NNN-*/x)
QUICK=0; BENCH=0
for a in "$@"; do case "$a" in --quick) QUICK=1;; --bench) BENCH=1;; esac; done
SCR=/tmp; [ -d /scratch ] && [ -w /scratch ] && SCR=/scratch
T=$(mktemp -d "$SCR/prechk-test.XXXXXX"); trap 'rm -rf "$T"' EXIT
NT=${THREADS:-16}
fails=0; n=0
f1() { ls -d $X/$1/x 2>/dev/null | head -1; }
# case NAME EXPECT_RC EXPECT_CLASS(or -) FILE [prechk.sh args...]
case_() {
  local name=$1 erc=$2 ecls=$3 file=$4; shift 4
  n=$((n+1))
  if [ ! -f "$file" ]; then echo "FAIL $name: input missing ($file)"; fails=$((fails+1)); return; fi
  local out; out=$("$P" --threads "$NT" "$@" "$file" 2>&1); local rc=$?
  local ok=1
  [ "$rc" = "$erc" ] || ok=0
  if [ "$ecls" != - ]; then echo "$out" | grep -qE "^  HAZARD +$ecls " || ok=0; fi
  local hz; hz=$(echo "$out" | grep -E "^  (HAZARD|\(info\))" | awk '{print $1 $2 "=" $3}' | tr '\n' ' ')
  if [ $ok = 1 ]; then echo "PASS $name: rc=$rc $hz"; else echo "FAIL $name: rc=$rc (expected $erc, class $ecls) $hz"; echo "$out" | tail -12 | sed 's/^/    /'; fails=$((fails+1)); fi
}

# ---------------- regression exports (official behaviour from each FINDING.md)
case_ 024-dup-expr        3 nanoda_parse   "$(f1 '024-*')/solution-dupexpr.export"
case_ 024-control         0 -              "$(f1 '024-*')/solution.export"
case_ 032-name-num-2^32   3 nanoda_parse   "$(f1 '032-*')/solution.export"
case_ 032-no-nanoda-cfg   0 -              "$(f1 '032-*')/solution.export" --nanoda no
case_ 044-bvar-2^20       3 parser_abort   "$(f1 '044-*')/sol_bvar2p20.export"
case_ 044-control         0 -              "$(f1 '044-*')/Main.export"
case_ 045-height-u16      3 nanoda_parse   "$(f1 '045-*')/toy/height/solution.export"
case_ 047-depth-100k      3 nanoda_depth   "$(f1 '047-*')/toy/deepE/solution.export"
case_ 047-depth-kernel    3 kernel_depth   "$(f1 '047-*')/toy/deepE/solution.export" --nanoda no
case_ 056-indexed-proj    3 nanoda_proj    "$(f1 '056-*')/Main.export" --config "$(f1 '056-*')/cfg.json"
case_ 003-proj-idx-wrap   3 nanoda_parse   "$(f1 '003-*')/wrap.ndjson"
case_ 003-control         0 -              "$(f1 '003-*')/ctl0.ndjson"
case_ 012-strlit-strict   3 order_strlit   "$(f1 '012-*')/toy/str/solution.export"
case_ 012-strlit-checkA   0 -              "$(f1 '012-*')/toy/str/solution.export" --mode checkA
case_ 051-control         0 -              "$(f1 '051-*')/toy/good/solution.export"
case_ 060-official-ok     0 -              "$(f1 '060-*')/solution-65536.export"
case_ 065-official-ok     0 -              "$(f1 '065-*')/solution-65536.export"
# 029 (nanoda big-Nat slowness) is NOT statically detectable: prechk is clean here BY DESIGN; only running the official
# nanoda reproduces that official rejection (see README).
case_ 029-not-static      0 -              "$(f1 '029-*')/toy/shr/solution.export"

# ---------------- exact boundaries (official nanoda 4c544ed, verified:
#   name number 2^32-1 accepted / 2^32 'expected u32'; height 65535 accepted / 65536 'expected u16';
#   65,535 nested binders (bvar 65,534) accepted / 65,536 (bvar 65,535) panics at nanoda src/expr.rs:814 (u16 overflow))
sed 's/"i":4294967296/"i":4294967295/' "$(f1 '032-*')/solution.export" > "$T/n32m1.export"
case_ bnd-name-num-2^32-1 0 -              "$T/n32m1.export"
sed -E 's/"regular":6553[6-9]\}/"regular":65535}/; s/"regular":6554[0-9]\}/"regular":65535}/' "$(f1 '045-*')/toy/height/solution.export" > "$T/h65535.export"
case_ bnd-height-65535    0 -              "$T/h65535.export"

# ---------------- exact Lean.Replay order simulation (ground truth: ReplayHazards.lean = Lean's own NameSet order:
#   012 toy 8 issues = 4 declarations, depth 20; rh-mid 16 = 8, depth 66; Mathlib 42 = 21, depth 55; 8M chain depth 4,197,622)
stat_() {   # stat_ NAME PATTERN FILE [args]: the report line 'replay order: ...' must match PATTERN
  local name=$1 pat=$2 file=$3; shift 3; n=$((n+1))
  local out; out=$("$P" --threads "$NT" "$@" "$file" 2>&1)
  if echo "$out" | grep -E "^  replay order: EXACT" | grep -qE "$pat"; then echo "PASS $name: $(echo "$out" | grep '^  replay order' | sed 's/^ *//')";
  else echo "FAIL $name: expected '$pat' in: $(echo "$out" | grep 'replay order')"; fails=$((fails+1)); fi
}
stat_ sim-012-exact-4     "order hazards exact 4 / .*walk depth 20$" "$(f1 '012-*')/toy/str/solution.export"
stat_ sim-051-depth-20    "order hazards exact 0 / .*walk depth 20$" "$(f1 '051-*')/toy/good/solution.export"

# ---------------- export-completeness guard (--closure TARGETS): official lean4export output is closed + has every target
TG="$(f1 '032-*')/export-targets.txt"
case_ clos-032-complete   0 -              "$(f1 '032-*')/solution.export" --closure "$TG"
head -n 16000 "$(f1 '032-*')/solution.export" > "$T/trunc.export"
case_ clos-truncated      3 closure        "$T/trunc.export" --closure "$TG"
python3 -I - "$(f1 '032-*')/solution.export" "$T/dropthm.export" <<'PY'
import sys
L = open(sys.argv[1], 'rb').read().split(b'\n')
thm = [i for i, l in enumerate(L) if l.startswith(b'{"def":')]
del L[thm[len(thm) // 2]]          # drop one definition that later records refer to
open(sys.argv[2], 'wb').write(b'\n'.join(L))
PY
case_ clos-dropped-decl   3 closure        "$T/dropthm.export" --closure "$TG"
echo "riemannHypothesis NoSuch.target" > "$T/badtg.txt"
case_ clos-missing-target 3 closure        "$(f1 '032-*')/solution.export" --closure "$T/badtg.txt"

# ---------------- generated exports
python3 "$(f1 '051-*')/chainapp.py" "$(f1 '051-*')/toy/good/solution.export" 200000 "$T/chain200k.export" 2 > /dev/null 2>&1
case_ 051-chain-200k      3 walk_depth     "$T/chain200k.export"
if [ $QUICK = 0 ]; then
  python3 "$(f1 '044-*')/deeplevel.py" "$(f1 '044-*')/Main.export" 16777216 "$T/deeplevel.export" > /dev/null 2>&1
  case_ 044-level-2^24    3 parser_abort   "$T/deeplevel.export"
  rm -f "$T/deeplevel.export"
fi

# ---------------- mutations of an honest export (fail closed on anything non-canonical)
B="$(f1 '024-*')/solution.export"
python3 -I - "$B" "$T" <<'PY'
import sys, re
src, out = sys.argv[1], sys.argv[2]
L = open(src, 'rb').read().split(b'\n')
if L[-1] == b'': L.pop()
def w(name, lines): open(f"{out}/{name}.export", 'wb').write(b'\n'.join(lines) + b'\n')
idx_app = next(i for i, l in enumerate(L) if b'"app":' in l)
idx_thm = next(i for i, l in enumerate(L) if l.startswith(b'{"thm":'))
idx_name = next(i for i, l in enumerate(L) if l.startswith(b'{"in":') and b'"str":' in l and i > 10)
m = L[:]; m[idx_app] = m[idx_app].replace(b',', b', ', 1); w("ws", m)                      # whitespace
m = L[:]; m.insert(idx_app, b''); w("blank", m)                                                # blank line
m = L[:]; m[idx_app] = m[idx_app] + b'\r'; w("crlf", m)                                        # CR
m = L[:]; m[idx_app] = re.sub(rb'"arg":(\d+)', lambda g: b'"arg":' + g.group(1) + b'.0', m[idx_app], 1); w("float", m)
m = L[:]; m[idx_app] = re.sub(rb'"arg":(\d+)', b'"arg":99999999', m[idx_app], 1); w("dangling", m)
m = L[:]; m.append(L[idx_thm]); w("dupdecl", m)                                                # duplicate declaration
m = L[:]; m[idx_app] = m[idx_app][:-1] + b',"extra":1}'; w("extrakey", m)
m = L[:]; m[idx_app] = re.sub(rb'"ie":(\d+)', lambda g: b'"ie":' + str(int(g.group(1)) + 1000000).encode(), m[idx_app], 1); w("noncontig", m)
m = L[:]; m[0] = b'{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.2.0"},"lean":{"githash":"x","version":"4.33.1"}}}'; w("fmtver", m)
m = L[:]; m[idx_name] = m[idx_name].replace(b'"str":"', b'"str":"\\ud800', 1); w("surrogate", m)
# mdata record appended (unused): official parser accepts, nanoda panics
last_ie = max(int(re.search(rb'"ie":(\d+)', l).group(1)) for l in L if re.search(rb'"ie":(\d+)', l))
m = L[:]; m.append(b'{"ie":%d,"mdata":{"data":{},"expr":0}}' % (last_ie + 1)); w("mdata", m)
# key order permutation inside a record (canonical-equivalent JSON): must stay clean
m = L[:]; m[idx_app] = re.sub(rb'\{"arg":(\d+),"fn":(\d+)\}', rb'{"fn":\2,"arg":\1}', m[idx_app], 1); w("keyorder", m)
PY
case_ mut-whitespace      4 malformed     "$T/ws.export"
case_ mut-blank-line      4 malformed     "$T/blank.export"
case_ mut-cr              4 malformed     "$T/crlf.export"
case_ mut-float-number    4 malformed     "$T/float.export"
case_ mut-dangling-ref    4 malformed     "$T/dangling.export"
case_ mut-dup-decl        4 malformed     "$T/dupdecl.export"
case_ mut-extra-key       4 malformed     "$T/extrakey.export"
case_ mut-noncontiguous   3 nanoda_parse  "$T/noncontig.export"
case_ mut-format-3.2.0    3 nanoda_parse  "$T/fmtver.export"
case_ mut-lone-surrogate  4 malformed     "$T/surrogate.export"
case_ mut-mdata           3 nanoda_parse  "$T/mdata.export"
case_ mut-mdata-nonanoda  0 -             "$T/mdata.export" --nanoda no
case_ mut-key-order       0 -             "$T/keyorder.export"

if [ $BENCH = 1 ]; then   # node-local benchmark exports (BENCH_INPUTS, default /scratch/bench-inputs)
  BI=${BENCH_INPUTS:-/scratch/bench-inputs}
  stat_ sim-rhmid-8-66      "order hazards exact 8 / .*walk depth 66$" "$BI/rh-mid/ref/solution.export"
  stat_ sim-mathlib-21-55   "order hazards exact 21 / .*walk depth 55$" "$BI/mathlib/export/mathlib.export"
  case_ rh-mid-checkA     0 -             "$BI/rh-mid/ref/solution.export" --mode checkA
  case_ rh-mid-strict     3 order_strlit  "$BI/rh-mid/ref/solution.export"
  case_ mathlib-checkA    0 -             "$BI/mathlib/export/mathlib.export" --mode checkA
fi
echo "cases: $n, failures: $fails"
if [ $fails = 0 ]; then echo "RESULT: PASS"; exit 0; else echo "RESULT: FAIL"; exit 1; fi
