#!/bin/bash
# xversion/test/run.sh [WORK] -- unit cases of the cross-version gate xvcheck.py. Synthetic exports (a meta line +
# a few declarations) exercise: release lookup (version + githash), unverified release / githash mismatch / unknown
# export format / missing meta -> no verdict (exit 2), the 4.37 rule 'Challenge definition is not sorried' (exit 1 for a
# non-sorried definition_names entry, 0 for `fun .. => sorryAx ..`, mdata IS stripped as in Lean's getLambdaBody,
# non-definitions are left to ccmp), and that releases without the rule ignore definition bodies.
# Optional end-to-end part (if the official toolchains exist): toy challenges exported by the OFFICIAL Lean 4.35.0 /
# 4.37.0-rc1 (own leanexport) -> xvcheck verdict = the release's own `lake comparator` verdict.
# Prints PASS/FAIL rows and RESULT; exit 0 iff no FAIL.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); XV=$H/../xvcheck.py
W=${1:-/tmp/xvtest.$$}; rm -rf "$W"; mkdir -p "$W"
fails=0
row() { if [ "$2" = "$3" ]; then echo "PASS $1 (exit $3)"; else echo "FAIL $1: expected exit $2, got $3"; fails=$((fails+1)); fi; }
meta() { printf '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"%s"},"lean":{"githash":"%s","version":"%s"}}}\n' "$3" "$2" "$1"; }
G437=0b77e12952ad39077d80d8bd6b66d601f225c321; G435=eb6cafb7290e8bd5f2937522d8d804f58f02bafc
# body(KIND): declarations: names f, sorryAx, Nat, x; def f : Nat := VALUE where VALUE depends on KIND
body() {
  cat <<'EOF'
{"in":1,"str":{"pre":0,"str":"f"}}
{"in":2,"str":{"pre":0,"str":"sorryAx"}}
{"in":3,"str":{"pre":0,"str":"Nat"}}
{"in":4,"str":{"pre":0,"str":"x"}}
{"in":5,"str":{"pre":0,"str":"g"}}
{"ie":0,"const":{"name":3,"us":[]}}
{"ie":1,"const":{"name":2,"us":[]}}
{"ie":2,"app":{"fn":1,"arg":0}}
{"ie":3,"lam":{"binderInfo":"default","body":2,"name":4,"type":0}}
{"ie":4,"bvar":0}
{"ie":5,"mdata":{"data":{},"expr":2}}
{"ie":6,"lam":{"binderInfo":"default","body":5,"name":4,"type":0}}
{"ie":7,"forallE":{"binderInfo":"default","body":0,"name":4,"type":0}}
EOF
  case $1 in
    sorried) echo '{"def":{"name":1,"levelParams":[],"type":7,"value":3,"hints":"opaque","safety":"safe","all":[1]}}';;
    real)    echo '{"def":{"name":1,"levelParams":[],"type":7,"value":3,"hints":"opaque","safety":"safe","all":[1]}}'
             ;;
    body)    echo '{"ie":8,"lam":{"binderInfo":"default","body":4,"name":4,"type":0}}'
             echo '{"def":{"name":1,"levelParams":[],"type":7,"value":8,"hints":"opaque","safety":"safe","all":[1]}}';;
    mdata)   echo '{"def":{"name":1,"levelParams":[],"type":7,"value":6,"hints":"opaque","safety":"safe","all":[1]}}';;
    thm)     echo '{"thm":{"name":1,"levelParams":[],"type":7,"value":3,"all":[1]}}';;
  esac
}
cfgf() { printf '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":[],"definition_names":[%s],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' "$1" > "$W/cfg.json"; }
t() { # t NAME EXPECTED_RC VERSION GITHASH FORMAT BODYKIND DEFNAMES
  { meta "$3" "$4" "$5"; body "$6"; } > "$W/$1.export"; cfgf "$7"
  python3 -I "$XV" "$W/$1.export" "$W/cfg.json" > "$W/$1.out" 2>&1; row "$1" "$2" $?; }
t v437-sorried           0 4.37.0-rc1 $G437 3.1.0 sorried '"f"'
t v437-body-not-sorried  1 4.37.0-rc1 $G437 3.1.0 body    '"f"'
t v437-mdata-stripped-as-getLambdaBody 0 4.37.0-rc1 $G437 3.1.0 mdata  '"f"'
t v437-not-a-def-left-to-ccmp 0 4.37.0-rc1 $G437 3.1.0 thm '"f"'
t v437-missing-left-to-ccmp 0 4.37.0-rc1 $G437 3.1.0 body '"g"'
t v437-no-definition-names 0 4.37.0-rc1 $G437 3.1.0 body  ''
# regressions: guillemet-escaped names («a.b») and definition_names: null
{ meta 4.37.0-rc1 $G437 3.1.0; echo '{"in":1,"str":{"pre":0,"str":"a.b"}}'; echo '{"in":2,"str":{"pre":0,"str":"sorryAx"}}'; echo '{"in":3,"str":{"pre":0,"str":"Nat"}}'; echo '{"in":4,"str":{"pre":0,"str":"x"}}'; echo '{"const":{"name":3,"us":[]},"ie":0}'; echo '{"bvar":0,"ie":1}'; echo '{"ie":2,"lam":{"binderInfo":"default","body":1,"name":4,"type":0}}'; echo '{"forallE":{"binderInfo":"default","body":0,"name":4,"type":0},"ie":3}'; echo '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":3,"value":2}}'; } > "$W/guillemet-body.export"
cfgf '"«a.b»"'
python3 -I "$XV" "$W/guillemet-body.export" "$W/cfg.json" > "$W/guillemet-body.out" 2>&1; row v437-guillemet-not-sorried 1 $?
{ meta 4.37.0-rc1 $G437 3.1.0; echo '{"in":1,"str":{"pre":0,"str":"a.b"}}'; echo '{"in":2,"str":{"pre":0,"str":"sorryAx"}}'; echo '{"in":3,"str":{"pre":0,"str":"Nat"}}'; echo '{"in":4,"str":{"pre":0,"str":"x"}}'; echo '{"const":{"name":3,"us":[]},"ie":0}'; echo '{"const":{"name":2,"us":[]},"ie":1}'; echo '{"app":{"arg":0,"fn":1},"ie":2}'; echo '{"ie":3,"lam":{"binderInfo":"default","body":2,"name":4,"type":0}}'; echo '{"forallE":{"binderInfo":"default","body":0,"name":4,"type":0},"ie":4}'; echo '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":3}}'; } > "$W/guillemet-sorried.export"
python3 -I "$XV" "$W/guillemet-sorried.export" "$W/cfg.json" > "$W/guillemet-sorried.out" 2>&1; row v437-guillemet-sorried 0 $?
printf '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":[],"definition_names":null,"permitted_axioms":["propext","Quot.sound","Classical.choice"]}\n' > "$W/cfg-null.json"
python3 -I "$XV" "$W/guillemet-body.export" "$W/cfg-null.json" > "$W/null-defs.out" 2>&1; row v437-definition-names-null 0 $?
t v435-body-allowed      0 4.35.0     $G435 3.1.0 body    '"f"'
t v435-githash-mismatch  2 4.35.0     $G437 3.1.0 body    '"f"'
t unverified-release-4.25 2 4.25.0     cdd38ac5115bdeec5f609e9126cce00f51ae88b3 3.1.0 body '"f"'
t unknown-format         2 4.35.0     $G435 3.0.0 body    '"f"'
# the same two cases in the canonical lean4export layout (sorted keys, compact): the fast reader decides alone
for k in sorried body; do
  { meta 4.37.0-rc1 $G437 3.1.0; body $k; } | python3 -I -c 'import json,sys
for l in sys.stdin: print(json.dumps(json.loads(l), sort_keys=True, separators=(",", ":"), ensure_ascii=False))' > "$W/canon-$k.export"
  cfgf '"f"'; python3 -I "$XV" "$W/canon-$k.export" "$W/cfg.json" > "$W/canon-$k.out" 2>&1; rc=$?
  row "v437-canonical-$k" "$([ $k = sorried ] && echo 0 || echo 1)" $rc
done
grep -q "Challenge definition is not sorried: 'f'" "$W/v437-body-not-sorried.out" && echo "PASS v437 message = official" || { echo "FAIL v437 message"; fails=$((fails+1)); }
# no meta line at all
{ body body; } > "$W/nometa.export"; cfgf '"f"'; python3 -I "$XV" "$W/nometa.export" "$W/cfg.json" > /dev/null 2>&1; row no-meta-line 2 $?
python3 -I "$XV" "$W/does-not-exist" "$W/cfg.json" > /dev/null 2>&1; row missing-file 2 $?
# ---- strict reader, kernel-closure rule, getLambdaBody mdata + cycles ----
# xt NAME EXPECTED_RC VERSION GITHASH DEFNAMES [XVCHECK-ARGS..] < body lines (after the meta line)
xt() { local n=$1 e=$2 v=$3 g=$4 d=$5; shift 5; { meta "$v" "$g" 3.1.0; cat; } > "$W/$n.export"; cfgf "$d"
  timeout 60 python3 -I "$XV" "$W/$n.export" "$W/cfg.json" "$@" > "$W/$n.out" 2>&1; row "$n" "$e" $?; }
NAMES='{"in":1,"str":{"pre":0,"str":"f"}}
{"in":2,"str":{"pre":0,"str":"sorryAx"}}
{"in":3,"str":{"pre":0,"str":"Nat"}}
{"in":4,"str":{"pre":0,"str":"x"}}
{"const":{"name":3,"us":[]},"ie":0}
{"const":{"name":2,"us":[]},"ie":1}
{"app":{"arg":0,"fn":1},"ie":2}
{"bvar":0,"ie":3}
{"forallE":{"binderInfo":"default","body":0,"name":4,"type":0},"ie":4}
{"ie":5,"lam":{"binderInfo":"default","body":3,"name":4,"type":0}}
{"ie":6,"lam":{"binderInfo":"default","body":2,"name":4,"type":0}}'
DEF_REAL='{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":5}}'
DEF_SORRY='{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":6}}'
# a definition record in any valid JSON spelling is read (official 4.37 comparator: REJECTED for a real body)
printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | xt reader-canonical-real 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$NAMES" "$(echo "$DEF_REAL" | sed 's/^{"def":/ { "def" : /; s/}}$/ } } /')" | xt reader-spaced-def-real 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$NAMES" "$(echo "$DEF_REAL" | sed 's/^{"def":/{"\\u0064ef":/')" | xt reader-escaped-def-key-real 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$(echo "$NAMES" | sed 's/^{"in":1,/{"\\u0069n":1,/')" "$DEF_REAL" | xt reader-escaped-name-key-real 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$(echo "$NAMES" | sed 's/"str":"f"/"str":"\\u0066"/')" "$DEF_REAL" | xt reader-escaped-name-string-real 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$NAMES" "$(echo "$DEF_REAL" | sed 's/^{"def":/ { "def" : /')" | xt reader-spaced-def-real-rsh-436 2 4.35.0 $G435 '"f"' --require-sorried-holes
printf '%s\n%s\n' "$NAMES" "$(echo "$DEF_SORRY" | sed 's/^{"def":/ { "def" : /')" | xt reader-spaced-def-sorried 0 4.37.0-rc1 $G437 '"f"'
# fail closed on anything the reader does not fully understand
printf '%s\n%s\n' "$NAMES" '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"name":1,"safety":"safe","type":4,"value":6}}' | xt reader-duplicate-key 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$(echo "$NAMES" | sed 's/"str":"x"/"str":"\\ud800"/')" "$DEF_SORRY" | xt reader-lone-surrogate 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n' "$NAMES" "$DEF_SORRY" '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":5}}' | xt reader-duplicate-declaration 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$(echo "$NAMES" | sed 's/{"in":4,/{"in":7,/')" "$DEF_SORRY" | xt reader-sparse-name-index 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n' "$NAMES" '{"thing":1}' "$DEF_SORRY" | xt reader-unknown-record 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n' "$NAMES" '{"ie":7,"natVal":"1"} x' "$DEF_SORRY" | xt reader-trailing-garbage 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n' "$NAMES" "$DEF_SORRY" | xt reader-hole-not-a-lean-name 2 4.37.0-rc1 $G437 '"f g"'
printf '%s\n%s\n' "$NAMES" "$DEF_SORRY" | xt reader-no-holes-not-read 0 4.37.0-rc1 $G437 ''
# getLambdaBody strips mdata between lambdas; getAppFn does not strip mdata; cycles / forward references -> no verdict
printf '%s\n%s\n%s\n%s\n' "$NAMES" '{"ie":7,"mdata":{"data":{"k":{"bool":true}},"expr":6}}' '{"ie":8,"lam":{"binderInfo":"default","body":7,"name":4,"type":0}}' \
  '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":8}}' | xt mdata-lam-mdata-lam-sorried 0 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n%s\n' "$NAMES" '{"ie":7,"mdata":{"data":{},"expr":1}}' '{"app":{"arg":0,"fn":7},"ie":8}' \
  '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":8}}' | xt mdata-mdata-under-appfn-not-sorried 1 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n' "$NAMES" '{"ie":7,"lam":{"binderInfo":"default","body":7,"name":4,"type":0}}' \
  '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":7}}' | xt mdata-self-cycle 2 4.37.0-rc1 $G437 '"f"'
printf '%s\n%s\n%s\n%s\n' "$NAMES" '{"ie":7,"lam":{"binderInfo":"default","body":8,"name":4,"type":0}}' '{"ie":8,"lam":{"binderInfo":"default","body":7,"name":4,"type":0}}' \
  '{"def":{"all":[1],"hints":"opaque","levelParams":[],"name":1,"safety":"safe","type":4,"value":7}}' | xt mdata-two-cycle 2 4.37.0-rc1 $G437 '"f"'
# a hole in the dependency closure of a kernel primitive is refused for every release (sorried or not); others pass
PRIM='{"in":1,"str":{"pre":0,"str":"Nat"}}
{"in":2,"str":{"pre":1,"str":"shiftLeft"}}
{"in":3,"str":{"pre":2,"str":"_f"}}
{"in":4,"str":{"pre":0,"str":"sorryAx"}}
{"in":5,"str":{"pre":0,"str":"x"}}
{"in":6,"str":{"pre":0,"str":"g"}}
{"const":{"name":1,"us":[]},"ie":0}
{"const":{"name":3,"us":[]},"ie":1}
{"const":{"name":4,"us":[]},"ie":2}
{"app":{"arg":0,"fn":2},"ie":3}
{"ie":4,"lam":{"binderInfo":"default","body":3,"name":5,"type":0}}
{"forallE":{"binderInfo":"default","body":0,"name":5,"type":0},"ie":5}
{"ie":6,"lam":{"binderInfo":"default","body":1,"name":5,"type":0}}
{"def":{"all":[3],"hints":"opaque","levelParams":[],"name":3,"safety":"safe","type":5,"value":4}}
{"def":{"all":[2],"hints":"opaque","levelParams":[],"name":2,"safety":"safe","type":5,"value":6}}
{"def":{"all":[6],"hints":"opaque","levelParams":[],"name":6,"safety":"safe","type":5,"value":4}}'
echo "$PRIM" | xt primclosure-closure-hole-435 2 4.35.0 $G435 '"Nat.shiftLeft._f"'
echo "$PRIM" | xt primclosure-closure-hole-437-sorried 2 4.37.0-rc1 $G437 '"Nat.shiftLeft._f"'
echo "$PRIM" | xt primclosure-closure-hole-guillemets 2 4.35.0 $G435 '"«Nat».shiftLeft.«_f»"'
echo "$PRIM" | xt primclosure-primitive-itself 2 4.35.0 $G435 '"Nat.shiftLeft"'
echo "$PRIM" | xt primclosure-unrelated-hole-435 0 4.35.0 $G435 '"g"'
echo "$PRIM" | xt primclosure-unrelated-hole-437 0 4.37.0-rc1 $G437 '"g"'
grep -q "dependency closure of the kernel primitive / builtin / kernel-implicit name 'Nat.shiftLeft'" "$W/primclosure-closure-hole-435.out" && echo "PASS primclosure message names the primitive" || { echo "FAIL primclosure message"; fails=$((fails+1)); }
# the strict reader: the canonical byte templates and the JSON path give identical tables (synthetic exports above)
python3 -I "$H/reader_equiv.py" "$XV" "$W"/reader-*.export "$W"/primclosure-*.export "$W"/mdata-*.export "$W"/canon-*.export > "$W/equiv.out" 2>&1; rc=$?
row "reader fast path = JSON path ($(grep -c '^SAME' "$W/equiv.out") read, $(grep -c '^REFUSED-ALIKE' "$W/equiv.out") refused alike)" 0 $rc
# ---- the meta line (release identity) and the release table are read strictly ----
# mt NAME EXPECTED_RC [XVCHECK-ARGS..] : line 1 = $META (literal), body from stdin, holes "f"
mt() { local n=$1 e=$2; shift 2; { printf '%s\n' "$META"; cat; } > "$W/$n.export"; cfgf '"f"'
  timeout 60 python3 -I "$XV" "$W/$n.export" "$W/cfg.json" "$@" > "$W/$n.out" 2>&1; row "$n" "$e" $?; }
EXF='"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"}'
M37='"lean":{"githash":"'$G437'","version":"4.37.0-rc1"}'
M36='"lean":{"githash":"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9","version":"4.36.0"}'
META="{\"meta\":{$EXF,$M37}}";        printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-canonical-meta-real 1
META="{\"meta\":{$EXF,$M37,$M36}}";   printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-duplicate-lean-key-437-then-436 2
META="{\"meta\":{$EXF,$M36,$M37}}";   printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-duplicate-lean-key-436-then-437 2
META="{\"meta\":{$EXF,$M37,$M36}}";   printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-duplicate-lean-key-rsh 2 --require-sorried-holes
grep -q "meta line (release identity) refused" "$W/meta-duplicate-lean-key-rsh.out" && echo "PASS meta rsh refusal names the meta line" || { echo "FAIL meta rsh reason"; fails=$((fails+1)); }
META="{\"meta\":{$EXF,\"lean\":{\"githash\":\"$G437\",\"version\":\"4.37.0-rc1\",\"version\":\"4.36.0\"}}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-duplicate-version-key 2
META="{\"meta\":{$EXF,$M37},\"meta\":{$EXF,$M36}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-duplicate-meta-key 2
META=$'\xef\xbb\xbf'"{\"meta\":{$EXF,$M37}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-utf8-bom 2
META="{\"meta\":{$EXF,\"lean\":{\"githash\":\"$G437\",\"version\":\"4.37.0-rc1\",\"extra\":1}}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-extra-key 2
META="{\"meta\":{$EXF,\"lean\":{\"githash\":\"$G437\",\"version\":4.37}}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-version-not-a-string 2
META="{\"meta\":{\"exporter\":{\"name\":\"other\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"},$M37}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-exporter-not-lean4export 2
META="{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":NaN},\"format\":{\"version\":\"3.1.0\"},$M37}}"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-nan 2
META="{\"meta\":{$EXF,$M37}} x"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-trailing-garbage 2
# an unambiguous non-compact spelling means the same release (no over-refusal): 4.37 rule applies -> REJECTED
META="{ \"meta\" : { $EXF , \"\\u006cean\" : {\"githash\":\"$G437\",\"version\":\"4.37.0-rc1\"} } }"; printf '%s\n%s\n' "$NAMES" "$DEF_REAL" | mt meta-spaced-escaped-meta-same-release 1
# the release table: strict, known rules only
python3 -I -c 'import json,sys; t=json.load(open(sys.argv[1])); t["releases"]["4.37.0-rc1"]["rules"].append("some-future-rule"); json.dump(t,open(sys.argv[2],"w"))' "$H/../releases.json" "$W/rel-unknown-rule.json"
META="{\"meta\":{$EXF,$M37}}"; printf '%s\n%s\n' "$NAMES" "$DEF_SORRY" | mt meta-table-unknown-rule 2 --releases "$W/rel-unknown-rule.json"
python3 -I -c 'import sys; s=open(sys.argv[1]).read().rstrip(); open(sys.argv[2],"w").write(s[:-1] + ", \"export_formats\": [\"9.9.9\"]}")' "$H/../releases.json" "$W/rel-dup-key.json"
META="{\"meta\":{$EXF,$M37}}"; printf '%s\n%s\n' "$NAMES" "$DEF_SORRY" | mt meta-table-duplicate-key 2 --releases "$W/rel-dup-key.json"
# deeply nested JSON (RecursionError) in a body line is the reader's own refusal
python3 -I -c 'import sys; sys.stdout.write("{\"ie\":7,\"mdata\":{\"data\":{\"k\":" + "["*200000 + "]"*200000 + "},\"expr\":1}}\n")' > "$W/deep.line"
META="{\"meta\":{$EXF,$M37}}"; printf '%s\n%s\n%s\n' "$NAMES" "$(cat "$W/deep.line")" "$DEF_SORRY" | mt meta-deep-nesting 2
grep -q "strict reader" "$W/meta-deep-nesting.out" && echo "PASS meta deep nesting refused by the strict reader" || { echo "FAIL meta deep nesting reason"; fails=$((fails+1)); }
# a valid escaped surrogate PAIR is one code point in both readers -> accepted (a lone one: refused,
# reader-lone-surrogate above)
printf '%s\n%s\n' "$(echo "$NAMES" | sed 's/"str":"x"/"str":"\\ud83d\\ude00"/')" "$DEF_SORRY" | xt meta-paired-surrogate-escape-accepted 0 4.37.0-rc1 $G437 '"f"'
# ---- reader exactness - numbers, natVal, bvar / level ranges, digit limit ----
# every reader-corpus case and every boundary case: the official answer of v4.36.0 / v4.37.0-rc1 (reader-corpus/OFFICIAL.jsonl), or a refusal
python3 -I "$H/reader-corpus/run.py" "$XV" > "$W/reader-corpus.out" 2>&1; rc=$?
grep '^FAIL' "$W/reader-corpus.out"
row "reader exactness rows: $(grep -c '^PASS' "$W/reader-corpus.out") pass, $(grep -c '^FAIL' "$W/reader-corpus.out") fail (official answer or refusal)" 0 $rc
# the level-depth check (the 2^24-1 limit itself needs 16M level records: mechanism tested with a lowered bound)
python3 -I - "$XV" "$W" > "$W/ldepth.out" 2>&1 <<'PYL'
import importlib.util, sys
s = importlib.util.spec_from_file_location("x", sys.argv[1]); X = importlib.util.module_from_spec(s); s.loader.exec_module(X)
M = '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9","version":"4.36.0"}}}\n'
def chain(n, kind):
    ls = [M]
    for i in range(1, n + 1):
        ls.append('{"il":%d,"succ":%d}\n' % (i, i - 1) if kind == "succ" else '{"il":%d,"%s":[%d,0]}\n' % (i, kind, i - 1))
    p = "%s/ld-%s-%d.export" % (sys.argv[2], kind, n); open(p, "w").write("".join(ls)); return p
X.MAX_LEVEL_DEPTH = 3
ok = True
for kind in ("succ", "max", "imax"):
    X.read_export(chain(3, kind))
    try:
        X.read_export(chain(4, kind)); ok = False; print("depth 4 accepted for", kind)
    except X.ExportError as e:
        ok = ok and "universe level depth 4 is too big" in str(e)
sys.exit(0 if ok else 1)
PYL
row "level depth bound (lowered to 3: depth 3 read, depth 4 refused; succ / max / imax)" 0 $?
# xvcheck never changes CPython's interpreter-wide int_max_str_digits; integer tokens above
# it are converted exactly in chunks. (a) exact values at the chunk / limit boundaries, reads under the limits 4300, 640
# (the minimum) and 0 with the limit unchanged after each call, and no setter call in xvcheck at all
python3 -I - "$XV" "$H/reader-corpus" > "$W/r31a.out" 2>&1 <<'PYA'
import importlib.util, sys
s = importlib.util.spec_from_file_location("x", sys.argv[1]); X = importlib.util.module_from_spec(s); s.loader.exec_module(X)
ok = "set_int_max_str_digits(" not in open(sys.argv[1]).read()
for lim in (4300, 640, 0):
    sys.set_int_max_str_digits(lim)
    for t in ("1" + "0" * 4300, "9" * 599, "9" * 600, "8" * 601, "-" + "7" * 1201, "1" + "2" * 19999, "0", "-0"):
        sys.set_int_max_str_digits(0); ref = int(t); sys.set_int_max_str_digits(lim)
        ok = ok and X._exact_int(t) == ref and sys.get_int_max_str_digits() == lim
    for f in ("digits-v4.36.0.ndjson", "r3-namenum-20000-digits.ndjson", "ordinary.ndjson"):
        X.read_export(sys.argv[2] + "/" + f)
        ok = ok and sys.get_int_max_str_digits() == lim
print("ok" if ok else "FAILED"); sys.exit(0 if ok else 1)
PYA
row "interpreter int digit limit never touched (exact chunked ints; reads under limits 4300 / 640 / 0)" 0 $?
# (b) two concurrent reader threads (4301- and 20000-digit numeric names) + a sibling thread that keeps checking the
# interpreter limit (4300, and int() of 5000 digits still refused): every read succeeds, nothing leaks
python3 -I - "$XV" "$H/reader-corpus" > "$W/r31b.out" 2>&1 <<'PYB'
import importlib.util, sys, threading
s = importlib.util.spec_from_file_location("x", sys.argv[1]); X = importlib.util.module_from_spec(s); s.loader.exec_module(X)
errs, stop = [], threading.Event()
def reader(f, n):
    want = None
    for _ in range(n):
        try:
            m = X.read_export(sys.argv[2] + "/" + f)
            got = list(m.cid_comp)          # compared as values (no int->str conversion in the test either)
            want = want or got
            if got != want: errs.append("different tables " + f)
        except Exception as e:
            errs.append("%s: %s" % (f, str(e)[:100]))
def sibling():
    while not stop.is_set():
        if sys.get_int_max_str_digits() != 4300: errs.append("limit changed to %d" % sys.get_int_max_str_digits())
        try:
            int("9" * 5000); errs.append("sibling int() of 5000 digits was allowed")
        except ValueError:
            pass
ts = [threading.Thread(target=reader, args=("digits-v4.36.0.ndjson", 40)),
      threading.Thread(target=reader, args=("r3-namenum-20000-digits.ndjson", 40))]
sb = threading.Thread(target=sibling); sb.start()
for t in ts: t.start()
for t in ts: t.join()
stop.set(); sb.join()
if sys.get_int_max_str_digits() != 4300: errs.append("final limit %d" % sys.get_int_max_str_digits())
print("ok" if not errs else "FAILED %d: %s" % (len(errs), errs[:3])); sys.exit(0 if not errs else 1)
PYB
row "two concurrent read_export threads + sibling: all reads ok, interpreter limit stays 4300" 0 $?
# ---- config cases: config decoding before vetoes, release table, long numeric names, exit codes ----
Y=$H/config-cases
( cd "$Y" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL config-case inputs: SHA256SUMS"; fails=$((fails+1)); }
# cfg6 (official evidence): 4.37 challenge with a non-sorried hole + "challenge_module": 17 -> official Lake exits 2
# (config decoding); the gate must refuse the config (rc 2), never REJECT through the release veto
python3 -I "$XV" "$Y/cfg6-challenge.export" "$Y/cfg6-comparator.json" > "$W/cfg6.out" 2>&1
row "cfg6 config error before the 4.37 sorried veto (official exit 2) -> DECLINED, never REJECTED" 2 $?
# the official Config decoding, field by field (same challenge: with a valid config the veto says REJECTED, rc 1)
python3 -I - "$Y/cfg6-comparator.json" "$W" > "$W/cfg6-variants.txt" <<'PYC'
import json, sys
base = json.load(open(sys.argv[1])); base["challenge_module"] = "Challenge"
def v(name, **kw):
    c = dict(base)
    for k, x in kw.items():
        if x == "<DEL>": c.pop(k, None)
        else: c[k] = x
    open("%s/cfg6-%s.json" % (sys.argv[2], name), "w").write(json.dumps(c)); print(name)
v("valid-1"); v("challenge_module-missing-2", challenge_module="<DEL>"); v("solution_module-null-2", solution_module=None)
v("theorem_names-string-2", theorem_names="qaTheorem"); v("theorem_names-number-elem-2", theorem_names=[1])
v("permitted_axioms-missing-2", permitted_axioms="<DEL>"); v("definition_names-null-0", definition_names=None)
v("definition_names-string-2", definition_names="chooseNat"); v("enable_nanoda-string-2", enable_nanoda="yes")
v("enable_nanoda-null-1", enable_nanoda=None); v("external_kernels-string-value-2", external_kernels={"k": "cmd"})
v("external_kernels-array-2", external_kernels=[]); v("external_kernels-named-2", external_kernels={"k": ["cmd"]})
v("extra-key-ignored-1", foo=1)
PYC
while read -r n; do python3 -I "$XV" "$Y/cfg6-challenge.export" "$W/cfg6-$n.json" > /dev/null 2>&1; row "cfg6 config $n (expected rc = suffix)" "${n##*-}" $?; done < "$W/cfg6-variants.txt"
# cfg1: a release entry without "rules" -> refused (not an empty rule list)
python3 -I "$XV" "$Y/cfg1-challenge.export" "$Y/cfg1-comparator.json" --releases "$Y/cfg1-releases.json" > /dev/null 2>&1
row "cfg1 releases.json entry without rules -> DECLINED" 2 $?
# cfg5 (official evidence, official exit 0 on both): a 4301-digit numeric name component in the config, and a
# 10^4300+37 numeric binder name in an unedited official export -> read exactly, gate OK
python3 -I "$XV" "$Y/cfg5-names-numeric-challenge.export" "$Y/cfg5-names-numeric-comparator.json" > /dev/null 2>&1
row "cfg5 config hole name with a 4301-digit numeric component -> OK (official exit 0)" 0 $?
python3 -I "$XV" "$Y/cfg5-big-component-challenge.export" "$Y/cfg5-big-component-comparator.json" > /dev/null 2>&1
row "cfg5 official export with a 10^4300+37 numeric name component -> OK (official exit 0)" 0 $?
# cfg3: missing option values and an unwritable --json are exit 2 with ONE record (exit 1 is reserved for REJECTED)
python3 -I "$XV" "$Y/cfg1-challenge.export" "$Y/cfg1-comparator.json" --json > /dev/null 2>&1; row "cfg3 --json without a value -> exit 2" 2 $?
python3 -I "$XV" "$Y/cfg1-challenge.export" "$Y/cfg1-comparator.json" --releases > /dev/null 2>&1; row "cfg3 --releases without a value -> exit 2" 2 $?
python3 -I "$XV" "$Y/cfg1-challenge.export" "$Y/cfg1-comparator.json" --json "$W" > "$W/cfg3.out" 2>/dev/null; rc=$?
[ "$(wc -l < "$W/cfg3.out")" = 1 ] && grep -q '"DECLINED"' "$W/cfg3.out" && [ $rc = 2 ] && row "cfg3 unwritable --json -> exit 2, one DECLINED record" 2 2 || row "cfg3 unwritable --json -> exit 2, one DECLINED record" 2 "$rc/$(wc -l < "$W/cfg3.out")-lines"
# ---- the official comparator's other pre-compare exit-2 config checks (resolveExternalKernels, own-kernel name) ----
# official Lean 4.37.0-rc1 lake comparator on the cfg6 pair (4.37 challenge, non-sorried hole): valid 1, empty map 1,
# enable_nanoda + external_kernels 2, empty command 2, kernel not found 2, kernel named `Lean default` 2
# variant names: <case>-<expected rc without flag>-<expected rc with --caller-resolves-kernels>
python3 -I - "$Y/cfg6-comparator.json" "$Y/cfg5-names-numeric-comparator.json" "$W" > "$W/r32-variants.txt" <<'PYK'
import json, sys
base = json.load(open(sys.argv[1])); base["challenge_module"] = "Challenge"
srt = json.load(open(sys.argv[2]))
def v(name, b, **kw):
    c = dict(b); c.update(kw); open("%s/r32-%s.json" % (sys.argv[3], name), "w").write(json.dumps(c)); print(name)
v("nanoda-conflict-2-2", base, enable_nanoda=True, external_kernels={"k": ["nanoda_bin"]})
v("empty-command-2-2", base, external_kernels={"k": []})
v("lean-default-name-2-2", base, external_kernels={"Lean default": ["/bin/true"]})
v("kernel-named-2-1", base, external_kernels={"k": ["/nonexistent/kernel-xyz"]})
v("enable-nanoda-2-1", base, enable_nanoda=True)
v("empty-map-1-1", base, external_kernels={})
v("no-kernels-1-1", base)
v("sorried-kernel-named-0-0", srt, external_kernels={"k": ["/nonexistent/kernel-xyz"]})
v("digit-run-20001-2-2", base, definition_names=["x." + "1" * 20001])
v("digit-run-20000-0-0", base, definition_names=["x." + "1" * 20000])
PYK
while read -r n; do r=${n%-*}; wf=${n##*-}; wo=${r##*-}
  c=$Y/cfg6-challenge.export; case $n in sorried-*) c=$Y/cfg5-names-numeric-challenge.export;; esac
  python3 -I "$XV" "$c" "$W/r32-$n.json" > /dev/null 2>&1; row "config $n (no flag)" "$wo" $?
  python3 -I "$XV" "$c" "$W/r32-$n.json" --caller-resolves-kernels > /dev/null 2>&1; row "config $n (--caller-resolves-kernels)" "$wf" $?
done < "$W/r32-variants.txt"
# ---- interpreter-independent JSON nesting bound; exponent-spelled index (cfg5b) stays a documented refusal ----
# (1) depth <= 512 is read, 513 refused, on body lines, the meta line path and the config; nested-1100 is refused under
#     any recursion limit (the bound is explicit, checked before the JSON parse)
python3 -I - "$XV" "$H/reader-corpus" "$W" > "$W/r33.out" 2>&1 <<'PYD'
import importlib.util, json, subprocess, sys
s = importlib.util.spec_from_file_location("x", sys.argv[1]); X = importlib.util.module_from_spec(s); s.loader.exec_module(X)
cx, w = sys.argv[2], sys.argv[3]
meta = open(cx + "/ordinary.ndjson", "rb").readline()
def body(depth):     # the name record holds an ignored field nested so that the line's total depth is `depth`
    k = depth - 2
    return (meta + b'{"in":1,"str":{"extra":' + b"[" * k + b"0" + b"]" * k + b',"pre":0,"str":"A"}}\n'
            + b'{"ie":0,"sort":0}\n{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}\n')
ok = X.MAX_JSON_DEPTH == 512
for d, want in ((512, True), (513, False)):
    p = "%s/depth-%d.ndjson" % (w, d); open(p, "wb").write(body(d))
    try:
        X.read_export(p); got = True
    except X.ExportError:
        got = False
    ok = ok and got == want
    rc = subprocess.run(["/usr/bin/python3", "-I", sys.argv[1], p, cx + "/config.json"], capture_output=True).returncode
    ok = ok and rc == (0 if want else 2)
    cfg = json.load(open(cx + "/config.json")); txt = json.dumps(cfg)[:-1] + ',"extra":' + "[" * (d - 1) + "0" + "]" * (d - 1) + "}"
    open("%s/cfg-depth-%d.json" % (w, d), "w").write(txt)
    rc = subprocess.run(["/usr/bin/python3", "-I", sys.argv[1], cx + "/ordinary.ndjson", "%s/cfg-depth-%d.json" % (w, d)],
                        capture_output=True).returncode
    ok = ok and rc == (0 if want else 2)
for lim in (1000, 100000):
    sys.setrecursionlimit(lim)
    try:
        X.read_export(cx + "/nested-1100.ndjson"); ok = False
    except X.ExportError as e:
        ok = ok and "nesting deeper than 512" in str(e)
    X.read_export(cx + "/nested-8.ndjson")
print("ok" if ok else "FAILED"); sys.exit(0 if ok else 1)
PYD
row "JSON nesting bound 512 (body + config: 512 read, 513 refused; nested-1100 refused under recursion limits 1000 / 100000)" 0 $?
# (2) cfg5b: name index spelled 1e0; official Lean 4.36 lake comparator reads it (exit 0); the gate refuses every
#     fraction / exponent token (official exports never contain one) -> documented conservative refusal
python3 -I "$XV" "$Y/cfg5b-challenge.export" "$Y/cfg5b-comparator.json" > "$W/cfg5b.out" 2>&1; rc=$?
grep -q "non-integer JSON number 1e0" "$W/cfg5b.out" && row "cfg5b index spelled 1e0 -> DECLINED (conservative; official reads it)" 2 $rc || row "cfg5b index spelled 1e0 -> DECLINED (conservative; official reads it)" 2 "$rc/other-reason"
# end-to-end with the official toolchains (optional)
TCR=${XV_TOOLCHAINS:-}   # optional: a directory of official toolchains (elan layout); unset = skip
for v in v4.35.0 v4.37.0-rc1; do
  TC=$TCR/leanprover--lean4---$v
  if [ ! -x "$TC/bin/leanexport" ]; then echo "SKIP e2e $v (no official toolchain at $TC)"; continue; fi
  for kind in sorried real; do
    d=$W/e2e-$v-$kind; mkdir -p "$d/chal" "$d/sol"
    val=$([ $kind = sorried ] && echo sorry || echo 'n + 1')
    for x in chal sol; do
      m=$([ $x = chal ] && echo Challenge || echo Main)
      printf 'name = "%s"\ndefaultTargets = ["%s"]\n\n[[lean_lib]]\nname = "%s"\n' $m $m $m > "$d/$x/lakefile.toml"
      echo "leanprover/lean4:$v" > "$d/$x/lean-toolchain"
    done
    printf 'def f (n : Nat) : Nat := %s\ntheorem foo : f 2 = f 2 := sorry\n' "$val" > "$d/chal/Challenge.lean"
    printf 'def f (n : Nat) : Nat := n + 1\ntheorem foo : f 2 = f 2 := rfl\n' > "$d/sol/Main.lean"
    echo '{"challenge_module":"Challenge","solution_module":"Main","theorem_names":["foo"],"definition_names":["f"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}' > "$d/chal/comparator.json"
    E=(env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$d/home" LANG=C.UTF-8)
    TG="foo f propext Quot.sound Classical.choice Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
    for x in chal sol; do m=$([ $x = chal ] && echo Challenge || echo Main)
      ( cd "$d/$x" && "${E[@]}" lake build > build.log 2>&1 && "${E[@]}" LEAN_PATH="$d/$x/.lake/build/lib/lean:$TC/lib/lean" leanexport $m -- $TG > "$d/$x.export" 2>/dev/null ); done
    ( cd "$d/chal" && "${E[@]}" lake comparator --config comparator.json --challenge-from-export "$d/chal.export" --solution-from-export "$d/sol.export" > "$d/cmp.out" 2>&1 ); orc=$?
    python3 -I "$XV" "$d/chal.export" "$d/chal/comparator.json" > "$d/xv.out" 2>&1; xrc=$?
    # xvcheck gates the challenge only: compare with the official verdict on an otherwise accepted solution
    exp=$([ $orc = 0 ] && echo 0 || echo 1)
    row "e2e $v challenge-def-$kind (official comparator exit $orc)" $exp $xrc
  done
done
[ $fails = 0 ] && { echo "RESULT: PASS"; rm -rf "$W"; exit 0; } || { echo "RESULT: FAIL ($fails) - work dir $W"; exit 1; }
