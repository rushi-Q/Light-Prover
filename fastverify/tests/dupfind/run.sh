#!/bin/bash
# tests/dupfind/run.sh [WORKDIR]  (kind: component, untrusted analysis tool; ~20 s, no Mathlib)
# Regression test of tools/dupfind (duplicate-lemma lookup by kernel statement hash):
#   index-selftest   index the pinned self-test export (584 rows (462 declarations; inductive blocks one row per type/ctor/rec)) -> sqlite index, lookup of its target is 'unique'
#   crafted-dup      a copy of the self-test export with the target theorem re-declared under a new name (dense indices,
#                    same type) -> lookup finds the duplicate; a theorem whose type differs is NOT reported
#   query-core       a core-only query module (no Mathlib) with two theorems of the same statement under different names:
#                    compile (sandbox) -> native export -> hash -> 'same_statement_in_file' and, after indexing that export,
#                    the lookup of the second name finds the first
#   query-warm       the same query with --snapshot (header snapshot) + --fast-export: same answers
#   aux-filter       auto-generated names (_proof_N, _simp_N, match_N, instances) are hidden unless --aux
# Prints 'PASS|FAIL case detail' rows and 'RESULT PASS|FAIL'.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/dupfind.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"; fails=0
DF="python3 -I $FV/tools/dupfind/dupfind.py"
row() { echo "$1 $2: $3"; [ "$1" = PASS ] || fails=$((fails+1)); }
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' "$FV/config/components.json")
ST=$(awk '$1=="PIN" && $2=="selftest_good" {print $4}' "$FV/check/sound/pins.env")
[ -f "$ST" ] || { row FAIL setup "self-test export $ST missing"; echo "RESULT FAIL"; exit 1; }
EXPH=$(python3 -I -c 'import sys; sys.path.insert(0, sys.argv[1]); import dupfind; print(dupfind.find_exphash() or "")' "$FV/tools/dupfind")
[ -n "$EXPH" ] || { row FAIL setup "no exphash binary (build tools/compress/exphash or set DUPFIND_EXPHASH)"; echo "RESULT FAIL"; exit 1; }
# 1. index the self-test export
$DF index selftest "$ST" "$W/ix-st" --origin library > "$W/ix-st.log" 2>&1 && grep -q '"n_decls": 584' "$W/ix-st.log" \
  && row PASS index-selftest "584 rows (462 declarations; inductive blocks one row per type/ctor/rec)" || row FAIL index-selftest "$(tail -1 "$W/ix-st.log")"
$DF lookup --index "$W/ix-st" --name fvSelfTest --json > "$W/l1.json" 2>&1 && python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); it=d["items"][0]; sys.exit(0 if it.get("duplicate") is False and it["matches"]==[] else 1)' "$W/l1.json" \
  && row PASS lookup-unique "fvSelfTest unique" || row FAIL lookup-unique "$(cat "$W/l1.json" | cut -c1-200)"
# 2. crafted duplicate: re-declare the target under a new name (same type) and a decoy with another type
python3 -I - "$ST" "$W/dup.export" <<'PY'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
rows = [l for l in open(src, encoding="utf-8")]
names = {}; nmax = -1; thm = None; other = None
for l in rows:
    r = json.loads(l)
    if "in" in r:
        nmax = max(nmax, r["in"]); s = r.get("str")
        if s: names[r["in"]] = (names.get(s["pre"], "") + "." + s["str"]).lstrip(".") if s["pre"] else s["str"]
    if "thm" in r and names.get(r["thm"]["name"]) == "fvSelfTest": thm = r["thm"]
    if "thm" in r and names.get(r["thm"]["name"]) != "fvSelfTest" and r["thm"]["levelParams"] == [] and other is None: other = r["thm"]
assert thm and other
out = open(dst, "w", encoding="utf-8"); out.writelines(rows)
n1, n2 = nmax + 1, nmax + 2
out.write(json.dumps({"in": n1, "str": {"pre": 0, "str": "fvSelfTestTwin"}}) + "\n")
out.write(json.dumps({"thm": {"all": [n1], "levelParams": [], "name": n1, "type": thm["type"], "value": thm["value"]}}) + "\n")
out.write(json.dumps({"in": n2, "str": {"pre": 0, "str": "fvSelfTestDecoy"}}) + "\n")
out.write(json.dumps({"thm": {"all": [n2], "levelParams": [], "name": n2, "type": other["type"], "value": other["value"]}}) + "\n")
PY
$DF index crafted "$W/dup.export" "$W/ix-dup" > "$W/ix-dup.log" 2>&1 || row FAIL crafted-index "$(tail -1 "$W/ix-dup.log")"
$DF lookup --index "$W/ix-dup" --name fvSelfTest --name fvSelfTestDecoy --json > "$W/l2.json" 2>&1 && python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); a,b=d["items"]
ok = a["duplicate"] and [m["name"] for m in a["matches"]]==["fvSelfTestTwin"] and all(m["name"]!="fvSelfTest" for m in b["matches"])
sys.exit(0 if ok else 1)' "$W/l2.json" && row PASS crafted-dup "twin found, decoy not matched to the target" || row FAIL crafted-dup "$(cut -c1-300 "$W/l2.json")"
# 2b. delta: the crafted export vs the self-test index -> exactly the twin is reported as an introduced duplicate
$DF delta "$W/dup.export" --index "$W/ix-st" --json > "$W/delta.json" 2>&1 && python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); it={i["query"]:i for i in d["items"]}
tw=it.get("fvSelfTestTwin"); de=it.get("fvSelfTestDecoy")
ok = d["new_or_changed_theorems"]==2 and tw and [m["name"] for m in tw["matches"]]==["fvSelfTest"] and de and all(m["name"]!="fvSelfTest" for m in de["matches"]) and de["matches"]
sys.exit(0 if ok else 1)' "$W/delta.json" \
  && row PASS delta "2 new theorems: twin == fvSelfTest, decoy == the theorem it copied (not fvSelfTest)" || row FAIL delta "$(cut -c1-300 "$W/delta.json")"
# 3. query path, core only
mkdir -p "$W/ws/.lake/packages" "$W/q"
cat > "$W/q/Q.lean" <<'LEAN'
theorem dup_first (n : Nat) : n + 0 = n := sorry
namespace DupTest
theorem second (m : Nat) : m + 0 = m := sorry
theorem third (m : Nat) : 0 + m = m := sorry
end DupTest
LEAN
$DF query "$W/q/Q.lean" --index "$W/ix-st" --toolchain "$TC" --packages "$W/ws" --fv "$FV" --work "$W/qw" --keep --json > "$W/q1.json" 2>"$W/q1.err"; rc=$?
python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); it={i["query"]:i for i in d["items"]}
ok = it["DupTest.second"].get("same_statement_in_file")=="dup_first" and "same_statement_in_file" not in it["DupTest.third"] and not it["dup_first"]["duplicate"]
sys.exit(0 if ok else 1)' "$W/q1.json" 2>/dev/null && row PASS query-core "3 targets exported; second == first in file; third differs ($(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["seconds"])' "$W/q1.json"))" \
  || row FAIL query-core "rc=$rc $(tail -c 300 "$W/q1.err") $(cut -c1-200 "$W/q1.json")"
$DF index query "$W/qw/query.export" "$W/ix-q" > /dev/null 2>&1 && $DF lookup --index "$W/ix-q" --name DupTest.second --json > "$W/l3.json" 2>&1 && python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); it=d["items"][0]; sys.exit(0 if it["duplicate"] and [m["name"] for m in it["matches"]]==["dup_first"] else 1)' "$W/l3.json" \
  && row PASS query-index-lookup "DupTest.second -> dup_first" || row FAIL query-index-lookup "$(cut -c1-300 "$W/l3.json")"
# 4. warm path
mkdir -p "$W/snap"
for i in 1 2; do $DF query "$W/q/Q.lean" --index "$W/ix-q" --toolchain "$TC" --packages "$W/ws" --fv "$FV" --work-dir "$W" --snapshot "$W/snap" --fast-export --json > "$W/q2-$i.json" 2>"$W/q2-$i.err" || true; done
python3 -I -c '
import json,sys; d=json.load(open(sys.argv[1])); it={i["query"]:i for i in d["items"]}
ok = d["seconds"]["warm"] and d["seconds"]["fast_export"] and it["DupTest.second"]["duplicate"] and it["dup_first"]["duplicate"] and not it["DupTest.third"]["duplicate"]
sys.exit(0 if ok else 1)' "$W/q2-2.json" 2>/dev/null && row PASS query-warm "snapshot + direct export, same answers ($(python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1]))["seconds"]; print({k:s[k] for k in ("compile","export","total")})' "$W/q2-2.json"))" \
  || row FAIL query-warm "$(tail -c 300 "$W/q2-2.err") $(cut -c1-200 "$W/q2-2.json")"
# 5. aux filter
python3 -I -c '
import sys; sys.path.insert(0, sys.argv[1]); import dupfind as d
aux = ["Foo.bar._proof_3", "X._simp_1_2", "Foo.match_1", "instFooBar", "_private.Mathlib.A.0.x", "Foo.eq_1", "Foo.bar._abel_1_4"]
user = ["Nat.add_comm", "GlobalTheory.T.cT_sub", "Foo.bar_proof", "Foo.simp_lemma", "instances_count"]
bad = [n for n in aux if not d.is_aux(n)] + [n for n in user if d.is_aux(n)]
print(bad); sys.exit(1 if bad else 0)' "$FV/tools/dupfind" > "$W/aux.out" 2>&1 && row PASS aux-filter "auxiliary names hidden, user names kept" || row FAIL aux-filter "$(cat "$W/aux.out")"
[ $fails = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL ($fails)"
