#!/bin/bash
# build/test/merge.sh [WORK] : component test of the B3 'merge' transform (S02; sound preset only, untrusted build).
#   projects/merge: T.S2 = {T.N1, T.S2} merges and builds; Main / T.Base stay singletons (other lib options / importers in
#   two groups); T.M2 uses `val` with `open P Q` while T.M1 declares P.val:
#   run 1 (default rules): the ambiguity rule keeps T.M2 out of T.S's group -> T.S = {T.M1, T.S}, no failure;
#   run 2 (merge=--no-ambiguity-rule): T.S = {T.M1, T.M2, T.S} fails merged ('ambiguous term') -> sched.py
#   --split-fallback rebuilds its members from their original records; the build still succeeds.
#   run 3 (merge=...:--deny:FILE with T.M2): the measured deny list dissolves that group up front (no split).
# Checks per run: BUILT; groups; splits; modules built; .olean files (T.N1 lives inside T.S2.olean); sources untouched.
#   projects/merge-silent: a SILENT leak (namespace-prefix shadowing) breaks a downstream module: with the default rules
#   the exact leak rule keeps the modules apart; with all rules off the build fails merged and build.sh rebuilds it
#   unmerged (BUILT either way).
#   projects/merge-order: a merged header must keep the original import order (equal-priority instances); the old
#   member-order header breaks a downstream module (unmerged retry), the current one does not.
#   projects/merge-late: merge=late (planner concurrent with the build, groups swapped in later; split works after it).
# Prints PASS/FAIL per case and 'RESULT: PASS|FAIL'; exit 0 iff all pass.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); D=$(cd "$H/../.." && pwd)
W=${1:-/tmp/fv-mergetest-$$}; rm -rf "$W"; mkdir -p "$W"
WS=$W/no-packages; mkdir -p "$WS"
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
fail=0; ok() { echo "PASS $1"; }; bad() { echo "FAIL $1"; fail=1; }
run() { # name unsafe expected_groups_json expected_splits_json expected_built_json
  local n=$1; rm -rf "$W/$n"; mkdir -p "$W/$n"; cp -a "$H/projects/merge" "$W/$n/proj"
  "$D/build/build.sh" "$W/$n/proj" "$WS" "$TC" --log "$W/$n/log" --threads 4 --preset B3 --unsafe "$2" > "$W/$n/fast.json" 2>&1
  grep -q '"status": "BUILT"' "$W/$n/fast.json" && ok "$n: toy build BUILT" || bad "$n: toy build: $(tail -1 "$W/$n/fast.json" | cut -c1-300)"
  /usr/bin/python3 -I - "$W/$n" "$3" "$4" "$5" <<'PY' || fail=1
import json, os, sys
W = sys.argv[1]; exp_g, exp_s, exp_b = (json.loads(x) for x in sys.argv[2:5]); f = True
n = os.path.basename(W)
g = json.load(open(f'{W}/log/merge/groups.json'))
print(('PASS' if g == exp_g else 'FAIL') + f' {n}: merge groups {g}'); f &= g == exp_g
ev = [json.loads(l) for l in open(f'{W}/log/sched.out') if l.startswith('{')]
splits = [e['module'] for e in ev if e.get('event') == 'split']
print(('PASS' if splits == exp_s else 'FAIL') + f' {n}: splits {splits}'); f &= splits == exp_s
built = sorted(e['module'] for e in ev if e.get('event') == 'module' and e['rc'] == 0)
print(('PASS' if built == sorted(exp_b) else 'FAIL') + f' {n}: modules built ok {built}'); f &= built == sorted(exp_b)
lib = f'{W}/proj/.lake/build/lib/lean'
have = sorted(m for m in ['T.Base', 'T.M1', 'T.M2', 'T.S', 'T.S2', 'T.N1', 'Main'] if os.path.exists(lib + '/' + m.replace('.', '/') + '.olean'))
print(('PASS' if have == sorted(exp_b) else 'FAIL') + f' {n}: oleans {have}'); f &= have == sorted(exp_b)
sys.exit(0 if f else 1)
PY
  diff -r -q "$H/projects/merge/src" "$W/$n/proj/src" > /dev/null && ok "$n: project sources untouched" || bad "$n: project sources changed"
}
run default merge,skip-kernel-tc '{"T.S": ["T.M1", "T.S"], "T.S2": ["T.N1", "T.S2"]}' '[]' '["Main", "T.Base", "T.M2", "T.S", "T.S2"]'
run noamb merge=--no-ambiguity-rule:--no-exact-leak-rule,skip-kernel-tc '{"T.S": ["T.M1", "T.M2", "T.S"], "T.S2": ["T.N1", "T.S2"]}' '["T.S"]' '["Main", "T.Base", "T.M1", "T.M2", "T.S", "T.S2"]'
# measured deny list (mergeplan --deny; build.sh passes build/hints/merge-deny.txt by default): the group that fails in
# 'noamb' is dissolved up front -> no split, every module built on its own except the T.S2 group
printf '# test deny list\nT.M2  # failed merged in noamb\n' > "$W/deny.txt"
run deny "merge=--no-ambiguity-rule:--no-exact-leak-rule:--deny:$W/deny.txt,skip-kernel-tc" '{"T.S2": ["T.N1", "T.S2"]}' '[]' '["Main", "T.Base", "T.M1", "T.M2", "T.S", "T.S2"]'
/usr/bin/python3 -I -c "import json,sys; s=json.load(open(sys.argv[1])); sys.exit(0 if (s['deny_names'], s['deny_dissolved_groups'], s['deny_dissolved_members']) == (1, 1, 3) else 1)" "$W/deny/log/merge/stats.json" && ok "deny: stats (1 name, 1 group, 3 members dissolved)" || bad "deny: stats $(cat "$W/deny/log/merge/stats.json" 2>/dev/null | cut -c1-300)"
[ -f "$W/default/log/merge-deny.txt" ] && /usr/bin/python3 -I -c "import json,sys; s=json.load(open(sys.argv[1])); sys.exit(0 if s['deny_names'] > 0 else 1)" "$W/default/log/merge/stats.json" 2>/dev/null \
  && ok "default: build/hints/merge-deny.txt snapshot read ($(grep -vc '^#' "$W/default/log/merge-deny.txt") names)" || bad "default: hints deny list not used"

# projects/merge-silent: T.H (namespace Q.H, `open A`) uses `V` = A.V; in a merged file with T.P1 (declares Q.V) the
# namespace-prefix match Q.V SHADOWS A.V silently -> T.S builds, but T.D (`Q.H.W = 1 := rfl`) fails even alone.
silent() { # name unsafe expect_rebuild(0|1)
  local n=$1; rm -rf "$W/$n"; mkdir -p "$W/$n"; cp -a "$H/projects/merge-silent" "$W/$n/proj"
  "$D/build/build.sh" "$W/$n/proj" "$WS" "$TC" --log "$W/$n/log" --threads 4 --preset B3 --unsafe "$2" > "$W/$n/fast.json" 2>&1
  grep -q '"status": "BUILT"' "$W/$n/fast.json" && ok "$n: toy build BUILT" || bad "$n: toy build: $(tail -1 "$W/$n/fast.json" | cut -c1-300)"
  if grep -q "rebuilding unmerged" "$W/$n/log/build.log" 2>/dev/null; then r=1; else r=0; fi
  [ "$r" = "$3" ] && ok "$n: unmerged rebuild = $r (expected $3)" || bad "$n: unmerged rebuild = $r (expected $3)"
}
silent silent-rules merge,skip-kernel-tc 0
silent silent-norules merge=--no-ambiguity-rule:--no-exact-leak-rule:--no-instance-leak-rule,skip-kernel-tc 1

# projects/merge-order: IMPORT ORDER. T.I1 / T.I2 declare equal-priority instances Foo Nat (1 / 2); in the original import
# order of Main (imports T.S) T.I1 comes after T.I2, so Main's `Foo.val = 1 := rfl` holds. The group {T.M, T.S} must list
# its external imports in the original walk order (T.I2, T.I1); the old member order (T.I1, T.I2) breaks Main downstream.
order() { # name unsafe expect_rebuild(0|1)
  local n=$1; rm -rf "$W/$n"; mkdir -p "$W/$n"; cp -a "$H/projects/merge-order" "$W/$n/proj"
  "$D/build/build.sh" "$W/$n/proj" "$WS" "$TC" --log "$W/$n/log" --threads 4 --preset B3 --unsafe "$2" > "$W/$n/fast.json" 2>&1
  grep -q '"status": "BUILT"' "$W/$n/fast.json" && ok "$n: toy build BUILT" || bad "$n: toy build: $(tail -1 "$W/$n/fast.json" | cut -c1-300)"
  /usr/bin/python3 -I -c "import json,sys; g=json.load(open(sys.argv[1])); sys.exit(0 if g == {'T.S': ['T.M', 'T.S']} else 1)" "$W/$n/log/merge/groups.json" \
    && ok "$n: merge groups {T.S: [T.M, T.S]}" || bad "$n: merge groups $(cat "$W/$n/log/merge/groups.json" 2>/dev/null)"
  if grep -q "rebuilding unmerged" "$W/$n/log/build.log" 2>/dev/null; then r=1; else r=0; fi
  [ "$r" = "$3" ] && ok "$n: unmerged rebuild = $r (expected $3)" || bad "$n: unmerged rebuild = $r (expected $3)"
}
order order merge,skip-kernel-tc 0
order order-legacy merge=--member-import-order,skip-kernel-tc 1

# projects/merge-late: merge=late - the build starts with Lake's plan at once, the merge planner runs concurrently and
# sched.py --merge-late swaps in the groups none of whose members was launched yet. T.Slow (heavy root, never merged)
# keeps the groups {T.A, T.S} and {T.M1, (T.M2,) T.F} waiting until the planner is done -> they are swapped in; with the
# rules disabled {T.M1, T.M2, T.F} fails merged ('ambiguous') -> split fallback -> BUILT.
late() { # name unsafe expected_splits_json
  local n=$1; rm -rf "$W/$n"; mkdir -p "$W/$n"; cp -a "$H/projects/merge-late" "$W/$n/proj"
  "$D/build/build.sh" "$W/$n/proj" "$WS" "$TC" --log "$W/$n/log" --threads 4 --preset B3 --unsafe "$2" > "$W/$n/fast.json" 2>&1
  grep -q '"status": "BUILT"' "$W/$n/fast.json" && ok "$n: toy build BUILT" || bad "$n: toy build: $(tail -1 "$W/$n/fast.json" | cut -c1-300)"
  /usr/bin/python3 -I - "$W/$n" "$3" <<'PY' || fail=1
import json, os, sys
W = sys.argv[1]; exp_s = json.loads(sys.argv[2]); n = os.path.basename(W); f = True
ev = [json.loads(l) for l in open(f'{W}/log/sched.out') if l.startswith('{')]
ml = [e for e in ev if e.get('event') == 'merge-late']
ok = len(ml) == 1 and ml[0]['applied'] >= 2 and ml[0]['absorbed'] >= 2
print(('PASS' if ok else 'FAIL') + f' {n}: merge-late swapped groups in {ml}'); f &= ok
splits = [e['module'] for e in ev if e.get('event') == 'split']
print(('PASS' if splits == exp_s else 'FAIL') + f' {n}: splits {splits}'); f &= splits == exp_s
a = os.path.exists(f'{W}/proj/.lake/build/lib/lean/T/A.olean')
print(('PASS' if not a else 'FAIL') + f' {n}: T.A built inside T.S (no T/A.olean)'); f &= not a
sys.exit(0 if f else 1)
PY
  diff -r -q "$H/projects/merge-late/src" "$W/$n/proj/src" > /dev/null && ok "$n: project sources untouched" || bad "$n: project sources changed"
}
late late merge=late,skip-kernel-tc '[]'
late late-split merge=late:--no-ambiguity-rule:--no-exact-leak-rule,skip-kernel-tc '["T.F"]'
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"
exit $fail
