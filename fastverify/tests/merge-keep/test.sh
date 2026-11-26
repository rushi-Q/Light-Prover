#!/bin/bash
# tests/merge-keep/test.sh [WORK] : two availability bugs (false REJECTED of valid projects) of the sound preset's
# untrusted B3 item `merge`; NOT soundness.
#  F1: `merge` merged the comparator's SOLUTION MODULE into its importer's group when some project module imports it
#    (cedar-spec e7e33626, TOML port: Cedar.Thm is imported by the lib root Cedar): a group writes only its sink's .olean,
#    so <solution_module>.olean never existed, the export failed -> REJECTED (official: ACCEPTED). 3 repros.
#  F2: a merged member's private / hygienic / aux-lemma names take the SINK's module name; when the challenge shares
#    definition modules with the project (code formalizations), compareAt compares such a constant and rejects a valid
#    project (SampCert e85bd645: SLang.probWhileCut.eq_def refers to _private.SampCert.Foundations.While.0...splitter;
#    While was merged into Foundations.Basic's group -> 'Const does not match'; official, fast-exact, sound --build B0:
#    ACCEPTED). RH unaffected (no RH project module occurs in its challenge export; solution module has no importer).
# Fix: bin/fastverify passes `--keep <solution_module>` and `--keep-file` (build/mergekeep.py: modules occurring in the
#   challenge export's declaration names as _private.M.0 / _@.M._hyg / M._auxLemma) to mergeplan.py; a kept module never
#   joins an importer's group (it may still be a sink).
# Toys (build/test/projects/merge layout: T.N1 merges into T.S2's group by default):
#   F1: solution_module = T.N1 (imported by T.S2);  F2: T.N1 gets a private def used by N.two, the challenge restates
#   S2.s2 : two = 2 over a copy of T.N1, solution_module = T.S2 (the sink).
# Rows: per toy the sound preset ACCEPTED + T.N1 not merged into an importer group; F2: merge-keep.txt lists T.N1;
#   control rows: build.sh with plain `merge` still merges T.N1 (the toys exercise the rule), merge=--keep:T.N1 does not.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); D=$(cd "$H/../.." && pwd)
W=${1:-/tmp/fv-a02merge-$$}; rm -rf "$W"; mkdir -p "$W"
TC=${TC:-$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1]))["lean_toolchains"]; print(next(v["prefix"] for v in c.values() if v["prefix"].endswith("v4.33.1")))' "$D/config/components.json" 2>/dev/null)}
[ -n "$TC" ] && [ -d "$TC" ] || TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
fail=0; ok() { echo "PASS $1"; }; bad() { echo "FAIL $1"; fail=1; }
mkdir -p "$W/ws"
merged() { python3 -I -c 'import json,sys; g=json.load(open(sys.argv[1])); print(int(any("T.N1" in m and s!="T.N1" for s,m in g.items())))' "$1" 2>/dev/null || echo X; }
# ---- F1: solution module imported by another module
cp -a "$D/build/test/projects/merge" "$W/f1proj"
mkdir -p "$W/f1chal/T"; cp -a "$H/f1-challenge/." "$W/f1chal/"; cp "$D/build/test/projects/merge/src/T/Base.lean" "$W/f1chal/T/"
env -i HOME="$HOME" PATH=/usr/bin:/bin "$D/bin/fastverify" "$W/f1proj" "$W/f1chal" "$W/f1out" --preset sound --threads 4 \
  --packages "$W/ws" > "$W/f1.log" 2>&1; rc=$?
[ $rc = 0 ] && ok "F1: sound preset ACCEPTED (exit 0)" || bad "F1: sound preset exit $rc: $(grep -m1 'verdict' "$W/f1.log" | cut -c1-300)"
m=$(merged "$W/f1out/log/build-fast/merge/groups.json"); [ "$m" = 0 ] && ok "F1: solution module T.N1 not merged into an importer group" || bad "F1: T.N1 merged=$m"
# ---- F2: private name of a merged member in the challenge's comparison closure
cp -a "$H/f2-proj" "$W/f2proj"; cp -a "$H/f2-challenge" "$W/f2chal"
env -i HOME="$HOME" PATH=/usr/bin:/bin "$D/bin/fastverify" "$W/f2proj" "$W/f2chal" "$W/f2out" --preset sound --threads 4 \
  --packages "$W/ws" > "$W/f2.log" 2>&1; rc=$?
[ $rc = 0 ] && ok "F2: sound preset ACCEPTED (exit 0)" || bad "F2: sound preset exit $rc: $(grep -m1 'verdict' "$W/f2.log" | cut -c1-300)"
m=$(merged "$W/f2out/log/build-fast/merge/groups.json"); [ "$m" = 0 ] && ok "F2: T.N1 (private name in the challenge export) not merged" || bad "F2: T.N1 merged=$m"
grep -qx T.N1 "$W/f2out/log/merge-keep.txt" 2>/dev/null && ok "F2: mergekeep.py lists T.N1 (from _private.T.N1.0.N.one')" || bad "F2: merge-keep.txt: $(tr '\n' ' ' < "$W/f2out/log/merge-keep.txt" 2>/dev/null)"
# ---- control: the planner rule itself (build.sh, B3 merge, without / with --keep)
for v in plain keep; do
  u=merge,skip-kernel-tc; [ $v = keep ] && u=merge=--keep:T.N1,skip-kernel-tc
  rm -rf "$W/b-$v"; mkdir -p "$W/b-$v"; cp -a "$H/f2-proj" "$W/b-$v/proj"
  "$D/build/build.sh" "$W/b-$v/proj" "$W/ws" "$TC" --log "$W/b-$v/log" --threads 4 --preset B3 --unsafe "$u" > "$W/b-$v/fast.json" 2>&1
  m=$(merged "$W/b-$v/log/merge/groups.json"); o=$([ -f "$W/b-$v/proj/.lake/build/lib/lean/T/N1.olean" ] && echo 1 || echo 0)
  if [ $v = plain ]; then [ "$m" = 1 ] && [ $o = 0 ] && ok "control: plain merge merges T.N1 (no T/N1.olean)" || bad "control: merged=$m olean=$o"
  else [ "$m" = 0 ] && [ $o = 1 ] && ok "control: merge=--keep:T.N1 keeps T.N1 a singleton (T/N1.olean written)" || bad "keep: merged=$m olean=$o"; fi
done
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"
exit $fail
