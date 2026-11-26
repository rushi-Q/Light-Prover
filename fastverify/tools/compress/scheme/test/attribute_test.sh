#!/bin/bash
# tests for attribute.py (no Lean, < 1 s): failure -> owner attribution on a synthetic 3-module train
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd); W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
pass=0; fail=0; ok() { echo "PASS $1"; pass=$((pass+1)); }; ko() { echo "FAIL $1: $2"; fail=$((fail+1)); }
mkdir -p "$W/m" "$W/src/A"
printf 'theorem helper : True := trivial\ntheorem used : True := helper\n' > "$W/src/A/Def.lean"
printf 'theorem k : True := A.helper\n' > "$W/src/A/Use.lean"
printf 'theorem z : True := trivial\n' > "$W/src/A/Mrg.lean"
printf 'theorem w : True := trivial\n' > "$W/src/A/Mem.lean"
printf 'A.Def\t1\t1\ttheorem\t0\t1\tA.helper\nA.Def\t2\t2\ttheorem\t1\t0\tA.used\n' > "$W/decls.tsv"
printf 'P01\tP01.tsv\nP03-dedup\tP03.tsv\nP07-stmtfmt\tP07.tsv\n' > "$W/m/manifest.tsv"
printf 'A.Def\t1\t1\tdelete\tP01\t\n' > "$W/m/P01.tsv"                                 # P01 removes A.helper
printf 'A.Use2\t0\t0\tsubst\tP03-dedup\tA.old A.gone\nA.Mrg\t1\t1\treplace\tP03-dedup\talias dupname := z\n' > "$W/m/P03.tsv"
printf 'A.Mrg\t1\t1\treplace\tP07-stmtfmt\ttheorem z :\\n    True := trivial\n' > "$W/m/P07.tsv"
printf 'A.Mem\tA.Mrg\n' > "$W/cm.tsv"
printf 'P06\tP06.tsv\n' >> "$W/m/manifest.tsv"; printf 'B.Y\t3\t4\treplace\tP06\tby abel\n' > "$W/m/P06.tsv"; printf 'B.X\t1\t1\treplace\tP07-stmtfmt\ttheorem x : True :=\\n  trivial\n' >> "$W/m/P07.tsv"
printf 'D18-docs\tDOC.tsv\n' >> "$W/m/manifest.tsv"; printf 'E.Doc\t3\t2\tinsert_before\tD18-docs\t/-- doc -/\n' > "$W/m/DOC.tsv"; printf 'E.Doc\t3\t4\tdelete\tP01\t\n' >> "$W/m/P01.tsv"
printf 'D18-rename\tREN.tsv\n' >> "$W/m/manifest.tsv"; printf 'A.Ren\t0\t0\tsubst\tD18-rename\tA.used_alt A.used\n' > "$W/m/REN.tsv"
printf 'A.Use\tUnknown constant `X`\tA.helper\t1\ttheorem\tk\tUnknown constant `A.helper`\n' > "$W/f.tsv"
printf 'A.Use2\tUnknown identifier `X`\tA.gone\t1\ttheorem\tq\tUnknown identifier `A.gone`\n' >> "$W/f.tsv"
printf 'A.Mrg\ta non-private declaration `X` has already been declared\tdupname\t1\talias\tdupname\tdup\n' >> "$W/f.tsv"
printf 'A.Mem\tfailed to compile definition, consider marking it as '"'"'noncomputable'"'"' because\t\t1\tdef\tw\tx\n' >> "$W/f.tsv"
printf 'A.Ren\tfail to show termination for\t\t1\tdef\tf\tx\n' >> "$W/f.tsv"
printf 'E.Doc\tunexpected end of input; expected X\t\t5\t-\t-\tunexpected end of input\n' >> "$W/f.tsv"
printf 'C.Use\timport B.X failed\t\t1\t-\t-\timport B.X failed, environment already contains '"'"'Q.lemma._abel_1_5'"'"' from B.Y\n' >> "$W/f.tsv"
python3 -I "$H/attribute.py" "$W/m" "$W/f.tsv" "$W/out" --decls "$W/decls.tsv" --src "$W/src" --chainmerge "$W/cm.tsv" > "$W/log" 2>&1 || ko run "$(cat "$W/log")"
r() { awk -F'\t' -v m="$1" '$1==m {print $4}' "$W/out/report.tsv"; }
[ "$(r A.Use)" = "P01@A.Def" ] && ok removed-and-used || ko removed-and-used "$(r A.Use)"
[ "$(r A.Use2)" = "P03-dedup@A.Use2" ] && ok introduced-by-subst || ko introduced-by-subst "$(r A.Use2)"
[ "$(r A.Mrg)" = "P03-dedup@A.Mrg" ] && ok duplicate-introduced || ko duplicate-introduced "$(r A.Mrg)"
[ "$(r A.Mem)" = "pipeline:normalize:ncs" ] && ok noncomputable-pipeline || ko noncomputable-pipeline "$(r A.Mem)"
[ "$(r A.Ren)" = "D18-rename@A.Ren" ] && grep -q "the new short name used also names another project declaration" "$W/out/report.tsv" && ok rename-shadow-hazard || ko rename-shadow-hazard "$(r A.Ren)"
[ "$(r C.Use)" = "P06@B.Y" ] && ok import-clash-auxiliary || ko import-clash-auxiliary "$(r C.Use)"
[ "$(r E.Doc)" = "D18-docs@E.Doc" ] && ok insert-anchored-in-deleted-code || ko insert-anchored-in-deleted-code "$(r E.Doc)"
grep -qx "A.Def" "$W/out/deny/P01.txt" && grep -qx "A.Mrg" "$W/out/deny/P03-dedup.txt" && ok deny-files || ko deny-files "$(ls "$W/out/deny")"
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]
