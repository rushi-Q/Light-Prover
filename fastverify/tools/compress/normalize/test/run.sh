#!/bin/bash
# Regression test of tools/compress/normalize (incl. the NCS fix and the Lean 4 module-system support):
#   0-5. Core-Lean checks (dropempty, normalize IMP/OPT classes, dfsverify plain mode, apply_tree, chainmerge, OleanDiff, OleanMergeDiff)
#   6.   NCS safety check (`example` / `alias` prevent stripping `noncomputable section`)
#   7.   Lean 4 `module` / `public import` checks: dropempty on `module` file, IMP-C1 on `public import` vs plain `import`
#        (non-exported `import` does NOT subsume `public import`, while `public import` DOES subsume both), `dfsverify`
#        `mode module-system` (identical on valid reduction, exit 1 on `public import` -> `import` visibility downgrade),
#        root-layout `apply_tree.py`, and real Lean 4.33.1 `module` elaboration + `OleanDiff` (`SAME-MODULO-POSITIONS`).
set -u
T=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); N=$(dirname "$T")
ORIG_T=$LIGHT_LEAN/fastverify/tools/compress/normalize/test
[ -d "$T/proj" ] && PROJ_FIX="$T/proj" || PROJ_FIX="$ORIG_T/proj"
ORIG_N=$LIGHT_LEAN/fastverify/tools/compress/normalize
[ -d "$N/oleandiff" ] && OD_DIR="$N/oleandiff" || OD_DIR="$ORIG_N/oleandiff"
TC=${TC:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1}
W=$(mktemp -d "${TMPDIR:-/tmp}/normtest.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }; ko() { echo "FAIL $1"; fail=$((fail+1)); }
DV=$W/dfsverify; g++ -O2 -std=c++17 -pthread -o "$DV" "$N/dfsverify/dfsverify.cpp" || { echo "cannot build dfsverify"; exit 2; }

# 0. dropempty: T.E (only open/namespace, its namespace T is registered by T.A below it) is dropped, Main flattened
python3 -I "$N/dropempty.py" "$PROJ_FIX" "$W/t0" > "$W/de.json" || ko dropempty-run
[ "$(cat $W/t0/.dropempty.txt)" = "T.E" ] && grep -q '^import T.A$' "$W/t0/src/Main.lean" && ok "dropempty drops T.E, flattens Main" || ko "dropempty: $(cat $W/de.json)"
# 1. normalize: expected classes
python3 -I "$N/normalize.py" "$W/t0" --edits "$W/e.tsv" --classes imp,opt,optres --graph-out "$W/g" --packages /nonexistent > "$W/n.json" || ko normalize-run
got=$(cut -f1,2,3 "$W/e.tsv.classes.tsv" | tr '\t' ' ' | sort | tr '\n' ';')
exp="Main 3 IMP-C1;T.B 2 OPT-O1;T.C 1 IMP-C2;T.C 3 OPT-O2;T.C 5 OPT-O3;T.D 2 IMP-C1;"
[ "$got" = "$exp" ] && ok "normalize classes ($got)" || ko "normalize classes: got '$got' expected '$exp'"
# 2. dfsverify: identity on the result; an order change is detected
"$DV" "$W/g.old.txt" "$W/g.new.txt" "$W/g.roots.txt" 2 > "$W/dv.txt" && grep -q "different 0" "$W/dv.txt" && ok "dfsverify identical" || ko "dfsverify identical: $(cat $W/dv.txt)"
sed 's/^T.C T.A T.B$/T.C T.B/' "$W/g.old.txt" > "$W/g.bad1.txt"
"$DV" "$W/g.old.txt" "$W/g.bad1.txt" "$W/g.roots.txt" 2 > /dev/null && ok "dfsverify C2 removal identical" || ko "dfsverify C2 removal"
printf 'T.A\nT.B0\nT.Y2 T.A\nT.Z T.Y2 T.B0\n' > "$W/o3.txt"; printf 'T.A\nT.B0\nT.Y2 T.A\nT.Z T.B0 T.Y2\n' > "$W/n3.txt"; printf 'T.Z\n' > "$W/r3.txt"
"$DV" "$W/o3.txt" "$W/n3.txt" "$W/r3.txt" 1 > /dev/null; [ $? = 1 ] && ok "dfsverify detects an order change" || ko "dfsverify missed an order change"
# 3. apply + chain merge
python3 -I "$N/apply_tree.py" "$W/t0" "$W/t1" "$W/e.tsv" > /dev/null || ko apply
python3 -I "$N/chainmerge.py" "$W/t1" "$W/t2" --packages /nonexistent > "$W/cm.json" || ko chainmerge-run
m=$(sort "$W/t2/.chainmerge.tsv" | tr '\t' '>' | tr '\n' ';')
[ "$m" = "T.B>T.D;T.C>T.D;T.X>T.Y;" ] && ok "chainmerge groups ($m)" || ko "chainmerge groups: $m"
grep -q '^end$' "$W/t2/src/T/Y.lean" && ok "chainmerge closes the unclosed section of X" || ko "chainmerge scope closing"
# 4. elaboration evidence (core Lean only, our own test code)
build() {
  local s=$1 o=$2; shift 2; mkdir -p "$o"
  for m in "$@"; do local r=${m//.//}; mkdir -p "$o/$(dirname $r)"
    (cd "$s" && LEAN_PATH="$o" "$TC/bin/lean" -DautoImplicit=false "$r.lean" -o "$o/$r.olean" > "$o/$m.log" 2>&1) || { echo "build $m failed: $(head -3 $o/$m.log)"; return 1; }
  done; }
build "$PROJ_FIX/src" "$W/o0" T.A T.B T.C T.D T.X T.Y T.E Main && ok "build original" || ko "build original"
build "$W/t1/src" "$W/o1" T.A T.B T.C T.D T.X T.Y Main && ok "build normalized" || ko "build normalized"
build "$W/t2/src" "$W/o2" T.A T.D T.Y Main && ok "build merged" || ko "build merged"
for m in T.A T.B T.C T.D T.X T.Y Main; do r=${m//.//}
  v=$(LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$OD_DIR/OleanDiff.lean" "$W/o0/$r.olean" "$W/o1/$r.olean" "$W" 2>&1 | tail -1)
  case "$v" in SAME-MODULO-POSITIONS*) ok "olean $m: $v";; *) ko "olean $m: $v";; esac; done
v=$(LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$OD_DIR/OleanMergeDiff.lean" "$W/o2/T/D.olean" T.D "$W/o0/T/B.olean" T.B "$W/o0/T/C.olean" T.C "$W/o0/T/D.olean" T.D 2>&1 | tail -1)
case "$v" in SAME-MODULO-PRIVATE-RENAMING|ALPHA-EQUAL-MODULO-PRIVATE-RENAMING) ok "merged T.D: $v";; *) ko "merged T.D: $v";; esac
v=$(LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$OD_DIR/OleanMergeDiff.lean" "$W/o2/T/Y.olean" T.Y "$W/o0/T/X.olean" T.X "$W/o0/T/Y.olean" T.Y 2>&1 | tail -2 | tr '\n' ' ')
case "$v" in *"private 1"*ALPHA-EQUAL-MODULO-PRIVATE-RENAMING*) ok "merged T.Y (private renamed, hygienic names alpha): $v";; *) ko "merged T.Y: $v";; esac
# 5. OleanDiff detects a changed proof
mkdir -p "$W/s3/T" "$W/o3/T"; sed 's/T.c : T.a = 1 := T.a_eq/T.c : T.a = 1 := by rfl/' "$PROJ_FIX/src/T/C.lean" > "$W/s3/T/C.lean"
(cd "$W/s3" && LEAN_PATH="$W/o0" "$TC/bin/lean" -DautoImplicit=false T/C.lean -o "$W/o3/T/C.olean" > /dev/null 2>&1)
v=$(LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$OD_DIR/OleanDiff.lean" "$W/o0/T/C.olean" "$W/o3/T/C.olean" "$W" 2>&1 | tail -1)
case "$v" in DIFFERENT*) ok "OleanDiff detects a proof change";; *) ko "OleanDiff missed a proof change: $v";; esac

# 6. D17 NCS safety check: `example` prevents removing `noncomputable section`
mkdir -p "$W/ncs/src"
cat > "$W/ncs/lakefile.toml" <<'EOF'
name = "ncs"
srcDir = "src"
[[lean_lib]]
name = "Ex"
EOF
cat > "$W/ncs/src/Ex.lean" <<'EOF'
noncomputable section
example : Nat := 0
end
EOF
python3 -I "$N/normalize.py" "$W/ncs" --edits "$W/ncs.tsv" --classes ncs --packages /nonexistent > /dev/null
[ ! -s "$W/ncs.tsv" ] && ok "NCS keeps noncomputable section when example is present" || ko "NCS stripped noncomputable section with example"

# 7. D20 Lean 4 `module` / `public import` end-to-end test (root layout, no src/ subdir, with [[lean_exe]] srcDir="scripts")
mkdir -p "$W/mp/M"
cat > "$W/mp/lakefile.toml" <<'EOF'
name = "mp"
defaultTargets = ["M"]
[[lean_lib]]
name = "M"
[[lean_exe]]
name = "aux"
srcDir = "scripts"
root = "Aux"
EOF
cat > "$W/mp/M/A.lean" <<'EOF'
module

@[expose] public def aVal : Nat := 7
EOF
cat > "$W/mp/M/B.lean" <<'EOF'
module

public import M.A

public theorem bThm : aVal = 7 := rfl
EOF
cat > "$W/mp/M/Priv.lean" <<'EOF'
module

import M.A

public def privWrap : Nat := 1
EOF
cat > "$W/mp/M/EmptyMod.lean" <<'EOF'
module

public import M.B
EOF
cat > "$W/mp/M.lean" <<'EOF'
module

public import M.EmptyMod
public import M.A
import M.Priv
public import M.A
EOF
# Note: in M.lean:
# - M.EmptyMod is dropped -> flattened to `public import M.B` (which `public import`s M.A -> so BOTH later `public import M.A` lines are IMP-C1 redundant!)
# - What if M2.lean has `import M.B` (non-public!) followed by `public import M.A`? Non-public `import M.B` does NOT export M.A publicly, so `public import M.A` MUST be kept!
cat > "$W/mp/M/KeepPub.lean" <<'EOF'
module

import M.B
public import M.A

public theorem kp : aVal = 7 := rfl
EOF

python3 -I "$N/dropempty.py" "$W/mp" "$W/mp0" --protect M > "$W/mp_de.json" || ko "modsys dropempty"
[ "$(cat $W/mp0/.dropempty.txt)" = "M.EmptyMod" ] && head -n 1 "$W/mp0/M.lean" | grep -qx 'module' && ok "modsys dropempty drops EmptyMod & preserves leading module header" || ko "modsys dropempty output"

python3 -I "$N/normalize.py" "$W/mp0" --edits "$W/mp_e.tsv" --classes imp,opt --graph-out "$W/mpg" --packages /nonexistent > "$W/mp_n.json" || ko "modsys normalize"
grep -q '^M	' "$W/mp_e.tsv" && ! grep -q '^M\.KeepPub	' "$W/mp_e.tsv" && ok "modsys IMP-C1 drops redundant public import in M, keeps public import after plain import in M.KeepPub" || ko "modsys IMP-C1 visibility rule: $(cat $W/mp_e.tsv)"

"$DV" "$W/mpg.old.txt" "$W/mpg.new.txt" "$W/mpg.roots.txt" 2 > "$W/mp_dv.txt" && grep -q "mode module-system" "$W/mp_dv.txt" && grep -q "different 0" "$W/mp_dv.txt" && ok "modsys dfsverify identical" || ko "modsys dfsverify: $(cat $W/mp_dv.txt)"
# Verify dfsverify catches an invalid downgrade (`public import M.A` dropped after plain `import M.B` in M.KeepPub)
sed 's/^M.KeepPub@mod M.B pub:M.A$/M.KeepPub@mod M.B/' "$W/mpg.new.txt" > "$W/mpg.bad.txt"
"$DV" "$W/mpg.old.txt" "$W/mpg.bad.txt" "$W/mpg.roots.txt" 1 > /dev/null; [ $? = 1 ] && ok "modsys dfsverify rejects visibility downgrade (public import dropped after plain import)" || ko "modsys dfsverify missed visibility downgrade"

python3 -I "$N/apply_tree.py" "$W/mp0" "$W/mp1" "$W/mp_e.tsv" > /dev/null && ok "modsys apply_tree on root-layout project" || ko "modsys apply_tree"

# Build both mp0 and mp1 with Lean 4.33.1 (writes .olean, .olean.server, .olean.private) and check OleanDiff!
build "$W/mp0" "$W/mpo0" M.A M.B M.Priv M.KeepPub M && build "$W/mp1" "$W/mpo1" M.A M.B M.Priv M.KeepPub M && ok "modsys Lean 4.33.1 build before & after" || ko "modsys Lean 4.33.1 build"
v=$(LEAN_PATH="$TC/lib/lean" "$TC/bin/lean" --run "$OD_DIR/OleanDiff.lean" "$W/mpo0/M.olean" "$W/mpo1/M.olean" "$W" 2>&1 | tail -1)
case "$v" in SAME-MODULO-POSITIONS*) ok "modsys OleanDiff M: $v";; *) ko "modsys OleanDiff M: $v";; esac


# 8. D19 OPT-O2 safety check: `set_option maxHeartbeats 0` (and `0 in`) means UNLIMITED in Lean 4, NEVER delete!
mkdir -p "$W/hb0/src"
cat > "$W/hb0/lakefile.toml" <<'EOF'
name = "hb0"
srcDir = "src"
[leanOptions]
maxHeartbeats = 4000000
synthInstance.maxHeartbeats = 400000
[[lean_lib]]
name = "Hb"
EOF
cat > "$W/hb0/src/Hb.lean" <<'EOF'
set_option maxHeartbeats 0 in
theorem t1 : True := trivial
set_option synthInstance.maxHeartbeats 0 in
theorem t2 : True := trivial
set_option maxHeartbeats 200000
set_option maxHeartbeats 0
set_option maxHeartbeats 4000000
theorem ok : True := trivial
EOF
python3 -I "$N/normalize.py" "$W/hb0" --edits "$W/hb0.tsv" --classes opt,optres --packages /nonexistent > /dev/null
got_hb=$(cut -f1,2,3 "$W/hb0.tsv.classes.tsv" | tr '\t' ' ' | sort | tr '\n' ';')
[ "$got_hb" = "Hb 5 OPT-O2;Hb 7 OPT-O2;" ] && ok "OPT-O2 preserves maxHeartbeats 0 (unlimited) while stripping finite tighter limits" || ko "OPT-O2 maxHeartbeats 0: got '$got_hb' expected 'Hb 5 OPT-O2;Hb 7 OPT-O2;'"


# 9. D19 OPT-O1 scope-tracking check: single-line `namespace A ... end A` and `end A.B` must NOT leak set_option into next section!
mkdir -p "$W/sc/src"
cat > "$W/sc/lakefile.toml" <<'EOF'
name = "sc"
srcDir = "src"
[[lean_lib]]
name = "Sc"
EOF
cat > "$W/sc/src/Sc.lean" <<'EOF'
section S1
set_option backward.isDefEq.respectTransparency false
namespace A theorem t1 : True := trivial end A
end S1
section S2
set_option backward.isDefEq.respectTransparency false
namespace P
namespace Q
end P.Q
end S2
section S3
set_option backward.isDefEq.respectTransparency false
theorem t2 : True := trivial
end S3
EOF
python3 -I "$N/normalize.py" "$W/sc" --edits "$W/sc.tsv" --classes opt --packages /nonexistent > /dev/null
[ ! -s "$W/sc.tsv" ] && ok "OPT-O1 scope tracking handles single-line namespace..end and multi-component end A.B" || ko "OPT-O1 leaked across scopes: $(cat $W/sc.tsv)"

# 10. D20 chainmerge --same-dir topic-layout preservation check
mkdir -p "$W/sd/src/Top1" "$W/sd/src/Top2"
cat > "$W/sd/lakefile.toml" <<'EOF'
name = "sd"
srcDir = "src"
[[lean_lib]]
name = "Top1"
[[lean_lib]]
name = "Top2"
EOF
cat > "$W/sd/src/Top1/A.lean" <<'EOF'
def a1 : Nat := 1
EOF
cat > "$W/sd/src/Top1/B.lean" <<'EOF'
import Top1.A
def b1 : Nat := a1
EOF
cat > "$W/sd/src/Top2/C.lean" <<'EOF'
import Top1.B
def c2 : Nat := b1
EOF
python3 -I "$N/chainmerge.py" "$W/sd" "$W/sd_all" --plan-only --packages /nonexistent > "$W/sd_all.json"
python3 -I "$N/chainmerge.py" "$W/sd" "$W/sd_dir" --same-dir --plan-only --packages /nonexistent > "$W/sd_dir.json"
grep -q '"members_removed": 2' "$W/sd_all.json" && grep -q '"members_removed": 1' "$W/sd_dir.json" && ok "chainmerge --same-dir merges Top1.A->Top1.B while preserving Top1/Top2 boundary" || ko "chainmerge --same-dir: all=$(cat $W/sd_all.json) dir=$(cat $W/sd_dir.json)"

# ---------- 8. chainmerge --costs / --max-cost greedy chain splitting + topic_coalesce ----------
mkdir -p "$W/cmcost/src/T"
cat > "$W/cmcost/lakefile.toml" <<'EOF'
name = "cmcost"
[[lean_lib]]
name = "Main"
srcDir = "src"
roots = ["Main"]
EOF
cat > "$W/cmcost/src/T/A.lean" <<'EOF'
def vA : Nat := 1
EOF
cat > "$W/cmcost/src/T/B.lean" <<'EOF'
import T.A
def vB : Nat := vA + 2
EOF
cat > "$W/cmcost/src/T/C.lean" <<'EOF'
import T.B
def vC : Nat := vB + 3
EOF
cat > "$W/cmcost/src/T/D.lean" <<'EOF'
import T.C
def vD : Nat := vC + 4
EOF
cat > "$W/cmcost/src/Main.lean" <<'EOF'
import T.D
theorem main_ok : vD = 10 := rfl
EOF
printf '{"T.A":12.0,"T.B":14.0,"T.C":15.0,"T.D":10.0,"Main":1.0}\n' | gzip > "$W/costs.json.gz"
python3 -I "$N/chainmerge.py" "$W/cmcost" "$W/cmcost_out" --same-dir --costs "$W/costs.json.gz" --max-cost 30.0 --packages /nonexistent > "$W/cmcost.json"
grep -q '"groups_merged": 2' "$W/cmcost.json" && grep -q '"members_removed": 2' "$W/cmcost.json" && [ -f "$W/cmcost_out/src/T/B.lean" ] && [ -f "$W/cmcost_out/src/T/D.lean" ] && [ ! -f "$W/cmcost_out/src/T/A.lean" ] && [ ! -f "$W/cmcost_out/src/T/C.lean" ] \
  && ok "chainmerge --costs/--max-cost splits [12,14,15,10]s chain cleanly into [A->B] and [C->D]" || ko "chainmerge --max-cost: $(cat $W/cmcost.json)"

mkdir -p "$W/tcoal/src/Dir1" "$W/tcoal/src/Dir2"
echo "leanprover/lean4:v4.33.1" > "$W/tcoal/lean-toolchain"
cat > "$W/tcoal/lakefile.toml" <<'EOF'
name = "tcoal"
defaultTargets = ["Main"]
[[lean_lib]]
name = "Main"
srcDir = "src"
roots = ["Main"]
EOF
cat > "$W/tcoal/src/Base.lean" <<'EOF'
def baseVal : Nat := 5
EOF
cat > "$W/tcoal/src/Dir1/L1.lean" <<'EOF'
import Base
private def p1 : Nat := 1
def leaf1 : Nat := baseVal + p1
EOF
cat > "$W/tcoal/src/Dir1/L2.lean" <<'EOF'
import Base
private def p2 : Nat := 2
def leaf2 : Nat := baseVal + p2
EOF
cat > "$W/tcoal/src/Dir1/L3Clash.lean" <<'EOF'
import Base
private def p1 : Nat := 9
def leaf3 : Nat := baseVal + p1
EOF
cat > "$W/tcoal/src/Dir2/Other.lean" <<'EOF'
import Base
def otherLeaf : Nat := baseVal + 10
EOF
cat > "$W/tcoal/src/Main.lean" <<'EOF'
import Dir1.L1
import Dir1.L2
import Dir1.L3Clash
import Dir2.Other
theorem coal_thm : leaf1 + leaf2 + leaf3 + otherLeaf = 42 := rfl
EOF
python3 -I "$N/topic_coalesce.py" "$W/tcoal" "$W/tcoal_out" --packages /nonexistent > "$W/tcoal.json"
grep -q '"members_removed": 1' "$W/tcoal.json" && grep -q '"private_clash_splits": 1' "$W/tcoal.json" && [ -f "$W/tcoal_out/src/Dir2/Other.lean" ] \
  && ok "topic_coalesce coalesces same-dir identical-import leaves while splitting private clashes & cross-dir" || ko "topic_coalesce: $(cat $W/tcoal.json)"
python3 -I "$N/topic_coalesce.py" "$W/tcoal" "$W/tcoal_si" --same-importers --packages /nonexistent > "$W/tcoal_si.json"
grep -q '"members_removed": 1' "$W/tcoal_si.json" && grep -q '"private_clash_splits": 1' "$W/tcoal_si.json" \
  && ok "topic_coalesce --same-importers (G1*) preserves exact importer sets & splits private/public short-name clashes" || ko "topic_coalesce --same-importers: $(cat $W/tcoal_si.json)"
build "$W/tcoal_out/src" "$W/otcoal" Base Dir1.L2 Dir1.L3Clash Dir2.Other Main \
  && ok "topic_coalesce output compiles cleanly under lean" || ko "topic_coalesce lean build failed"

echo "normalize test: $pass passed, $fail failed"; [ $fail = 0 ]
