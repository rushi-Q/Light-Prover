#!/bin/bash
# Regression tests for the 4 bugs fixed in fastverify/tools/compress/dedup/:
#   B1: dangling `attribute [...] in` / multi-line `variable ... in` above deleted redirected decl
#   B2a: same-module short-name reference (invisible to kernel used_constants) blocks unsafe deletion
#   B2b: named-argument call (`old (n := ...)`) blocks unsafe redirect
#   B3: `_root_.OLD` prefixed references are rewritten cleanly by apply_edits.py
#   B4: IMPORT-class redirected users receive direct `import tmod`
set -euo pipefail
T=$(cd "$(dirname "$0")/.." && pwd)
W=$(mktemp -d /tmp/dedup-d19-reg.XXXXXX); trap 'rm -rf "$W"' EXIT
TC=${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.33.1; export PATH=$TC/bin:$PATH

# 1. B3 regression: apply_edits.py rewrites BOTH plain `A.old` and `_root_.A.old`
mkdir -p "$W/proj/M"
cat > "$W/proj/M/U.lean" <<'EOF'
import M.T
example := A.old
example := _root_.A.old
example := fooA.old
EOF
printf 'M.U\t0\t0\tsubst\tP03\tA.old B.new\n' > "$W/e_b3.tsv"
python3 "$T/apply_edits.py" "$W/proj" "$W/out_b3" "$W/e_b3.tsv" --srcdir . --copy > "$W/b3.json"
grep -q '^example := B.new$' "$W/out_b3/M/U.lean" || { cat "$W/out_b3/M/U.lean"; echo "FAIL B3 plain"; exit 1; }
grep -q '^example := _root_.B.new$' "$W/out_b3/M/U.lean" || { cat "$W/out_b3/M/U.lean"; echo "FAIL B3 _root_.OLD"; exit 1; }
grep -q '^example := fooA.old$' "$W/out_b3/M/U.lean" || { cat "$W/out_b3/M/U.lean"; echo "FAIL B3 identifier prefix corrupted"; exit 1; }

# 2. B1 regression: dangling `attribute ... in` and `variable ... in` removed when redirected decl is deleted
mkdir -p "$W/proj2/M"
cat > "$W/proj2/M/A.lean" <<'EOF'
namespace NA
theorem target : True := trivial
end NA
EOF
cat > "$W/proj2/M/B.lean" <<'EOF'
import M.A
namespace NB
attribute [local simp] Nat.add_zero in
theorem dup1 : True := by
  have h : True := trivial
  exact h
variable (x : Nat)
  in
theorem dup2 : True := by
  have h : True := trivial
  exact h
end NB
EOF
# Construct minimal plan (header + 13 cols: gi act name mod tgt tmod sl pl incl indeg priv l1 l2) + redirect tables
cat > "$W/plan2.tsv" <<'EOF'
gi	act	name	mod	tgt	tmod	sl	pl	incl	indeg	priv	l1	l2
1	ALIAS	NB.dup1	M.B	NA.target	M.A	1	3	1	0	0	4	6
2	ALIAS	NB.dup2	M.B	NA.target	M.A	1	3	1	0	0	9	11
EOF
cat > "$W/redir2.tsv" <<'EOF'
NB.dup1	M.B	NA.target		OK
NB.dup2	M.B	NA.target		OK
EOF
python3 "$T/dedup_edits.py" "$W/plan2.tsv" "$W/proj2" "$W/e_b1.tsv" --actions ALIAS --mode alias --redirect "$W/redir2.tsv" --protect dummy_target > "$W/b1.json"
python3 "$T/apply_edits.py" "$W/proj2" "$W/out_b1" "$W/e_b1.tsv" --srcdir . --copy > "$W/b1_ap.json"
if grep -qE 'attribute \[local simp\]|variable \(x : Nat\)' "$W/out_b1/M/B.lean"; then
  cat "$W/out_b1/M/B.lean"
  echo "FAIL B1 dangling modifier..in remained"
  exit 1
fi

# 3. B2a + B2b regression: redirect_check.py rejects same-mod short ref and named-arg call
mkdir -p "$W/proj3/M" "$W/scan3"
cat > "$W/proj3/M/A.lean" <<'EOF'
namespace NA
theorem t1 (m : Nat) : m = m := rfl
theorem t2 (m : Nat) : m = m := rfl
end NA
EOF
cat > "$W/proj3/M/B.lean" <<'EOF'
import M.A
namespace NB
theorem d_short (n : Nat) : n = n := rfl
theorem u_short : 0 = 0 := d_short 0
theorem d_named (n : Nat) : n = n := rfl
theorem u_named : 0 = 0 := NB.d_named (n := 0)
end NB
EOF
# scan3/c0.tsv: K mod kind name p4 p5 p6 p7 start end used
cat > "$W/scan3/c0.tsv" <<'EOF'
K	M.B	t	NB.d_short	0	0	0	0	3	3	
K	M.B	t	NB.u_short	0	0	0	0	4	4	
K	M.B	t	NB.d_named	0	0	0	0	5	5	
K	M.B	t	NB.u_named	0	0	0	0	6	6	NB.d_named
EOF
cat > "$W/plan3.tsv" <<'EOF'
gi	act	name	mod	tgt	tmod	sl	pl	incl	indeg	priv	l1	l2	c13	c14	binfo_eq
1	ALIAS	NB.d_short	M.B	NA.t1	M.A	1	1	1	0	0	3	3	0	0	1
2	ALIAS	NB.d_named	M.B	NA.t2	M.A	1	1	1	0	0	5	5	0	0	1
EOF
python3 "$T/redirect_check.py" "$W/scan3" "$W/plan3.tsv" "$W/proj3" "$W/redir3.tsv" > "$W/b2.json"
grep -q $'NB.d_short\t.*\tsame-mod-short-ref' "$W/redir3.tsv" || { cat "$W/redir3.tsv"; echo "FAIL B2a same-mod-short-ref not caught"; exit 1; }
grep -q $'NB.d_named\t.*\tnamed-arg-call' "$W/redir3.tsv" || { cat "$W/redir3.tsv"; echo "FAIL B2b named-arg-call not caught"; exit 1; }

# 4. B4 regression: redirected IMPORT user receives direct `import tmod`
mkdir -p "$W/proj4/M"
cat > "$W/proj4/M/T.lean" <<'EOF'
namespace NT
theorem tgt : True := trivial
end NT
EOF
cat > "$W/proj4/M/D.lean" <<'EOF'
namespace ND
theorem dup : True := trivial
end ND
EOF
cat > "$W/proj4/M/U.lean" <<'EOF'
import M.D
example : True := ND.dup
EOF
cat > "$W/plan4.tsv" <<'EOF'
gi	act	name	mod	tgt	tmod	sl	pl	incl	indeg	priv	l1	l2
1	IMPORT	ND.dup	M.D	NT.tgt	M.T	1	3	1	1	0	2	4
EOF
cat > "$W/proj4/M/D.lean" <<'EOF'
namespace ND
theorem dup : True := by
  have h : True := trivial
  exact h
end ND
EOF
cat > "$W/redir4.tsv" <<'EOF'
ND.dup	M.D	NT.tgt	M.U:2	OK
EOF
python3 "$T/dedup_edits.py" "$W/plan4.tsv" "$W/proj4" "$W/e_b4.tsv" --actions IMPORT --mode alias --redirect "$W/redir4.tsv" --protect dummy_target > "$W/b4.json"
python3 "$T/apply_edits.py" "$W/proj4" "$W/out_b4" "$W/e_b4.tsv" --srcdir . --copy > "$W/b4_ap.json"
grep -q '^import M.T$' "$W/out_b4/M/U.lean" || { cat "$W/out_b4/M/U.lean"; echo "FAIL B4 direct import M.T missing on redirected user"; exit 1; }
grep -q 'NT.tgt' "$W/out_b4/M/U.lean" || { cat "$W/out_b4/M/U.lean"; echo "FAIL B4 subst missing"; exit 1; }

echo "PASS (dedup D19 regressions: B1 modifier..in, B2a same-mod-short-ref, B2b named-arg-call, B3 _root_.OLD, B4 direct import tmod)"
