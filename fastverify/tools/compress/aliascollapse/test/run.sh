#!/bin/bash
# Regression test of the FLT-layout transformations: collide.py, collapse.py (plain / --unify), attrhide.py
# (check / hide) on a tiny core-only fixture in the AI-FLT layout (cards Theorems/Thm_X, proofs P2M/Sol/S_X, Definitions).
# Every produced tree is elaborated module by module with the official lean 4.33.1 (core only, a few seconds) in bwrap
# without network. Prints PASS/FAIL rows and RESULT; exit 0 iff all pass.
set -u
H=$(cd "$(dirname "$0")/.." && pwd); C=$(cd "$H/.." && pwd)
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
W=$(mktemp -d /tmp/p08-collapse-test.XXXX); trap 'rm -rf "$W"' EXIT
fails=0
pass() { echo "PASS $*"; }
fail() { echo "FAIL $*"; fails=$((fails + 1)); }
# compile TREE: every module in topological order (imports first), olean output in TREE.out
compile() {
  local t=$1 o=$1.out; rm -rf "$o"; mkdir -p "$o"
  python3 -I - "$t" > "$W/order" <<'PY'
import os, sys
t = sys.argv[1]; mods = {}
for d, _, fs in os.walk(t):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f); m = os.path.relpath(p, t)[:-5].replace('/', '.')
            mods[m] = [l.split()[1] for l in open(p) if l.startswith('import ')]
seen, out = set(), []
def visit(m):
    if m in seen or m not in mods: return
    seen.add(m)
    for i in mods[m]: visit(i)
    out.append(m)
for m in sorted(mods): visit(m)
print('\n'.join(out))
PY
  while read -r m; do
    local f=${m//.//}
    mkdir -p "$o/$(dirname "$f")"
    env -i PATH=/usr/bin:/bin bwrap --ro-bind / / --tmpfs /tmp --bind "$t" "$t" --bind "$o" "$o" --unshare-net --die-with-parent \
      --chdir "$t" --dev /dev --proc /proc --setenv LEAN_PATH "$o" "$TC/bin/lean" "$f.lean" -o "$o/$f.olean" > "$W/lean.log" 2>&1 \
      || { echo "  lean failed on $m:"; sed 's/^/    /' "$W/lean.log" | head -5; return 1; }
  done < "$W/order"
}
nmods() { find "$1" -name '*.lean' | wc -l; }

cp -r "$H/test/fixture" "$W/orig"
compile "$W/orig" && pass "original fixture elaborates" || fail "original fixture"

# 1. collide.py: exactly the S_C pair collides (private _root_.Clash.n vs public Clash.n of DefB, imported by the card only)
python3 -I "$H/collide.py" "$W/orig" /dev/null "$TC/src/lean" --out "$W/deny.txt" --jobs 2 > "$W/collide.json" 2> "$W/collide.err" || true
[ "$(cut -f1 "$W/deny.txt" 2>/dev/null)" = "P2M.Sol.S_C" ] && pass "collide.py denies exactly P2M.Sol.S_C" || { fail "collide.py: $(cat "$W/deny.txt" "$W/collide.err" 2>/dev/null | head -3)"; }

# 2. plain collapse without the deny list must FAIL to elaborate (the collision is real), with it must pass
python3 -I "$H/collapse.py" "$W/orig" "$W/c0" --pairs flt > /dev/null
compile "$W/c0" > /dev/null 2>&1 && fail "collapse without deny list should hit the name collision" || pass "collapse without deny list fails as predicted (Clash.n)"
python3 -I "$H/collapse.py" "$W/orig" "$W/c1" --pairs flt --deny "$W/deny.txt" > "$W/c1.json"
[ "$(nmods "$W/c1")" = 8 ] && pass "collapse: 10 -> 8 files (2 pairs inlined, 1 denied)" || fail "collapse: $(nmods "$W/c1") files"
grep -q "^end Inner$" "$W/c1/Theorems/Thm_A.lean" 2>/dev/null && fail "closers: 'end Inner.Deep' must close two scopes" || pass "closers respect 'end A.B' (one scope per component)"
compile "$W/c1" && pass "collapsed tree elaborates" || fail "collapsed tree"

# 3. --unify: Thm_A's card dropped, solution renamed to _root_.A; B is unified too
python3 -I "$H/collapse.py" "$W/orig" "$W/u1" --pairs flt --deny "$W/deny.txt" --unify --pairs-out "$W/u1.pairs" > "$W/u1.json"
grep -q "theorem _root_.A (n : Nat)" "$W/u1/Theorems/Thm_A.lean" && ! grep -q "p2m_exact_reverting" "$W/u1/Theorems/Thm_A.lean" \
  && pass "unify: Thm_A states A once" || fail "unify: Thm_A"
[ "$(grep -c unified "$W/u1.pairs")" = 2 ] && pass "unify: 2 pairs unified" || fail "unify: $(cat "$W/u1.pairs")"
compile "$W/u1" && pass "unified tree elaborates" || fail "unified tree"

# 4. attrhide: check mode (L = R recorded), then hide mode
python3 -I "$C/attrhide/attrhide.py" "$W/orig" "$W/h1" --mode check > /dev/null
compile "$W/h1" && pass "attrhide check tree elaborates" || fail "attrhide check tree"
ok=$(cat "$W/h1/.lake/p2m_hide/Theorems.Thm_B.instance" "$W/h1/.lake/p2m_hide/Theorems.Thm_B.simp" 2>/dev/null | grep -c "LmR=0 RmL=0")
[ "$ok" = 2 ] && pass "attrhide check: explicit lists of Thm_B equal the rule" || fail "attrhide check: $(cat "$W/h1/.lake/p2m_hide/"* 2>/dev/null)"
python3 -I "$C/attrhide/attrhide.py" "$W/orig" "$W/h2" --mode hide --matched "$W/h1/.lake/p2m_hide" > /dev/null
grep -q "^p2m_hide inst (Definitions.DefA P2M.Util)$" "$W/h2/Theorems/Thm_B.lean" && pass "attrhide hide: Thm_B lists -> one line per kind" || fail "attrhide hide: $(grep -n p2m_hide "$W/h2/Theorems/Thm_B.lean")"
compile "$W/h2" && pass "attrhide hide tree elaborates" || fail "attrhide hide tree"

[ $fails = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL ($fails)"
exit $([ $fails = 0 ] && echo 0 || echo 1)
