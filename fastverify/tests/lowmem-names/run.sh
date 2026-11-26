#!/bin/bash
# tests/lowmem-names/run.sh [FASTVERIFY_ROOT]  -- regression test of name handling in the
# low-memory comparison: ccmp-lowmem (check/lowmem/src{,-437}: LowMemParse.lean +
# lowmem_arena.c) must read NAMES exactly like the official reader (LeanExport/Parse.lean: name indices map to Names,
# declarations are keyed by Name): a second name index of an existing Name is an alias (accepted), and a Name declared
# twice - under two aliased indices - is 'Duplicate declaration' (refused). Fails on the earlier binaries (66d15628 /
# 8fd79c6c), passes with the current ones (pins in check/lowmem/pins{,-437,-ultralowmem}.env).
# Inputs (data/, SHA256SUMS): L2/L3b/L3c + cfg-nokernels.json (a second name index for an existing Name),
# the repro inputs dupdecl_* (a Name declared twice under two aliased indices, written by a
# generator script; dupdecl_sol_st.export = dupdecl_sol_436 with the self-test challenge's meta line, so
# the full judges' cross-version gate admits it), the package's pinned self-test challenge.
# Oracle (optional rows "ref/*", run when the official 4.36 toolchain is present): official `lake comparator` 4.36 ACCEPTS
# L2/L3b/L3c and REJECTS the dupdecl inputs with 'Duplicate declaration: fvSelfTest'.
set -u
FV=$(readlink -f "${1:-$(dirname "$(readlink -f "$0")")/../..}")
D=$(cd "$(dirname "$(readlink -f "$0")")/data" && pwd)
( cd "$D" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL inputs: data/SHA256SUMS"; echo "RESULT pass=0 fail=1"; exit 1; }
W=$(mktemp -d "${TMPDIR:-/tmp}/lowmem-names.XXXXXX"); trap 'rm -rf "$W"' EXIT
pass=0; fail=0
ok() { echo "PASS $1"; pass=$((pass+1)); }
no() { echo "FAIL $1: $2"; fail=$((fail+1)); }
pin() { awk -v n="$2" '$1=="PIN" && $2==n {print $4}' "$1"; }
CHAL=$(pin "$FV/check/sound/pins.env" selftest_challenge)
TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
TC37=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$FV/config/components.json" 2>/dev/null)
LM36=$(pin "$FV/check/lowmem/pins.env" ccmp_lowmem); LM37=$(pin "$FV/check/lowmem/pins-437.env" ccmp_lowmem)
ULMBIN=$(pin "$FV/check/lowmem/pins-ultralowmem.env" ccmp_lowmem)
[ "$ULMBIN" = "$LM36" ] || no "pins/ultralowmem-ccmp" "pins-ultralowmem.env pins another ccmp_lowmem ($ULMBIN) than pins.env ($LM36)"
cfg_cmp() {  # the comparator config as the judges pass it to ccmp-lowmem --compare-only (no external kernels)
  /usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("external_kernels",None); c.pop("enable_nanoda",None); json.dump(c,open(sys.argv[2],"w"))' "$1" "$2"; }
cfg_cmp "$D/cfg-nokernels.json" "$W/cfg_l.json"; cfg_cmp "$D/dupdecl_cfg.json" "$W/cfg_z.json"
leg() {  # leg NAME BIN TC CFG CHAL SOL WANT_RC WANT_REGEX   (ccmp-lowmem --compare-only, the low-memory judges' leg 1)
  local n=$1 b=$2 tc=$3 cfg=$4 ch=$5 sol=$6 wrc=$7 re=$8
  [ -x "$b" ] && [ -d "$tc" ] || { no "$n" "binary $b or toolchain $tc missing"; return; }
  ( cd "$W" && LEAN_ABORT_ON_PANIC=1 "$b" "$tc" "$cfg" "$ch" "$sol" --compare-only ) > "$W/leg.out" 2>&1; local rc=$?
  if [ "$rc" = "$wrc" ] && grep -qE "$re" "$W/leg.out"; then ok "$n"; else no "$n" "rc=$rc (want $wrc /$re/): $(grep -E '^error|passed' "$W/leg.out" | head -n 2 | tr '\n' ' ')"; fi
}
judge() {  # judge NAME WANT_RC WANT_VERDICT REASON_REGEX(-=any) SCRIPT EXPORT CHALLENGE CONFIG [ARGS...]
  local n=$1 wrc=$2 wv=$3 re=$4; shift 4
  "$@" --threads 4 --workdir "$W" > "$W/j.out" 2> "$W/j.err"; local rc=$?
  local got; got=$(tail -n 1 "$W/j.out" | /usr/bin/python3 -I -c 'import json,sys
try: d=json.loads(sys.stdin.read()); print(d.get("verdict"), "|", d.get("reason"))
except Exception: print("BADJSON |")')
  if [ "$rc" = "$wrc" ] && [ "${got%% |*}" = "$wv" ] && { [ "$re" = - ] || printf '%s' "${got#*| }" | grep -qE "$re"; }; then ok "$n"
  else no "$n" "rc=$rc $got (want $wrc $wv /$re/)"; fi
}

# ---- a Name declared twice under two aliased indices (clean copy for checkAxioms, forged copy for compareAt) ----
leg duplicate-declaration/leg1-436 "$LM36" "$TC36" "$W/cfg_z.json" "$D/dupdecl_chal_436.export" "$D/dupdecl_sol_436.export" 1 '^error: Duplicate declaration: fvSelfTest'
leg duplicate-declaration/leg1-437 "$LM37" "$TC37" "$W/cfg_z.json" "$D/dupdecl_chal_437.export" "$D/dupdecl_sol_437.export" 1 '^error: Duplicate declaration: fvSelfTest'
leg duplicate-declaration/leg1-436-selftest-meta "$LM36" "$TC36" "$W/cfg_z.json" "$CHAL" "$D/dupdecl_sol_st.export" 1 '^error: Duplicate declaration: fvSelfTest'
judge duplicate-declaration/check-sound-lowmem 1 REJECTED 'Duplicate declaration: fvSelfTest' "$FV/check/lowmem/check-sound-lowmem.sh" "$D/dupdecl_sol_st.export" "$CHAL" "$D/dupdecl_cfg.json"
judge duplicate-declaration/check-sound-lowmem-437 1 REJECTED 'Duplicate declaration: fvSelfTest' "$FV/check/lowmem/check-sound-lowmem.sh" "$D/dupdecl_sol_st.export" "$CHAL" "$D/dupdecl_cfg.json" --pins "$FV/check/lowmem/pins-437.env"
judge duplicate-declaration/check-sound-ultralowmem 1 REJECTED 'Duplicate declaration: fvSelfTest' "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/dupdecl_sol_st.export" "$CHAL" "$D/dupdecl_cfg.json"
judge duplicate-declaration/check-sound-control 1 REJECTED - "$FV/check/sound/check-sound.sh" "$D/dupdecl_sol_st.export" "$CHAL" "$D/dupdecl_cfg.json"

# ---- a second name index for an existing Name (official comparator ACCEPTS) ----
for c in L2-dupname-target L3b-dupname-legal-used L3c-dupname-legal-origref; do
  leg "duplicate-name-legal/$c/leg1-436" "$LM36" "$TC36" "$W/cfg_l.json" "$CHAL" "$D/$c.export" 0 '^Comparison and axiom check passed!$'
  leg "duplicate-name-legal/$c/leg1-437" "$LM37" "$TC37" "$W/cfg_l.json" "$CHAL" "$D/$c.export" 0 '^Comparison and axiom check passed!$'
  judge "duplicate-name-legal/$c/check-sound-lowmem" 0 ACCEPTED - "$FV/check/lowmem/check-sound-lowmem.sh" "$D/$c.export" "$CHAL" "$D/cfg-nokernels.json"
  judge "duplicate-name-legal/$c/check-sound-lowmem-437" 0 ACCEPTED - "$FV/check/lowmem/check-sound-lowmem.sh" "$D/$c.export" "$CHAL" "$D/cfg-nokernels.json" --pins "$FV/check/lowmem/pins-437.env"
  judge "duplicate-name-legal/$c/check-sound-ultralowmem" 0 ACCEPTED - "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/$c.export" "$CHAL" "$D/cfg-nokernels.json"
  judge "duplicate-name-legal/$c/check-sound-control" 0 ACCEPTED - "$FV/check/sound/check-sound.sh" "$D/$c.export" "$CHAL" "$D/cfg-nokernels.json"
done

# ---- full-width expression ids. wide_wrap_value = self-test good.export whose target value
# refers to expr id 2^64+527 (unbound: the official reader fails 'Expr not found'); wide_sparse_valid = good.export + one unused
# expr bound at id 2^64 (the official comparator accepts). Previously the dense pass truncated the id to 64 bits (527) and
# leg 1 passed wide_wrap_value; now any slow-line number >= 2^32 declines pass 1 and the official reader decides. ----
leg wide-expr-id/wrap-leg1-436 "$LM36" "$TC36" "$W/cfg_l.json" "$CHAL" "$D/wide_wrap_value.export" 1 '^error: Expr not found 18446744073709552143'
leg wide-expr-id/wrap-leg1-437 "$LM37" "$TC37" "$W/cfg_l.json" "$CHAL" "$D/wide_wrap_value.export" 1 '^error: Expr not found 18446744073709552143'
leg wide-expr-id/sparse-valid-leg1-436 "$LM36" "$TC36" "$W/cfg_l.json" "$CHAL" "$D/wide_sparse_valid.export" 0 '^Comparison and axiom check passed!$'
judge wide-expr-id/wrap/check-sound-lowmem 1 REJECTED 'Expr not found' "$FV/check/lowmem/check-sound-lowmem.sh" "$D/wide_wrap_value.export" "$CHAL" "$D/cfg-nokernels.json"
judge wide-expr-id/wrap/check-sound-ultralowmem 1 REJECTED 'Expr not found' "$FV/check/lowmem/check-sound-ultralowmem.sh" "$D/wide_wrap_value.export" "$CHAL" "$D/cfg-nokernels.json"

# ---- reference rows: the official Lean 4.36 lake comparator on the same inputs (oracle; skipped without the toolchain) ----
if [ -x "$TC36/bin/lake" ]; then
  printf '{"version":"1.1.0","packagesDir":".lake/packages","packages":[]}\n' > "$W/lake-manifest.json"
  ref() { local n=$1 sol=$2 cfg=$3 wrc=$4 re=$5
    ( cd "$W" && LEAN_ABORT_ON_PANIC=1 PATH="$TC36/bin:/usr/bin:/bin" "$TC36/bin/lake" comparator --config="$cfg" \
        --challenge-from-export="$CHAL" --solution-from-export="$sol" ) > "$W/ref.out" 2>&1; local rc=$?
    if [ "$rc" = "$wrc" ] && grep -qE "$re" "$W/ref.out"; then ok "$n"; else no "$n" "rc=$rc: $(tail -n 2 "$W/ref.out" | tr '\n' ' ')"; fi; }
  ref ref/official-436/duplicate-declaration "$D/dupdecl_sol_st.export" "$W/cfg_z.json" 1 'Duplicate declaration: fvSelfTest'
  for c in L2-dupname-target L3b-dupname-legal-used L3c-dupname-legal-origref wide_sparse_valid; do
    ref "ref/official-436/$c" "$D/$c.export" "$W/cfg_l.json" 0 'Your solution is okay!'
  done
  ref ref/official-436/wide_wrap_value "$D/wide_wrap_value.export" "$W/cfg_l.json" 1 'Expr not found 18446744073709552143'
else
  echo "SKIP ref/*: official Lean 4.36 toolchain not found"
fi
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?
