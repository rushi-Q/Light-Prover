#!/bin/bash
# tests/cross-version-regress/run.sh [FV_ROOT] - regression tests of the cross-version gate and the judges on official 4.36 / 4.37 exports: cases escaped-json (CRITICAL), primitive-closure-hole (HIGH),
# mdata-hole (MEDIUM), duplicate-meta (inputs in x/ with SHA256SUMS). Every row runs a TRUSTED entry point
# of FV_ROOT on the reproduction inputs and compares verdict + exit code with the fixed behaviour:
#   escaped-json            4.37 challenge whose definition record is written with JSON spaces / escapes + a non-sorried hole
#          Nat.shiftLeft._f + a proof of False: official Lean 4.37.0-rc1 lake comparator REJECTS -> every judge REJECTED
#          (4.36 copy of the same, --require-sorried-holes: DECLINED). Before the fix: OK / ACCEPTED.
#   primitive-closure-hole  canonical official 4.36 challenge, definition hole Nat.shiftLeft._f (in the closure of the GMP primitive
#          Nat.shiftLeft) + a proof of False: official 4.36 comparator ACCEPTS (spec gap) -> every judge and the warm daemon
#          refuse (DECLINED / refuses to start). Before the fix: ACCEPTED.
#   mdata-hole              official 4.37.0-rc1 leanexport --export-mdata challenge with a sorried hole under mdata: official comparator
#          ACCEPTS -> xvcheck OK, check-sound ACCEPTED (4.36 and 4.37 pins); cyclic expression indices -> no verdict in
#          bounded time. Before the fix: REJECTED / hang.
#   duplicate-meta          4.37.0-rc1 challenge whose META line holds "lean" twice (4.37.0-rc1, then 4.36.0) + non-sorried hole: official
#          4.37.0-rc1 comparator REJECTS -> the gate refuses the meta line (DECLINED) in every judge. Before the fix: gated as
#          4.36.0, OK -> ACCEPTED.
# Optional reference rows (official toolchains present): the official comparators' own verdicts on the same inputs.
# Prints PASS/FAIL rows and RESULT; exit 0 iff no FAIL. THREADS (default 4).
{ # whole script parsed before it runs (safe against edits while running)
set -u
FV=${1:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}; X=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)/x
T=${THREADS:-4}; W=$(mktemp -d /tmp/cross-version-regress.XXXXXX); trap 'rm -rf "$W"' EXIT
( cd "$X" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL inputs: SHA256SUMS mismatch"; exit 1; }
pass=0; fail=0
row() { # row NAME WANT_RC WANT_VERDICT GOT_RC GOT_VERDICT [DETAIL]
  if [ "$2" = "$4" ] && [ "$3" = "$5" ]; then echo "PASS $1 (rc=$4 $5)"; pass=$((pass+1))
  else echo "FAIL $1: want rc=$2 $3, got rc=$4 $5 ${6:+| $6}"; fail=$((fail+1)); fi; }
jv() { /usr/bin/python3 -I -c 'import json,sys
try: j=json.load(open(sys.argv[1])); print(j.get(sys.argv[2]) if len(sys.argv) > 2 else j.get("verdict"))
except Exception: print("NO-JSON")' "$@"; }
jr() { /usr/bin/python3 -I -c 'import json,sys
try: print(str(json.load(open(sys.argv[1])).get("reason",""))[:160])
except Exception: print("")' "$1"; }
XV=$FV/check/xversion/xvcheck.py; REL=$FV/check/xversion/releases.json
xv() { # xv NAME WANT_RC WANT_VERDICT CHAL CFG [ARGS..]
  local n=$1 wr=$2 wv=$3 c=$4 g=$5; shift 5
  timeout 60 /usr/bin/python3 -I "$XV" "$X/$c" "$X/$g" --releases "$REL" --json "$W/$n.json" "$@" > /dev/null 2>&1; local rc=$?
  row "$n" "$wr" "$wv" "$rc" "$(jv "$W/$n.json")" "$(jr "$W/$n.json")"; }
judge() { # judge NAME WANT_RC WANT_VERDICT SCRIPT SOL CHAL CFG [ARGS..]
  local n=$1 wr=$2 wv=$3 s=$4 so=$5 c=$6 g=$7; shift 7
  timeout 1800 "$FV/$s" "$X/$so" "$X/$c" "$X/$g" --threads "$T" --json "$W/$n.json" "$@" > "$W/$n.log" 2>&1; local rc=$?
  row "$n" "$wr" "$wv" "$rc" "$(jv "$W/$n.json")" "$(jr "$W/$n.json")"; }
fastv() { # fastv NAME WANT_RC WANT_VERDICT SOL CHAL CFG [ARGS..]
  local n=$1 wr=$2 wv=$3 so=$4 c=$5 g=$6; shift 6
  mkdir -p "$W/$n.ch"; cp "$X/$c" "$W/$n.ch/challenge.export"; cp "$X/$g" "$W/$n.ch/comparator.json"
  timeout 1800 "$FV/bin/fastverify" - "$W/$n.ch" "$W/$n.out" --from-export "$X/$so" --preset sound --threads "$T" \
    --challenge-sha256 "$(sha256sum "$W/$n.ch/challenge.export" | cut -d' ' -f1)" \
    --comparator-sha256 "$(sha256sum "$W/$n.ch/comparator.json" | cut -d' ' -f1)" "$@" > "$W/$n.log" 2>&1; local rc=$?
  row "$n" "$wr" "$wv" "$rc" "$(jv "$W/$n.out/result.json")" "$(tail -1 "$W/$n.log" | cut -c1-160)"; }

echo "== escaped JSON: definition records in valid non-compact / escaped JSON (4.37 challenge, non-sorried hole, proof of False)"
xv escaped-json-xvcheck-rsh-canonical 1 REJECTED chal37_canon.export comparator_shl.json --require-sorried-holes
xv escaped-json-xvcheck-rsh-spaced    1 REJECTED chal37_spaced.export comparator_shl.json --require-sorried-holes
xv escaped-json-xvcheck-rsh-escaped   1 REJECTED chal37_uesc.export comparator_shl.json --require-sorried-holes
xv escaped-json-xvcheck-escaped       1 REJECTED chal37_uesc.export comparator_shl.json
judge escaped-json-check-sound-rsh-4kernels 1 REJECTED check/sound/check-sound.sh sol37_prove_false.export chal37_uesc.export comparator_shl.json --require-sorried-holes --kernel con-leche --kernel nanoda
judge escaped-json-check-sound-pins437      1 REJECTED check/sound/check-sound.sh sol37_prove_false.export chal37_uesc.export comparator_shl.json --pins "$FV/check/sound/pins-437.env"
judge escaped-json-check-sound-svc-rsh      1 REJECTED check/sound/check-sound-svc.sh sol37_prove_false.export chal37_spaced.export comparator_shl.json --require-sorried-holes
judge escaped-json-check-notary-rsh         1 REJECTED check/notary/check-notary.sh sol37_prove_false.export chal37_uesc.export comparator_shl.json --require-sorried-holes
judge escaped-json-check-lowmem-rsh         1 REJECTED check/lowmem/check-sound-lowmem.sh sol37_prove_false.export chal37_uesc.export comparator_shl.json --require-sorried-holes
judge escaped-json-check-ultralowmem-rsh    1 REJECTED check/lowmem/check-sound-ultralowmem.sh sol37_prove_false.export chal37_uesc.export comparator_shl.json --require-sorried-holes
fastv escaped-json-fastverify-sound-rsh     1 REJECTED sol37_prove_false.export chal37_uesc.export comparator_shl.json --require-sorried-holes
judge escaped-json-check-sound-436-escaped-rsh 2 DECLINED check/sound/check-sound.sh sol36_prove_false.export chal36_uesc.export comparator_shl.json --require-sorried-holes

echo "== primitive closure hole: canonical 4.36 challenge, hole Nat.shiftLeft._f in the closure of the GMP primitive Nat.shiftLeft (proof of False)"
xv primitive-closure-hole-xvcheck 2 DECLINED chal36_canon.export comparator_shl.json
judge primitive-closure-hole-check-sound-4kernels 2 DECLINED check/sound/check-sound.sh sol36_prove_false.export chal36_canon.export comparator_shl.json --kernel con-leche --kernel nanoda
judge primitive-closure-hole-check-sound-svc      2 DECLINED check/sound/check-sound-svc.sh sol36_prove_false.export chal36_canon.export comparator_shl.json
judge primitive-closure-hole-check-notary         2 DECLINED check/notary/check-notary.sh sol36_prove_false.export chal36_canon.export comparator_shl.json
judge primitive-closure-hole-check-lowmem         2 DECLINED check/lowmem/check-sound-lowmem.sh sol36_prove_false.export chal36_canon.export comparator_shl.json
judge primitive-closure-hole-check-ultralowmem    2 DECLINED check/lowmem/check-sound-ultralowmem.sh sol36_prove_false.export chal36_canon.export comparator_shl.json
judge primitive-closure-hole-check-frontier       2 DECLINED check/frontier/check-frontier.sh sol36_prove_false.export chal36_canon.export comparator_shl.json
fastv primitive-closure-hole-fastverify-sound     2 ERROR sol36_prove_false.export chal36_canon.export comparator_shl.json   # bin/fastverify: its gate refusal = ERROR (no verdict)
# the warm daemon refuses to start (its start-up xversion gate runs before the base is read)
timeout 120 /usr/bin/python3 -I "$FV/check/warm/fvcheckd.py" serve --state "$W/warm-state" --challenge "$X/chal36_canon.export" \
  --challenge-sha256 "$(sha256sum "$X/chal36_canon.export" | cut -d' ' -f1)" --config "$X/comparator_shl.json" \
  --base "$X/sol36_prove_false.export" --threads "$T" --skip-selftest > "$W/warm.log" 2>&1; rc=$?
if [ "$rc" != 0 ] && [ "$rc" != 124 ] && grep -q "xversion gate refused the challenge" "$W/warm.log" && grep -q "dependency closure" "$W/warm.log"; then
  row primitive-closure-hole-fvcheckd-refuses-to-start x REFUSED x REFUSED
else row primitive-closure-hole-fvcheckd-refuses-to-start x REFUSED "$rc" "STARTED-OR-OTHER" "$(grep -m1 -i "error\|refus" "$W/warm.log" | cut -c1-160)"; fi
pkill -f "$W/warm-state" 2>/dev/null

echo "== mdata hole: official 4.37 --export-mdata challenge (sorried hole under mdata); cyclic expression indices"
xv mdata-hole-xvcheck-mdata 0 OK chal_official_mdata.export comparator_mdata.json
# the gate no longer false-rejects; the judge's verdict is then decided by the legs: the official-kernel leg accepts, the
# second kernel gruszka 3eb3aadd declines Expr.mdata in the SOLUTION export ('Expr.mdata is not supported') -> DECLINED (no
# verdict; availability limit of the pinned second kernel, not a gate decision). Before the fix: REJECTED by the gate.
judge mdata-hole-check-sound-mdata         2 DECLINED check/sound/check-sound.sh sol_official_mdata.export chal_official_mdata.export comparator_mdata.json
judge mdata-hole-check-sound-mdata-pins437 2 DECLINED check/sound/check-sound.sh sol_official_mdata.export chal_official_mdata.export comparator_mdata.json --pins "$FV/check/sound/pins-437.env"
for n in mdata-hole-check-sound-mdata mdata-hole-check-sound-mdata-pins437; do
  r=$(jr "$W/$n.json"); case "$r" in *"second kernel could not decide"*) row "$n-reason-is-second-kernel-not-gate" 0 second-kernel 0 second-kernel;;
    *) row "$n-reason-is-second-kernel-not-gate" 0 second-kernel 1 "other" "$r";; esac
  l=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("legs",{}).get("lean",{}).get("message",""))' "$W/$n.json" 2>/dev/null)
  [ "$l" = "Lean default kernel accepts the solution" ] && row "$n-official-kernel-leg-accepts" 0 accepts 0 accepts || row "$n-official-kernel-leg-accepts" 0 accepts 1 "$l"
done
t0=$(date +%s); xv mdata-hole-xvcheck-cyclic 2 DECLINED cyclic_chal.export cyclic_cfg.json; echo "     (cyclic: $(( $(date +%s) - t0 )) s)"

echo "== duplicate meta key: 4.37.0-rc1 challenge whose META line holds \"lean\" twice (4.37.0-rc1, then 4.36.0); non-sorried hole 'secret'"
xv duplicate-meta-xvcheck-canonical-meta     1 REJECTED dupmeta_chal37.export dupmeta_cfg.json
xv duplicate-meta-xvcheck-duplicate-lean-key 2 DECLINED dupmeta_chal37_dupmeta.export dupmeta_cfg.json
xv duplicate-meta-xvcheck-duplicate-lean-key-rsh 2 DECLINED dupmeta_chal37_dupmeta.export dupmeta_cfg.json --require-sorried-holes
case "$(jr "$W/duplicate-meta-xvcheck-duplicate-lean-key-rsh.json")" in *"meta line (release identity) refused"*) row duplicate-meta-rsh-reason-is-meta-line 0 meta 0 meta;;
  *) row duplicate-meta-rsh-reason-is-meta-line 0 meta 1 other "$(jr "$W/duplicate-meta-xvcheck-duplicate-lean-key-rsh.json")";; esac
judge duplicate-meta-check-sound-canonical-meta 1 REJECTED check/sound/check-sound.sh dupmeta_sol37.export dupmeta_chal37.export dupmeta_cfg.json
judge duplicate-meta-check-sound-dupmeta        2 DECLINED check/sound/check-sound.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
judge duplicate-meta-check-sound-dupmeta-pins437 2 DECLINED check/sound/check-sound.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json --pins "$FV/check/sound/pins-437.env"
judge duplicate-meta-check-sound-svc-dupmeta    2 DECLINED check/sound/check-sound-svc.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
judge duplicate-meta-check-notary-dupmeta       2 DECLINED check/notary/check-notary.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
judge duplicate-meta-check-lowmem-dupmeta       2 DECLINED check/lowmem/check-sound-lowmem.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
judge duplicate-meta-check-ultralowmem-dupmeta  2 DECLINED check/lowmem/check-sound-ultralowmem.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
judge duplicate-meta-check-frontier-dupmeta     2 DECLINED check/frontier/check-frontier.sh dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json
fastv duplicate-meta-fastverify-sound-dupmeta   2 ERROR dupmeta_sol37.export dupmeta_chal37_dupmeta.export dupmeta_cfg.json   # bin/fastverify: gate refusal = ERROR

# reference rows: the official comparators on the same inputs (documents the target behaviour; skipped without toolchains)
TCR=${TOOLCHAINS:-$HOME/.elan/toolchains}
offc() { # offc NAME WANT_RC TC CHAL CFG SOL
  local tc=$TCR/leanprover--lean4---$3; [ -x "$tc/bin/lake" ] || { echo "SKIP $1 (no $tc)"; return; }
  mkdir -p "$W/$1"; ( cd "$W/$1" && env -i PATH="$tc/bin:/usr/bin:/bin" HOME="$W/$1" LANG=C.UTF-8 timeout 1800 lake comparator \
    --config "$X/$5" --challenge-from-export "$X/$4" --solution-from-export "$X/$6" > out.log 2>&1 ); local rc=$?
  if [ "$rc" = "$2" ]; then echo "PASS ref $1 (official rc=$rc)"; pass=$((pass+1)); else echo "FAIL ref $1: official rc=$rc want $2 | $(tail -1 "$W/$1/out.log" | cut -c1-120)"; fail=$((fail+1)); fi; }
offc official-437-spaced-rejects 1 v4.37.0-rc1 chal37_spaced.export comparator_shl.json sol37_prove_false.export
offc official-437-escaped-rejects 1 v4.37.0-rc1 chal37_uesc.export comparator_shl.json sol37_prove_false.export
offc official-436-closure-hole-accepts-spec-gap 0 v4.36.0 chal36_canon.export comparator_shl.json sol36_prove_false.export
offc official-437-mdata-accepts 0 v4.37.0-rc1 chal_official_mdata.export comparator_mdata.json sol_official_mdata.export
offc official-437-dupmeta-rejects 1 v4.37.0-rc1 dupmeta_chal37_dupmeta.export dupmeta_cfg.json dupmeta_sol37.export
echo "RESULT pass=$pass fail=$fail"; [ "$fail" = 0 ]; exit $?
}
