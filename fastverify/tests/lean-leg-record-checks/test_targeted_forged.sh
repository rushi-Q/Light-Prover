#!/bin/bash
# test_targeted_forged.sh PLAIN_PLEANCHECKER INCR_PLEANCHECKER OUT : cases of the TARGETED skip
# of pleanchecker_incr, the Lean leg ALONE:
#  g1 (craft_g1*.py): theorem named like the kernel-generated recursor QI.rec (g1a: no recursor record; g1d: recursor
#         record + theorem after it; g1e: theorem before the block), target = QI.rec, snapshot = final = the export;
#         control g1c (genuine shape). Attack: plain and targeted must both exit != 0; control: both 0.
#  forged-ctor (the forged-constructor exports, target d): forged ctor record (forged.export), forged-d-only, honest (control),
#         and the inductInfo-field / unsafe-recursor variants ind-isrec/ind-nidx/ind-nnested/ind-refl/rec-unsafe.
#  ic     (mk_implicit_closure.py, target r9_d): the kernel-implicit names' CLOSURE (string literal ->
#         Char.ofNat -> Char.ofNatAux; String -> ... -> String.utf8EncodeChar): ic/charaux, ic/utf8 (snapshot != final:
#         plain on the final export, FULL incremental and targeted must all exit != 0) and ic/walkpos (snapshot = final:
#         the target precedes Char.ofNat in the walk; plain and targeted must both exit != 0).
# Prints TSV rows + 'RESULT pass=N fail=M'.
set -u
P=$1; I=$2; O=$3; mkdir -p "$O"; H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
ST=${SELFTEST_DIR:-/scratch/fastverify-next/selftest}
# the forged-constructor exports: FORGED_CTOR_DIR=DIR, else unpacked from corpora/forged-ctor.tar.xz (sha256-checked); a missing input
# is a failure
if [ -z "${FORGED_CTOR_DIR:-}" ]; then
  FORGED_CTOR_DIR=$O/forged-ctor; rm -rf "$FORGED_CTOR_DIR"; mkdir -p "$FORGED_CTOR_DIR"
  tar -xJf "$H/corpora/forged-ctor.tar.xz" -C "$FORGED_CTOR_DIR" && (cd "$FORGED_CTOR_DIR" && sha256sum -c --quiet "$H/corpora/forged-ctor.sha256") || { echo "FAIL: forged-ctor corpus"; exit 1; }
fi
for f in honest forged forged-d-only ind-isrec ind-nidx ind-nnested ind-refl rec-unsafe; do [ -s "$FORGED_CTOR_DIR/$f.export" ] || { echo "FAIL: missing $FORGED_CTOR_DIR/$f.export"; exit 1; }; done
/usr/bin/python3 -I $H/recursor_name/craft_g1.py $ST $O/recursor-name > /dev/null && /usr/bin/python3 -I $H/recursor_name/craft_g1dup.py $ST $O/recursor-name > /dev/null || { echo "FAIL: craft_g1"; exit 1; }
echo QI.rec > $O/targets-recursor-name.txt
/usr/bin/python3 -I $H/mk_implicit_closure.py $ST $O/ic > /dev/null || { echo "FAIL mk_implicit_closure.py"; exit 1; }
pass=0; fail=0
one() { # one LABEL EXPORT TARGETS WANT
  local lab=$1 x=$2 tg=$3 want=$4 rp rt ok
  LEAN_STACK_SIZE_KB=917376 timeout 300 "$P" -j4 --from-export "$x" > $O/plain.log 2>&1; rp=$?
  printf 'snap %s\nfinal %s\n' "$x" "$x" | LEAN_STACK_SIZE_KB=917376 timeout 300 "$I" -j4 -v --incremental --targeted="$tg" > $O/tgt.log 2>&1; rt=$?
  local sk; sk=$(grep -o '[0-9]* targets pre-verified' $O/tgt.log | head -1)
  if [ $want = control ]; then [ $rp = 0 ] && [ $rt = 0 ] && ok=PASS || ok=FAIL; else [ $rp != 0 ] && [ $rt != 0 ] && ok=PASS || ok=FAIL; fi
  [ $ok = PASS ] && pass=$((pass+1)) || fail=$((fail+1))
  printf '%s\t%s\t%s\tplain=%s\ttargeted=%s\t%s\t%s\n' $ok "$lab" $want $rp $rt "${sk:-0 targets pre-verified}" "$(grep -E 'rejects|accepts' $O/tgt.log | tail -1 | cut -c1-120)"
}
ic() { # ic LABEL SNAP FINAL TARGETS : every mode must exit != 0 (attack)
  local lab=$1 sn=$2 x=$3 tg=$4 rp rf rt ok
  LEAN_STACK_SIZE_KB=917376 timeout 300 "$P" -j4 --from-export "$x" > $O/plain.log 2>&1; rp=$?
  printf 'snap %s\nfinal %s\n' "$sn" "$x" | LEAN_STACK_SIZE_KB=917376 timeout 300 "$I" -j4 -v --incremental > $O/full.log 2>&1; rf=$?
  printf 'snap %s\nfinal %s\n' "$sn" "$x" | LEAN_STACK_SIZE_KB=917376 timeout 300 "$I" -j4 -v --incremental --targeted="$tg" > $O/tgt.log 2>&1; rt=$?
  [ $rp != 0 ] && [ $rf != 0 ] && [ $rt != 0 ] && ok=PASS || ok=FAIL
  [ $ok = PASS ] && pass=$((pass+1)) || fail=$((fail+1))
  printf '%s\t%s\tattack\tplain=%s\tfull=%s\ttargeted=%s\t%s\t%s\n' $ok "$lab" $rp $rf $rt "$(grep -o 'incremental path not usable ([^;]*' $O/full.log | head -1 | cut -c1-110)" "$(grep -o 'target [^ ]* not skipped: .*' $O/tgt.log | head -1 | cut -c1-110)"
}
one recursor-name/g1c_control $O/recursor-name/g1c_control.export $O/targets-recursor-name.txt control
one recursor-name/g1a_thm_named_rec $O/recursor-name/g1a_thm_named_rec.export $O/targets-recursor-name.txt attack
one recursor-name/g1d_dup_rec_thm $O/recursor-name/g1d_dup_rec_thm.export $O/targets-recursor-name.txt attack
one recursor-name/g1e_dup_thm_rec $O/recursor-name/g1e_dup_thm_rec.export $O/targets-recursor-name.txt attack
one forged-ctor/honest $FORGED_CTOR_DIR/honest.export $FORGED_CTOR_DIR/targets.txt control
for x in forged forged-d-only ind-isrec ind-nidx ind-nnested ind-refl rec-unsafe; do one forged-ctor/$x $FORGED_CTOR_DIR/$x.export $FORGED_CTOR_DIR/targets.txt attack; done
ic ic/charaux $O/ic/charaux/snap.export $O/ic/charaux/final.export $O/ic/targets.txt
ic ic/utf8 $O/ic/utf8/snap.export $O/ic/utf8/final.export $O/ic/targets.txt
one ic/walkpos $O/ic/walkpos.export $O/ic/targets.txt attack
echo "plain $(sha256sum "$P" | cut -c1-16) incr $(sha256sum "$I" | cut -c1-16)"
echo "RESULT pass=$pass fail=$fail"
