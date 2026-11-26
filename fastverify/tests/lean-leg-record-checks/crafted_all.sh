#!/bin/bash
# crafted_all.sh BIN KIND OUTPREFIX  : every crafted single-kernel suite on one
# Lean-leg binary, ALONE.
#   KIND plain  : leanleg.sh (par + --seq) on the CVE shapes (crafted by leanleg.sh) + the 14 kernel-issues exports + mk_kernel_issue_exports.py's 5 + c2s (streaming cases) + c1only
#                 + implicit (kernel-implicit closure) + the C1/C2 edge cases (par,seq)
#   KIND incr   : plain + incr.sh (full/targeted incremental modes) + test_incr_attacks.py (ATK3/4/5, ATK6/7)
#   KIND lowmem : the ultra-low-memory leg: leanleg.sh through the --low-mem --evict=smart wrapper + the C1/C2 edge cases (lowmem,par,seq)
# Inputs: with CRAFTED=DIR, the prepared corpora DIR/{kernel-issues/crafted,kernel-issues/so,issue-analogues,c2s,c1only,implicit/finals}; without it everything
# is made in a fresh temporary directory: issue-analogues (mk_kernel_issue_exports.py), c2s (mk_c2_stream.py), c1only (mk_c1only.py), implicit
# (mk_implicit_closure.py), all from SELFTEST_DIR's good.export, and the kernel-issues corpus (made by fastverify/tests/kernel-issues/
# test.py with the official 4.33.1 toolchain) unpacked from corpora/kernel-crafted.tar.xz (sha256s in corpora/kernel-crafted.sha256).
# A missing or empty input directory is a FAILURE (exit 1), never a silent skip.
# Writes OUTPREFIX.<suite>.tsv and prints one summary line per suite; exit 0 iff every suite printed 'RESULT PASS' / 'fail=0'.
set -u
B=$1; K=$2; O=$3; H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
ST=${SELFTEST_DIR:-/scratch/fastverify-next/selftest}; export SELFTEST_DIR=$ST
die() { echo "FAIL: $*"; exit 1; }
if [ -n "${CRAFTED:-}" ]; then CR=$CRAFTED
else
  CR=$(mktemp -d "${TMPDIR:-/tmp}/leanleg-crafted.XXXXXX"); trap 'rm -rf "$CR"' EXIT
  py() { /usr/bin/python3 -I "$@" > /dev/null || die "generator $1"; }
  py "$H/mk_kernel_issue_exports.py" "$ST/good.export" "$CR/issue-analogues"; py "$H/mk_c2_stream.py" "$ST/good.export" "$CR/c2s"
  py "$H/mk_c1only.py" "$ST" "$CR/c1only"; py "$H/mk_implicit_closure.py" "$ST" "$CR/implicit"
  mkdir -p "$CR/kernel-issues" && tar -xJf "$H/corpora/kernel-crafted.tar.xz" -C "$CR/kernel-issues" && (cd "$CR/kernel-issues" && sha256sum -c --quiet "$H/corpora/kernel-crafted.sha256") \
    || die "kernel-issues corpus (corpora/kernel-crafted.tar.xz)"
fi
for d in kernel-issues/crafted issue-analogues c2s c1only implicit/finals; do
  compgen -G "$CR/$d/*.export" > /dev/null || die "no crafted exports in $CR/$d"
done
[ -s "$CR/kernel-issues/so/Solution.export" ] || die "missing $CR/kernel-issues/so/Solution.export (kernel-issues base control)"
rc=0
sum() { local r; r=$(grep -E '^RESULT' "$2" | tail -1); printf '%-28s %s  [%s]\n' "$1" "$r" "$2"
  case "$r" in "RESULT PASS"*|*" fail=0") ;; *) rc=1;; esac; }
echo "binary $B sha256 $(sha256sum "$B" | cut -d' ' -f1) kind $K host $(hostname) $(date -u +%FT%TZ) inputs $CR"
if [ "$K" = lowmem ]; then
  # (C1-only exports are not run here: the ultra-low-memory leg accepts them by design - its C1 covers exactly the blocks it
  #  hands to the kernel)
  W=$(mktemp -d /tmp/leanleg-lmw.XXXXXX); printf '#!/bin/sh\nfor a do shift; [ "$a" = --seq ] || set -- "$@" "$a"; done\nexec %s --low-mem --evict=smart "$@"\n' "$B" > $W/lm; chmod +x $W/lm
  bash "$H/leanleg.sh" $W/lm "$CR/kernel-issues/crafted" "$CR/issue-analogues" "$CR/c2s" "$CR/implicit/finals" > "$O.leanleg-lowmem.tsv" 2>&1; sum leanleg-lowmem-evict "$O.leanleg-lowmem.tsv"
  bash "$H/leanleg.sh" "$B" "$CR/kernel-issues/crafted" "$CR/issue-analogues" "$CR/c2s" "$CR/implicit/finals" > "$O.leanleg-plain.tsv" 2>&1; sum leanleg-plain-modes "$O.leanleg-plain.tsv"
  /usr/bin/python3 -I "$H/test_c1c2_edge_cases.py" "$B" --modes lowmem,par,seq > "$O.c1c2-edge.tsv" 2>&1; sum c1c2-edge "$O.c1c2-edge.tsv"
  rm -rf $W
  exit $rc
fi
bash "$H/leanleg.sh" "$B" "$CR/kernel-issues/crafted" "$CR/issue-analogues" "$CR/c2s" "$CR/c1only" "$CR/implicit/finals" > "$O.leanleg.tsv" 2>&1; sum leanleg "$O.leanleg.tsv"
/usr/bin/python3 -I "$H/test_c1c2_edge_cases.py" "$B" --modes par,seq > "$O.c1c2-edge.tsv" 2>&1; sum c1c2-edge "$O.c1c2-edge.tsv"
if [ "$K" = incr ]; then
  bash "$H/incr.sh" "$B" "$CR/kernel-issues/crafted" "$CR/issue-analogues" "$CR/implicit/finals" > "$O.incr.tsv" 2>&1; sum incr-modes "$O.incr.tsv"
  /usr/bin/python3 -I "$H/test_incr_attacks.py" "$B" > "$O.incr-attacks.tsv" 2>&1; sum incr-attacks "$O.incr-attacks.tsv"
fi
exit $rc
