#!/bin/bash
# 051 repro: honest toy solution (toy/good: official Lean 4.33.1 build + official lean4export) + an appended chain of N
# kernel-valid definitions PFX.d0 .. PFX.dN (PFX.d(i+1) : Type := (fun _ : Type => PFX.d(i)) S, chainapp.py), written to
# node-local /scratch. All checkers run with DEFAULT stacks; kernels in a krun-equivalent sandbox (kx.sh = the krun sandbox +
# one extra read-only bind for the generated export).
# Usage: ./repro.sh [N PFX]...   default "8000000 x04c" (realized replay DFS depth 4,197,622: official REJECTS, pchk ACCEPTS,
#        check B ACCEPTS). "10000000 x04c" (depth 6,117,257): official REJECTS, pchk REJECTS, check B ACCEPTS.
#        ~15 min per case (official comparator ~8 min). The realized depth is printed by Depth.lean (simulation of
#        Lean/Replay.lean's NameSet-order DFS over the chain).
set -u
H=$(cd "$(dirname "$0")" && pwd); T=$H/toy/good
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PCHK=/scratch/fastverify/checkers/pchk; DK=/scratch/fastverify/checkers/dualkernel
PLC=${PLC:-$PCHK/.lake/build/bin/pleanchecker-k}
if ldd "$PLC" 2>&1 | grep -q "not found"; then PLC=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k; fi
G=${GRUSZKA:-$DK/target/release/gruszka}
${FV_KRUN:-krun} "SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $T/solution.export 2" >/dev/null 2>&1
[ $? -eq 132 ] && G=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka-v3
D=$(mktemp -d ${FV_SCRATCH:-${TMPDIR:-/tmp}}/repro-051.XXXXXX)   # private per run (several runs may share one unix user)
[ -n "${KEEP:-}" ] || trap 'rm -rf "$D"' EXIT
[ $# -eq 0 ] && set -- 8000000 x04c
while [ $# -ge 2 ]; do
  N=$1; P=$2; shift 2
  SOL=$D/good+chain$N-$P.export; CH=$T/challenge.export
  [ -s $SOL ] || python3 $H/chainapp.py $T/solution.export $N $SOL 2 $P
  echo "### N=$N prefix=$P: export $(stat -c %s $SOL) bytes; $($TC/bin/lean --run $H/Depth.lean $N $P 2>&1 | tail -1)"
  W=$(mktemp -d /tmp/x04-051.XXXXXX); cd $W
  cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "external_kernels": {"nanoda": ["nanoda_bin"]}}
JSON
  t() { local s=$(date +%s); timeout -k 10 ${LIMIT:-3600} "$@" > out.log 2>&1; local r=$?; echo "exit $r ($(( $(date +%s) - s )) s)  $(grep -m2 -E 'okay|^error|with-kernel|Stack overflow' out.log | tr '\n' ' ' | cut -c1-150)"; }
  echo "OFFICIAL lake comparator 4.36 (nanoda + Lean kernel): $(PATH=$TC/bin:$PATH t $TC/bin/lake comparator --config comparator.json --challenge-from-export $CH --solution-from-export $SOL)"
  echo "FAST A  pchk run.sh T=32:                             $(t $H/kx.sh $D "CCMP_LEANCHECKER=$PLC sh $PCHK/run.sh $PCHK $SOL 32 $CH")"
  echo "FAST B  kcompare + (gruszka AND nl-fast):             $(t $H/kx.sh $D "sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 16 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 16 :: $DK/target/release/nl-fast -q -j 16 $SOL")"
  if docker info >/dev/null 2>&1; then   # the DEPLOYED pleanchecker-k (glibc 2.38) in a throw-away ubuntu:24.04 container
    echo "FAST A' DEPLOYED pleanchecker-k (container):         $(PK_BIND=$D t $H/pk-deployed --from-export $SOL)"
  fi
  cd /; rm -rf $W; [ -n "${KEEP:-}" ] || rm -f $SOL
done
