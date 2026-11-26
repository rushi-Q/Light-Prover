#!/bin/bash
# run_cyc.sh EXPORT... : every kernel of the official and the fast flows on each export (sandboxed via krun),
# 120 s timeout each (124 = timeout/hang). rc: 0 accept, else reject/decline.
TB=${FV_SANDBOX_BIN:-$LIGHT_LEAN/bin}
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PK=${PK:-${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k}
P=/scratch/fastverify/checkers/pchk; DK=/scratch/fastverify/checkers/dualkernel/target/release
G=${G:-${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/gruszka}
printf '%-34s %6s %6s %6s %6s %6s %6s %6s\n' export LEANCHK PLCK-K PLCK NANODA C07 GRUSZ NLFAST
for e in "$@"; do
  r=$($TB/krun "
    cfg='{\"use_stdin\":false,\"export_file_path\":\"$e\",\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"unpermitted_axiom_hard_error\":false,\"num_threads\":4,\"nat_extension\":true,\"string_extension\":true}'
    printf '%s' \"\$cfg\" > /tmp/c.json
    t() { timeout 120 \"\$@\" > /tmp/out.\$\$ 2>&1; echo -n \"\$? \"; }
    t $TC/bin/leanchecker --from-export $e
    t $PK --from-export $e
    t $P/.lake/build/bin/pleanchecker --from-export $e
    t $TC/bin/nanoda_bin /tmp/c.json
    t $P/target/release/nanoda_bin /tmp/c.json
    $DK/susz pack --no-index $e /tmp/m.s >/dev/null 2>&1; t $G /tmp/m.s 1
    t $DK/nl-fast -q -j 4 $e
  ")
  printf '%-34s' "$(basename $e)"; for x in $r; do printf ' %6s' $x; done; echo
done
