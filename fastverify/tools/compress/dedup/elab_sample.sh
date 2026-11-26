#!/bin/bash
# elab_sample.sh SRC_ROOT MODLIST OUTDIR BASE_LAKE [JOBS] [TIMEOUT_S] [EXTRA_LEAN_OPTS...]
# Module-level G2 check: elaborates each module of MODLIST (one module name per line) from SRC_ROOT (the source root of
# an edited tree) against the BASE build's oleans (BASE_LAKE = <base project>/.lake: build/lib/lean + packages/*), with
# the official Lean 4.33.1, kernel ON, linters off, inside the read-only bwrap sandbox without network (only OUTDIR
# writable). Imports resolve to the base oleans: valid for edits that keep every statement (proof/alias/redirect edits).
# RH options (lakefile leanOptions) are passed; GroundTheory.{Local,Global}Fields.* get synthInstance.maxHeartbeats.
# Output: OUTDIR/res.tsv  module<TAB>rc<TAB>seconds ; OUTDIR/log/<module>.log
set -u
H=$(cd "$(dirname "$0")" && pwd)
SRC=$(readlink -f $1); L=$(readlink -f $2); O=$(mkdir -p $3 && readlink -f $3); B=$(readlink -f $4); J=${5:-32}; TO=${6:-900}
shift $(( $# < 6 ? $# : 6 ))
TC=${INCR_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
LP=$B/build/lib/lean; for d in $B/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
mkdir -p $O/log $O/olean
cat > $O/one.sh <<EOS
#!/bin/bash
m=\$1; f=$SRC/\$(echo \$m | tr . /).lean
X=""; case \$m in GroundTheory.LocalFields.*|GroundTheory.GlobalFields.*) X="-DsynthInstance.maxHeartbeats=400000";; esac
t0=\$(date +%s.%N)
LEAN_PATH=$LP timeout $TO $TC/bin/lean --tstack=400000 -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true -DmaxHeartbeats=4000000 \$X -Dlinter.all=false $* -R $SRC -o $O/olean/\$m.olean \$f > $O/log/\$m.log 2>&1
rc=\$?; t1=\$(date +%s.%N)
rm -f $O/olean/\$m.olean
printf '%s\t%s\t%.1f\n' \$m \$rc \$(echo "\$t1 - \$t0" | bc)
EOS
chmod +x $O/one.sh
$H/sandbox_ro.sh $O $SRC:$B:$L -- bash -c "cat $L | xargs -P $J -n 1 $O/one.sh > $O/res.tsv"
awk -F'\t' '{n++; if($2==0) ok++} END {print "modules", n, "ok", ok}' $O/res.tsv
