#!/bin/sh
# incwd.sh H GRUSZKA (inside krun; /tmp is private): the SAME check B commands (harness run line: kcompare/with-kernel.sh +
# allof.sh + arena-run(gruszka) + nl-fast -q -j T), the SAME files, started from different working directories.
H=$1; G=$2; DK=/scratch/fastverify/checkers/dualkernel; NL=$DK/target/release/nl-fast
CH=$H/challenge.export; SOL=$H/solution.export
B() { sh $DK/kcompare/with-kernel.sh $DK/target/release/kcompare $CH $SOL 4 -- sh $DK/kcompare/allof.sh -- env K02_THP=1 SUSZ=$DK/target/release/susz GRUSZKA=$G sh $DK/scripts/arena-run $SOL 4 :: $NL -q -j 4 $SOL > out.log 2>&1; r=$?
      echo "exit $r  ($(grep -E '^allof: pid' out.log | sed 's/allof: pid [0-9]* //' | tr '\n' ' ')| $(grep with-kernel out.log))"; }
mkdir -p /tmp/clean /tmp/steps /tmp/bad /tmp/core /tmp/cache
cd /tmp/clean; echo "FAST B dual, cwd without nano-lean.toml                 : $(B)"
cd /tmp/steps; printf 'steps = 1\n' > nano-lean.toml
echo "FAST B dual, cwd with nano-lean.toml 'steps = 1'          : $(B)"
cd /tmp/bad; printf 'threads = 0\n' > nano-lean.toml
echo "FAST B dual, cwd with nano-lean.toml 'threads = 0'        : $(B)   nl-fast says: $(grep -m1 nano-lean.toml out.log)"
cd /tmp/core; printf 'term_core = true\n' > nano-lean.toml; $NL -j 4 $SOL > o 2>&1
echo "nl-fast, cwd with 'term_core = true' (non-quiet)          : exit $?  $(grep -m1 -E 'experimental|attempted' o)"
cd /tmp/cache; printf 'cache = "verdicts.bin"\n' > nano-lean.toml
$NL -j 4 $SOL > o1 2>&1; r1=$?; $NL -j 4 $SOL > o2 2>&1; r2=$?
echo "nl-fast, cwd with 'cache = \"verdicts.bin\"', run 1         : exit $r1  $(grep -E 'cache [0-9]+ hits' o1)"
echo "nl-fast, same cwd, run 2 (cache file from run 1)          : exit $r2  $(grep -E 'cache [0-9]+ hits' o2)  <- definitions/theorems taken as accepted, not checked"
echo "  verdicts.bin: $(stat -c %s verdicts.bin) bytes, created by nl-fast in the cwd"
