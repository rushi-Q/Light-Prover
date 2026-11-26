#!/bin/sh
# RUN (kind kernel-src):  sh {src}/run.sh {src} {export} {threads} {challenge}
# (C01 copy of C02's ccmp run.sh @9e0f535; only change: CCMP_LEANCHECKER defaults to C01's pleanchecker)
# (C08: CCMP_LEANCHECKER defaults to pleanchecker-k = the same pleanchecker linked against the k/src kernel, see build_k.sh)
#  * check-mid main run (a challenge is given and EXPORT is not a corpus test): ccmp = the official 4.36 comparator logic with the
#    statement/axiom comparison, nanoda and the Lean kernel replay running CONCURRENTLY (verdict = conjunction, unchanged checks);
#    kernels = the OFFICIAL 4.36 binaries (leanchecker, nanoda_bin; nanoda with THREADS-2 threads via the comparator-generated
#    config, field nanoda_threads). No inner bwrap: the harness's ksandbox already isolates the run.
#  * otherwise (suite/suitex soundness-gate tests, which the harness runs with the check-mid challenge; check-mathlib): kernel-only
#    verdict of the Lean kernel replay ($CCMP_LEANCHECKER or the official leanchecker --from-export EXPORT).
# exit 0 = accept, 1 = reject, 2 = could not run.
S=$1; E=$2; T=${3:-32}; C=${4:-}
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
export PATH=$TC/bin:/usr/bin:/bin
# C07: nanoda_bin resolves to C07's nanoda build (official 4c544ed + speedups, same config/verdict logic) instead of the toolchain's
export PATH=$S/target/release:$PATH
# as the official comparator does for every kernel (Check.lean envOverride): a panic aborts (=> reject) instead of continuing
# with a default value; also covers the kernel-only branch below (suite/suitex gate, check-mathlib). Suggested by C03.
export LEAN_ABORT_ON_PANIC=1
# C01: the Lean kernel replay is C01's parallel leanchecker (pleanchecker, PChk/Par.lean; official kernel, parallel replay)
export CCMP_LEANCHECKER=${CCMP_LEANCHECKER:-$S/.lake/build/bin/pleanchecker-k}
# bound Lean's default task pool (FastParse tokenizers, ccmp tasks) to the slot instead of all online CPUs
export LEAN_NUM_THREADS=$T
# phase timings of pleanchecker on stderr (diagnostics only)
export PCHK_VERBOSE=1
LC=$CCMP_LEANCHECKER
case "$E" in */arena/suite/*|*/suitex/*) C= ;; esac
if [ -z "$C" ]; then
  "$LC" --from-export "$E"; rc=$?
  [ $rc -le 1 ] && exit $rc; exit 1
fi
W=$(mktemp -d) && cd "$W" || exit 2
# the comparator resolves git/env/kernels with `which`, a symlink into /etc/alternatives, which the harness sandbox does not
# bind: provide the POSIX equivalent (`command -v`) on PATH.
mkdir -p "$W/bin" && printf '#!/bin/sh\ncommand -v "$1"\n' > "$W/bin/which" && chmod +x "$W/bin/which" && export PATH="$W/bin:$PATH"
# C01 (opt-in, scheduling only): PCHK_NICE=N runs the Lean-kernel replay at nice N, so the CPU goes to nanoda (the critical
# path) first and the Lean kernel fills idle cores. Same binary, same arguments; only the process priority differs.
if [ -n "${PCHK_NICE:-}" ]; then
  printf '#!/bin/sh\nexec nice -n %s "%s" "$@"\n' "$PCHK_NICE" "$CCMP_LEANCHECKER" > "$W/bin/plc" && chmod +x "$W/bin/plc"
  export CCMP_LEANCHECKER="$W/bin/plc"
fi
NT=$((T > 4 ? T - 2 : 2))
cat > comparator.json <<JSON
{"challenge_module": "Challenge", "solution_module": "Main",
 "theorem_names": ["riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
                   "LFunction_eq_zero_re_of_isPrimitive"],
 "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
 "external_kernels": {"nanoda": ["nanoda_bin"]}, "nanoda_threads": $NT}
JSON
date -u +"%T ccmp start (nanoda_threads $NT)"
"$S/.lake/build/bin/ccmp" "$TC" comparator.json "$C" "$E"; rc=$?
date -u +"%T ccmp end rc=$rc"
exit $rc
