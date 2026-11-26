#!/bin/sh
# with-kernel.sh — full comparator-equivalent verdict = an external kernel AND kcompare, run concurrently.
#
#   with-kernel.sh KCOMPARE CHALLENGE EXPORT KC_THREADS -- KERNEL_CMD [ARGS...]
#
# CHALLENGE empty, or EXPORT inside the arena/suitex corpus: only the kernel runs (exec).
# Otherwise kcompare checks EXPORT against CHALLENGE (theorems from $KC_THEOREMS, default: the five RH names;
# permitted axioms from $KC_AXIOMS, default propext,Quot.sound,Classical.choice) while the kernel checks the
# whole export. Exit: 0 iff both accept; 1 if either rejects; otherwise 2 (decline / error).
set -u
kc=$1; ch=$2; ex=$3; kt=$4; shift 4
[ "${1:-}" = "--" ] && shift
# No challenge, or a kernel-corpus file (the harness's arena/suitex gate passes the check-mid {challenge} to every
# corpus test, but those files are kernel tests labelled by leanchecker alone and contain no challenge theorems):
# the kernel alone decides.
case "$ex" in */arena/suite/*|*/inputs/suitex/*) ch="" ;; esac
if [ -z "$ch" ]; then exec "$@"; fi
th=${KC_THEOREMS:-riemannHypothesis,riemannZeta_eq_zero_re,LFunction_ne_zero_of_half_lt_re,LFunction_eq_zero_re,LFunction_eq_zero_re_of_isPrimitive}
ax=${KC_AXIOMS:-propext,Quot.sound,Classical.choice}
"$kc" -j "$kt" --challenge "$ch" --theorems "$th" --axioms "$ax" "$ex" &
kpid=$!
"$@"
k=$?
wait $kpid
c=$?
echo "with-kernel: kernel exit $k, kcompare exit $c" >&2
if [ $k -eq 0 ] && [ $c -eq 0 ]; then exit 0; fi
if [ $k -eq 1 ] || [ $c -eq 1 ]; then exit 1; fi
exit 2
