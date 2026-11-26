#!/bin/bash
# mk_midmut.sh [RHMID_EXPORT] [OUTDIR] : two rh-mid mutants for the thread matrix (specs/midM1.spec = first, midM2.spec = last
# theorem outside the challenge, value := its own type; made by tools/mk_thm_mutant_spec.py from the rh-mid reference export)
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
E=${1:-/scratch/bench-inputs/rh-mid/ref/solution.export}; O=${2:-$W/midmut}; mkdir -p "$O"; F=$(fvmut_bin) || exit 2
for m in midM1 midM2; do [ -s "$O/$m.export" ] || "$F" "$E" "$O/$m.export" "$HERE/specs/$m.spec" --threads 8 || exit 1; done
