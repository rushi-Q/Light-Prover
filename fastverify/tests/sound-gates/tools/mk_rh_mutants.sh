#!/bin/bash
# mk_rh_mutants.sh HONEST_EXPORT OUTDIR : the RH mutants M1-M4 (specs/M1.spec-M4.spec) from the
# honest 61.6 GB RH export (sha256 5ea74b91...be244e). On XFS with reflinks M1/M2/M4 cost no space (copy_file_range);
# M3 renumbers 687 M lines (full copy). The results must have the published sha256 (checked here).
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
H=${1:?honest export}; O=${2:?outdir}; mkdir -p "$O"; F=$(fvmut_bin) || exit 2
declare -A WANT=([M1]=d969870f99ebd03dbbb3b941f398a6e06146803af528c6360f3748172227d18f [M2]=dd47080add75f99a0c1ed28c26f33bf3a14f4b1147818bcda1f76d4528904c93
                 [M3]=9478e9e0721ef33926ae048a2b5b5d92d71959910de147434f97019bedfc58a2 [M4]=33117ee20cc28dc94ad771dce0777680eaa3a4d54933cfb3b98b670c9554c5fc)
for m in M1 M2 M4 M3; do "$F" "$H" "$O/$m.export" "$HERE/specs/$m.spec" --threads "${SLOT_CORES:-16}" || { echo "fvmut $m FAILED"; exit 1; }; done
bad=0
for m in M1 M2 M3 M4; do ( s=$(sha256sum "$O/$m.export" | cut -d' ' -f1); [ "$s" = "${WANT[$m]}" ] && echo "$m sha256 OK" || echo "$m sha256 MISMATCH $s" ) & done; wait
