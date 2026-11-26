#!/bin/bash
# run-dev.sh OUT PRESET [EXTRA ARGS] : rh-mid through bin/fastverify on this host (FASTVERIFY_BIN, RHMID, WS overridable)
set -u
OUT=$1; P=$2; shift 2
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FVB=${FASTVERIFY_BIN:-$H/../../bin/fastverify}; R=${RHMID:-/scratch/bench-inputs/rh-mid}
S=$(mktemp -d "${TMPSRC:-/scratch}/rhmid-src.XXXXXX"); cp -a "$R/pristine/." "$S/"; cp "$H/lakefile.toml" "$S/lakefile.toml"; touch -d @0 "$S/lakefile.toml"
A=(); [ "$P" = sound ] && A=(--challenge-sha256 851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9)
"$FVB" "$S" "$R/challenge" "$OUT" --preset "$P" --threads "${THREADS:-$(nproc)}" --packages "${WS:-${FV_PACKAGES:-$H/../../../verify/challenge}}" "${A[@]}" "$@"
rc=$?; rm -rf "$S"; exit $rc
