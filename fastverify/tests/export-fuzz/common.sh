# sourced by the export-fuzz scripts: H (this directory), FV (package under test), W (node-local work dir), base_inputs()
H=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)
FV=${FV_UNDER_TEST:-$(cd "$H/../.." && pwd)}
W=${EXPORT_FUZZ_WORK:-${TMPDIR:-/tmp}/$USER-exportfuzz}
export EXPORT_FUZZ_WORK=$W
# optional extra base: the accept-base of the cmpx corpus against the rh-miniF mini challenge (a local mirror of the cmpx corpus)
CMPX_DIR=${CMPX_DIR:-${BENCH_INPUTS:-/scratch/bench-inputs}/cmpx}
RHMINI_CHALLENGE=${RHMINI_CHALLENGE:-/scratch/bench-inputs/rh-miniF/challenge}
mkdir -p "$W"
base_inputs() {  # base_inputs NAME -> sets SOL CH CFG (returns 1 if the base is not available here)
  if [ "$1" = cmpx ]; then
    SOL=$CMPX_DIR/accept-base.ndjson; CH=$RHMINI_CHALLENGE/challenge.export; CFG=$RHMINI_CHALLENGE/comparator.leanonly.json
  else
    SOL=$W/bases/$1/out/solution.export; CH=$W/bases/$1/out/challenge.export; CFG=$W/bases/$1/challenge/comparator.json
  fi
  [ -f "$SOL" ] && [ -f "$CH" ] && [ -f "$CFG" ]
}
targets_of() {  # targets_of CFG -> theorem + definition names + permitted axioms (comma separated)
  python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(",".join(c["theorem_names"]+c.get("definition_names",[])+c["permitted_axioms"]))' "$1"
}
