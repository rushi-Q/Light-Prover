#!/bin/bash
# gen-late.sh OUT : rh-mid reference export + ONE trailing sparse-index string line (legal for the official reader; forces
# FastParse's late decline -> official re-parse in ccmp and pleanchecker; finding 039 part 2)
cp /scratch/bench-inputs/rh-mid/ref/solution.export "$1" && echo '{"in":999999999,"str":{"pre":0,"str":"zzzLateSparse"}}' >> "$1"
