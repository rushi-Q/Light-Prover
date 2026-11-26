#!/bin/bash
# gen-bad.sh OUT: in/solution.export (official build) + in/append.ndjson (badThm : False := True with SPARSE indices)
cat "$(dirname "$0")/in/solution.export" "$(dirname "$0")/in/append.ndjson" > "$1"
