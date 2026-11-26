#!/bin/bash
# gen-chain.sh OUT [N] [PFX]: x/toy/good/solution.export + a chain of N kernel-valid definitions (x/chainapp.py). N=8,000,000
# PFX=x04c: replay DFS depth 4.2M -> the official replay walk overflows its stack (official REJECTS). ~1.5 GB, ~2 min.
H=$(cd "$(dirname "$0")" && pwd); python3 -I "$H/x/chainapp.py" "$H/x/toy/good/solution.export" "${2:-8000000}" "$1" 2 "${3:-x04c}"
