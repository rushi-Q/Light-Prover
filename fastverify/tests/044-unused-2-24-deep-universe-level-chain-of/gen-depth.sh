#!/bin/bash
# gen-depth.sh OUT [N]: x/Main.export (official build of theorem main_thm : True) + N unused level records forming one succ
# chain (x/deeplevel.py). N = 2^24 (default): the official export parser panics -> official REJECTS. N = 2^24-2: accepted.
H=$(cd "$(dirname "$0")" && pwd); python3 -I "$H/x/deeplevel.py" "$H/x/Main.export" "${2:-16777216}" "$1"
