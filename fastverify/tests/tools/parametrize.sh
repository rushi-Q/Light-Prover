#!/bin/bash
# parametrize.sh : make the OFFICIAL-flow scripts of the test snapshots read the official tool locations from the variables
# set by lib/paths.sh (FV_T33, FV_T36, FV_OFFICIAL_EXPORTER, FV_PACKAGES; derived from config/components.json), keeping this
# installation's paths as fallbacks (no behaviour change here). Idempotent; already applied to the snapshots in this
# repository - run it again after adding a snapshot of a new finding.
set -eu
T=$(cd "$(dirname "$0")/.." && pwd)
find "$T" -path "$T/results" -prune -o -type f \( -name 'officialflow*.sh' -o -name 'gen-bv.sh' \) -print | while read -r f; do
  sed -i -E \
    -e 's#(^|[ ;])T33=\$HOME/\.elan/toolchains/leanprover--lean4---v4\.33\.1#\1T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}#' \
    -e 's#(^|[ ;])T36=\$HOME/\.elan/toolchains/leanprover--lean4---v4\.36\.0#\1T36=${FV_T36:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}#' \
    -e 's#(^|[ ;])EXP=\$R/env/tools/lean4export/\.lake/build/bin/lean4export#\1EXP=${FV_OFFICIAL_EXPORTER:-$R/env/tools/lean4export/.lake/build/bin/lean4export}#' \
    -e 's#(^|[ ;])EXP=$LIGHT_LEAN/env/tools/lean4export/\.lake/build/bin/lean4export#\1EXP=${FV_OFFICIAL_EXPORTER:-$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export}#' \
    -e 's#(^|[ ;])PK=\$R/verify/challenge/\.lake/packages#\1PK=${FV_PACKAGES:-$R/verify/challenge}/.lake/packages#' "$f"
  bash -n "$f"
done
grep -rlE 'FV_T33|FV_OFFICIAL_EXPORTER' --include='officialflow*.sh' "$T" | wc -l
