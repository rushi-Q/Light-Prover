#!/bin/bash
# fvbudget.sh CHALLENGE OUT --from-export FILE [fastverify args...]
#   export-in verification under THIS process's memory/CPU budget: reads the cgroup / host limits (lib/budget.py host),
#   estimates the trusted check's peak for the export's size and picks the largest thread count whose estimate fits
#   (with a 15 % margin), then runs `bin/fastverify - CHALLENGE OUT --preset sound --from-export FILE --threads T ...`.
#   Prints the plan first; exit code = fastverify's. If nothing fits, the run still starts at 1 thread (the check
#   itself DECLINES on an OOM kill - never a verdict) unless FVBUDGET_STRICT=1 (then exit 2 without running).
set -u
FV=${FV:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
[ $# -ge 4 ] && [ "$3" = --from-export ] || { sed -n '2,8p' "$0" >&2; exit 2; }
CHAL=$1; OUT=$2; EXP=$4; shift 4
SZ=$(stat -c %s -- "$EXP") || exit 2
PLAN=$(/usr/bin/python3 -I "$FV/lib/budget.py" plan "$SZ") || exit 2
T=$(printf '%s' "$PLAN" | /usr/bin/python3 -I -c 'import json,sys; print(json.load(sys.stdin)["threads"])')
FITS=$(printf '%s' "$PLAN" | /usr/bin/python3 -I -c 'import json,sys; print(json.load(sys.stdin)["fits"])')
echo "[fvbudget] export $SZ bytes; plan: $(printf '%s' "$PLAN" | tr -d '\n ' | cut -c1-200)" >&2
if [ "$FITS" != True ] && [ "${FVBUDGET_STRICT:-0}" = 1 ]; then echo "[fvbudget] does not fit the memory budget (strict mode): not started" >&2; exit 2; fi
exec "$FV/bin/fastverify" - "$CHAL" "$OUT" --preset sound --from-export "$EXP" --threads "$T" "$@"
