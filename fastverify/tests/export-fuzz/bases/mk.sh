#!/bin/bash
# bases/mk.sh NAME... : write the base projects (bases/mkbases.py) and build each with the package's OFFICIAL flow
# (--preset reference: sandboxed official lake build, official lean4export, official lake comparator) into $W/bases/NAME/out.
# Skips a base whose export exists. Every base must be ACCEPTED officially.
set -u
. "$(dirname "$(readlink -f "$0")")/../common.sh"
B=$W/bases; python3 -I "$H/bases/mkbases.py" "$B"
rc=0
for n in "$@"; do
  [ -f "$B/$n/out/solution.export" ] && continue
  rm -rf "$B/$n/out"
  "$FV/bin/fastverify" "$B/$n/solution" "$B/$n/challenge" "$B/$n/out" --preset reference --threads 8 > "$B/$n/fv.log" 2>&1
  v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$B/$n/out/result.json" 2>/dev/null)
  echo "base $n: official verdict ${v:-NONE}"; [ "$v" = ACCEPTED ] || rc=1
done
exit $rc
