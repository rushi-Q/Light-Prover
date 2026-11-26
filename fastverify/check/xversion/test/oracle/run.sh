#!/bin/bash
# tests/oracle/run.sh XVCHECK_PY EXPORT... : xvcheck.py's strict reader vs the OFFICIAL Lean reader (LeanExport.parseStream,
# identical in v4.36.0 and v4.37.0-rc1; ccmp's FastParse reproduces it). Needs the official toolchain (TC37; TC37=<4.36 prefix>
# runs the 4.36 reader). Contract checked: the official answer, or a refusal. Outcomes per export:
#   AGREE (both read, same tables) | XVCHECK-REFUSES-ONLY (stricter: no verdict) | BOTH-REFUSE  -> fine
#   DISAGREE (both read, different) | OFFICIAL-REFUSES-ONLY (official parse error or kernel abort, xvcheck reads) -> counted
#   ORACLE-ERROR (timeout or abnormal Lean exit that is neither a parse error nor a kernel abort) -> counted separately
# (official-only refusals and oracle execution failures must not pass silently)
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); XV=$1; shift
TC37=${TC37:-$HOME/.elan/toolchains/leanprover--lean4---v4.37.0-rc1}
[ -x "$TC37/bin/lean" ] || { echo "SKIP oracle (no official toolchain at $TC37)"; exit 0; }
W=$(mktemp -d /tmp/xv-oracle.XXXXXX); trap 'rm -rf "$W"' EXIT; fails=0; oerr=0; n=0
for e in "$@"; do
  n=$((n+1))
  env -i PATH="$TC37/bin:/usr/bin:/bin" HOME="$W" timeout 1200 "$TC37/bin/lean" --run "$H/OfficialDump.lean" "$e" "$W/d$n.jsonl" > "$W/o$n.log" 2>&1; orc=$?
  if [ "$orc" = 0 ]; then
    python3 -I "$H/compare_official.py" "$XV" "$e" "$W/d$n.jsonl" || fails=$((fails+1))
    continue
  fi
  if [ "$orc" = 1 ] && grep -q "uncaught exception:\|INTERNAL PANIC:" "$W/o$n.log"; then
    if python3 -I -c 'import importlib.util,sys
s=importlib.util.spec_from_file_location("x",sys.argv[1]); X=importlib.util.module_from_spec(s); s.loader.exec_module(X)
try:
    X.read_export(sys.argv[2]); sys.exit(1)
except X.ExportError: sys.exit(0)' "$XV" "$e"; then echo "BOTH-REFUSE $e ($(tail -1 "$W/o$n.log" | cut -c1-100))"
    else echo "OFFICIAL-REFUSES-ONLY $e ($(tail -1 "$W/o$n.log" | cut -c1-120)) - xvcheck read it: COUNTED"; fails=$((fails+1)); fi
  else
    echo "ORACLE-ERROR $e (official reader exit $orc: $(tail -1 "$W/o$n.log" | cut -c1-120))"; oerr=$((oerr+1))
  fi
done
echo "RESULT oracle: $n exports, $fails disagreements, $oerr oracle execution failures"; [ $fails = 0 ] && [ $oerr = 0 ]
