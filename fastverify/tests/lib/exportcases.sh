#!/bin/bash
# exportcases.sh TESTDIR WORK -- exporter regression: the package's export stage vs the OFFICIAL lean4export v4.33.0 on the
# SAME .olean files. Cases: TESTDIR/ECASES, one per line ('#' comments), fields separated by '|':
#   name | sources | lean flags | root modules | targets
#   * sources: .lean files (relative to TESTDIR/x/) compiled IN ORDER with the official Lean 4.33.1 into one directory
#     (a file that fails to compile simply leaves no .olean: the case then tests the exporters on what exists)
#   * lean flags: extra flags for that compilation, e.g. -Ddebug.skipKernelTC=true (oleans the old fast build produced)
#   * targets: constant names, or @rh = the RH challenge's export-targets.txt
# The package side is export/export.sh --official-fallback (native first; any decline -> official exporter). Verdicts:
#   PASS         both exit 0 with byte-identical output, or both fail
#   FAIL-EXPORT  both exit 0, outputs differ                  FAIL  the package exports where the official exporter fails
#   PASS-DECLINE / WARN-DECLINE: export.sh exit 2 (could not run) where the official fails / succeeds
# Output: '=== RESULT case=... official=.. fast=.. osha=.. fsha=..' lines -> lib/parse.py.
{ # whole script parsed before it runs (safe against edits while running)
set -u
H=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd); FVROOT=${FV_ROOT:-$(cd "$H/../.." && pwd)}
TD=$(cd "$1" && pwd); W=$2; id=$(basename "$TD"); case $id in [0-9][0-9][0-9]-*) id=${id:0:3};; esac; X=$TD/x
mkdir -p "$W"; W=$(readlink -f "$W"); L=$W.log; : > "$L"
T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
OFFEXP=${FV_OFFICIAL_EXPORTER:-$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export}
EXS=${FV_EXPORT_STAGE:-$FVROOT/export/export.sh}
RHT=$LIGHT_LEAN/verify/challenge/export-targets.txt
trim() { local s=$1; s=${s#"${s%%[![:space:]]*}"}; s=${s%"${s##*[![:space:]]}"}; printf '%s' "$s"; }
sha() { [ -s "$1" ] && sha256sum < "$1" | cut -c1-16 || echo -; }
n=0
while IFS='|' read -r name srcs flags mods tg <&3; do
  name=$(trim "$name"); case $name in ''|'#'*) continue;; esac
  srcs=$(trim "$srcs"); flags=$(trim "$flags"); mods=$(trim "$mods"); tg=$(trim "$tg")
  n=$((n+1)); C=$W/c$n; mkdir -p "$C/b"; echo "##### $name  (sources=$srcs flags=$flags roots=$mods targets=$tg)" >> "$L"
  for s in $srcs; do cp "$X/$s" "$C/b/"; done
  ( cd "$C/b" && for s in $srcs; do m=${s##*/}; m=${m%.lean}
      env -i HOME="$HOME" PATH="$T33/bin:/usr/bin:/bin" LEAN_PATH="$C/b:$T33/lib/lean" lean $flags -o "$m.olean" "$m.lean" > "$m.log" 2>&1
      echo "  compile $m: rc=$? $(grep -m1 -o 'error: .*' "$m.log" | cut -c1-120)"; done ) >> "$L" 2>&1 < /dev/null
  [ "$tg" = @rh ] && tg=$(cat "$RHT")
  printf '%s\n' $tg > "$C/targets.txt"
  (cd "$C/b" && env -i HOME="$HOME" PATH="$T33/bin:/usr/bin:/bin" LEAN_PATH="$C/b:$T33/lib/lean" LEAN_ABORT_ON_PANIC=1 \
     "$OFFEXP" $mods -- $tg > "$C/off.export" 2> "$C/off.err" < /dev/null); o=$?
  echo "  official lean4export: exit $o $(sha "$C/off.export") $(grep -m1 -oE '(error|import|PANIC).*' "$C/off.err" | cut -c1-120)" >> "$L"
  [ $o = 0 ] || o=1
  if [ ! -x "$EXS" ]; then echo "=== RESULT case=$name official=$o fast=3" >> "$L"; continue; fi
  (cd "$C" && env -i HOME="$HOME" PATH=/usr/bin:/bin "$EXS" --lean-path "$C/b:$T33/lib/lean" --module "$mods" \
     --targets-file "$C/targets.txt" --toolchain "$T33" --project "$C/b" --out "$C/pkg.export" --official-fallback \
     --threads "${EVAL_THREADS:-8}" --json "$C/pkg.json" > "$C/pkg.out" 2>&1 < /dev/null); f=$?
  echo "  package export.sh: exit $f $(sha "$C/pkg.export") $(tail -c 400 "$C/pkg.out" | tr '\n' ' ')" >> "$L"
  case $f in 0|1|2) ;; *) f=E$f;; esac
  os=-; fs=-; [ $o = 0 ] && os=$(sha "$C/off.export"); [ "$f" = 0 ] && fs=$(sha "$C/pkg.export")
  echo "=== RESULT case=$name official=$o fast=$f osha=$os fsha=$fs" >> "$L"
done 3< "$TD/ECASES"
python3 -I "$H/parse.py" "$id" "$L" | tee "$W.tsv"
[ -n "${KEEP_WORK:-}" ] || rm -rf "$W"
! cut -f7 "$W.tsv" | grep -qE '^(FAIL|ERROR)'
exit $?
}
