#!/bin/bash
# setup.sh : node-local preparation of the export-fuzz tools: the bulk variant of check-sound.sh ($W/check-sound-bulk.sh,
# from the package under test; verified by the unmodified script's --preflight first), the parser-differential binary
# ($W/pd), and the base projects ($W/bases, built with the package's OFFICIAL flow --preset reference).
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
"$FV/check/sound/check-sound.sh" --preflight > /dev/null || { echo "setup: check-sound.sh --preflight failed" >&2; exit 2; }
python3 -I "$H/mkbulk.py" "$FV/check/sound/check-sound.sh" "$W/check-sound-bulk.sh" && chmod 755 "$W/check-sound-bulk.sh"
[ -x "$W/pd/.lake/build/bin/parsediff" ] || bash "$H/parsediff/build.sh" "$W/pd" > "$W/pd.build.log" 2>&1 || { echo "setup: parsediff build failed ($W/pd.build.log)" >&2; exit 2; }
bash "$H/bases/mk.sh" ${BASES:-ind quot lit univ hole}
echo "setup: ok ($W)"
