#!/bin/bash -p
# tests/env-isolation/run.sh [SCRIPT...] - regression test: the caller's environment must not be able to run code
# inside, or redirect, the trusted wiring scripts. For each script (default: every trusted bash entry point of the package)
# three hostile environments are tried on `--preflight` (cheap, no export needed); PASS iff no injected code ran.
#   (a) the script's own *_CLEAN_ENV marker + a PATH whose first entry holds a logging fake `sha256sum`
#   (b) BASH_ENV pointing at a logging file
#   (c) an exported shell function `readlink` (BASH_FUNC_readlink%%) that logs
# Prints PASS|FAIL rows and RESULT pass=N fail=M; exit 0 iff all PASS. Needs no network, writes only to a temp dir.
set -u
FV=${FASTVERIFY_ROOT:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
T=$(mktemp -d "${TMPDIR:-/tmp}/q01env.XXXXXX") || exit 2
trap 'rm -rf "$T"' EXIT
mkdir -p "$T/bin"
printf '#!/bin/sh\necho fake-sha256sum >> "%s/log"\nexec /usr/bin/sha256sum "$@"\n' "$T" > "$T/bin/sha256sum"; chmod +x "$T/bin/sha256sum"
printf 'echo bash-env >> "%s/log"\n' "$T" > "$T/bashenv"
if [ $# -eq 0 ]; then
  set -- "check/sound/check-sound.sh:CHECK_SOUND_CLEAN_ENV" "check/sound/check-sound-svc.sh:CHECK_SOUND_CLEAN_ENV" \
         "check/lowmem/check-sound-lowmem.sh:CHECK_SOUND_LOWMEM_CLEAN_ENV" "check/lowmem/check-sound-ultralowmem.sh:CHECK_SOUND_LOWMEM_CLEAN_ENV" \
         "check/notary/check-notary.sh:CHECK_NOTARY_CLEAN_ENV" "check/frontier/check-frontier.sh:CHECK_FRONTIER_CLEAN_ENV"
fi
pass=0; fail=0
row() { if [ "$2" = 0 ]; then echo "PASS $1"; pass=$((pass+1)); else echo "FAIL $1: injected code ran ($2 log lines)"; fail=$((fail+1)); fi; }
for spec in "$@"; do
  s=${spec%%:*}; m=${spec#*:}; S=$FV/$s
  [ -f "$S" ] || { echo "SKIP $s (missing)"; continue; }
  : > "$T/log"; env "$m=1" PATH="$T/bin:/usr/bin:/bin" "$S" --preflight > /dev/null 2>&1; row "$s marker+PATH" "$(wc -l < "$T/log")"
  : > "$T/log"; env BASH_ENV="$T/bashenv" "$S" --preflight > /dev/null 2>&1; row "$s BASH_ENV" "$(wc -l < "$T/log")"
  : > "$T/log"; env "BASH_FUNC_readlink%%=() { echo exported-fn >> $T/log; /usr/bin/readlink \"\$@\"; }" "$S" --preflight > /dev/null 2>&1
  row "$s exported function" "$(wc -l < "$T/log")"
done
echo "RESULT pass=$pass fail=$fail"
[ "$fail" = 0 ]
