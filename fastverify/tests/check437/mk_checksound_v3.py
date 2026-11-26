#!/usr/bin/python3 -I
"""mk_checksound_v3.py LIVE_check-sound.sh OUT  - the '--pins FILE' generalization of the trusted wiring (v3): exact,
reviewable replacements on the live v2 script; every pattern must match exactly once. Default behaviour (no --pins) is
byte-for-byte the same decision logic: only the version strings read from the pins file become variables, with the 4.36
defaults when the pins file does not set them."""
import sys
s = open(sys.argv[1], encoding="utf-8").read()
def rep(old, new, count=1):
    global s
    n = s.count(old)
    assert n == count, (n, old[:90])
    s = s.replace(old, new)
rep("""#   check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S]
#                  [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs]
#   check-sound.sh --preflight""", """#   check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S]
#                  [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs]
#                  [--pins FILE]
#   check-sound.sh --preflight [--pins FILE]
#
# v3 (decision logic UNCHANGED): `--pins FILE` selects another pins file of the same format, so the
#   same wiring can run the trusted check built from ANOTHER official Lean release (check/sound/pins-437.env: the official
#   v4.37.0-rc1 comparator judge code + kernel, for projects on 4.37.0-rc1). A pins file may set TC_VERSION (the elan name of
#   the official toolchain its judge binaries were built from; verified against fastverify/toolchains on every run; default
#   leanprover/lean4:v4.36.0) and TC_LABEL (text of the verdict basis; default 4.36). The pins file's path and sha256 go into
#   the JSON result (`pins`, `pins_sha256`, `toolchain`). Without --pins nothing changes.""")
rep("WIRING=check-sound-v2-D08   # the wiring version of this script (the pins' SOUND_VERSION describes the binaries)",
    "WIRING=check-sound-v2.1-D23   # the wiring version of this script (the pins' SOUND_VERSION describes the binaries)")
# finish(): record the pins file and the toolchain
rep("""  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s}\\n' \\
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \\
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}")""",
"""  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s,"pins":%s,"pins_sha256":%s,"toolchain":%s}\\n' \\
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \\
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}" \\
    "$(json_str "${PINS:-}")" "$(json_str "${PINS_SHA:-}")" "$(json_str "${TC_VERSION:-}")")""")
# arguments
rep("""if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; set -- "$HERE/pins.env" "$HERE/pins.env" "$HERE/pins.env" "$@"; fi
[ $# -ge 3 ] || { echo "usage: check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs] | --preflight" >&2; decline "usage"; }
E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0
while [ $# -gt 0 ]; do
  case "$1" in
    --private-inputs) PRIVIN=1; shift;;""", """if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; set -- "$HERE/pins.env" "$HERE/pins.env" "$HERE/pins.env" "$@"; fi
[ $# -ge 3 ] || { echo "usage: check-sound.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs] [--pins FILE] | --preflight [--pins FILE]" >&2; decline "usage"; }
E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0; PINSOPT=
while [ $# -gt 0 ]; do
  case "$1" in
    --private-inputs) PRIVIN=1; shift;;
    --pins) PINSOPT=${2:-}; shift 2 || decline "--pins needs a value";;""")
# pins file selection + toolchain version
rep("""# ---------- pinned components: pins.env = SOUND_VERSION, TC36 and lines "PIN <name> <sha256> <path>" ----------
PINS=$HERE/pins.env
[ -f "$PINS" ] || decline "missing $PINS"
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS" | head -1)
TC36=$(sed -n 's/^TC36=//p' "$PINS" | head -1)""", """# ---------- pinned components: pins.env = SOUND_VERSION, TC36 and lines "PIN <name> <sha256> <path>" ----------
# v3: `--pins FILE` = another pins file of the same format (absolute path; recorded with its sha256 in the JSON result);
# optional lines TC_VERSION=leanprover/lean4:vX (the official release the judge binaries were built from; the toolchain at
# TC36 must verify against fastverify/toolchains/<that release>.json) and TC_LABEL=X (text of the verdict basis).
PINS=$HERE/pins.env
if [ -n "$PINSOPT" ]; then
  case "$PINSOPT" in /*) ;; *) decline "--pins must be an absolute path";; esac
  PINS=$(readlink -f -- "$PINSOPT") || decline "cannot resolve --pins '$PINSOPT'"
fi
[ -f "$PINS" ] || decline "missing $PINS"
PINS_SHA=$(sha256sum "$PINS" | cut -d' ' -f1)
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS" | head -1)
TC_VERSION=$(sed -n 's/^TC_VERSION=//p' "$PINS" | head -1); [ -n "$TC_VERSION" ] || TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=$(sed -n 's/^TC_LABEL=//p' "$PINS" | head -1); [ -n "$TC_LABEL" ] || TC_LABEL=4.36
case "$TC_VERSION" in leanprover/lean4:v[0-9]*) ;; *) decline "pins: TC_VERSION must name an official release (leanprover/lean4:vX)";; esac
TC36=$(sed -n 's/^TC36=//p' "$PINS" | head -1)""")
rep("""[ -n "$TC36" ] && [ -d "$TC36" ] || decline "official Lean 4.36 toolchain not found ($TC36)\"""",
    """[ -n "$TC36" ] && [ -d "$TC36" ] || decline "official Lean $TC_LABEL toolchain not found ($TC36)\"""")
rep("""/usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" leanprover/lean4:v4.36.0 > /dev/null 2>&1 \\
  || decline "the official Lean 4.36 toolchain at $TC36 does not verify against fastverify/toolchains\"""",
    """/usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" "$TC_VERSION" > /dev/null 2>&1 \\
  || decline "the official Lean $TC_LABEL toolchain at $TC36 does not verify against fastverify/toolchains ($TC_VERSION)\"""")
rep("""BASIS="challenge export as given (sha256 checked by the caller); statements + axioms: official Lean 4.36 comparator judge code (ccmp compareAt + checkAxioms); kernel 1: official Lean 4.36 kernel libraries (pleanchecker parallel Lean.Replay walk${INCR:+, incremental/overlapped with the build (PChk/Incr.lean)}); kernel 2: gruszka (independent)\"""",
    """BASIS="challenge export as given (sha256 checked by the caller); statements + axioms: official Lean $TC_LABEL comparator judge code (ccmp compareAt + checkAxioms); kernel 1: official Lean $TC_LABEL kernel libraries (pleanchecker parallel Lean.Replay walk${INCR:+, incremental/overlapped with the build (PChk/Incr.lean)}); kernel 2: gruszka (independent)\"""")
rep("""finish 0 ACCEPTED "statements + axioms match the challenge (official judge code); the official Lean 4.36 kernel (parallel replay) and the independent kernel gruszka accept every declaration of the export\"""",
    """finish 0 ACCEPTED "statements + axioms match the challenge (official judge code); the official Lean $TC_LABEL kernel (parallel replay) and the independent kernel gruszka accept every declaration of the export\"""")

# 5. the pins file is parsed from a PRIVATE COPY whose sha256 is the recorded one
rep("""[ -f "$PINS" ] || decline "missing $PINS"
PINS_SHA=$(sha256sum "$PINS" | cut -d' ' -f1)
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS" | head -1)
TC_VERSION=$(sed -n 's/^TC_VERSION=//p' "$PINS" | head -1); [ -n "$TC_VERSION" ] || TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=$(sed -n 's/^TC_LABEL=//p' "$PINS" | head -1); [ -n "$TC_LABEL" ] || TC_LABEL=4.36
case "$TC_VERSION" in leanprover/lean4:v[0-9]*) ;; *) decline "pins: TC_VERSION must name an official release (leanprover/lean4:vX)";; esac
TC36=$(sed -n 's/^TC36=//p' "$PINS" | head -1)
if [ "$TC36" = @components ]; then
  TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' \\
         "$PKGROOT/config/components.json" 2>/dev/null) || decline "cannot read comparator.prefix from config/components.json"
fi""", """[ -f "$PINS" ] || decline "missing $PINS"
# the pins file is read ONCE into a private copy; everything below parses the copy and the recorded sha256 is the copy's
# (nothing can change what was parsed after the fact)
PINS_PRIV=$(mktemp "${TMPDIR:-/tmp}/checkSound-pins.XXXXXX") || decline "cannot create a private copy of the pins file"
cp -- "$PINS" "$PINS_PRIV" || decline "cannot copy the pins file"
PINS_SHA=$(sha256sum "$PINS_PRIV" | cut -d' ' -f1)
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS_PRIV" | head -1)
TC_VERSION=$(sed -n 's/^TC_VERSION=//p' "$PINS_PRIV" | head -1); [ -n "$TC_VERSION" ] || TC_VERSION=leanprover/lean4:v4.36.0
TC_LABEL=$(sed -n 's/^TC_LABEL=//p' "$PINS_PRIV" | head -1); [ -n "$TC_LABEL" ] || TC_LABEL=4.36
case "$TC_VERSION" in leanprover/lean4:v[0-9]*) ;; *) decline "pins: TC_VERSION must name an official release (leanprover/lean4:vX)";; esac
TC36=$(sed -n 's/^TC36=//p' "$PINS_PRIV" | head -1)
if [ "$TC36" = @components ]; then
  # the package's registered toolchain of TC_VERSION: comparator.prefix for the default 4.36 (as before), otherwise the
  # lean_toolchains entry of config/components.json (written by tools/addrelease.py); verified below like any other path
  TC36=$(/usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); v=sys.argv[2]
print(c["comparator"]["prefix"] if v == "leanprover/lean4:v4.36.0" else c["lean_toolchains"][v]["prefix"])' \\
         "$PKGROOT/config/components.json" "$TC_VERSION" 2>/dev/null) || decline "config/components.json has no toolchain prefix for $TC_VERSION"
fi""")
rep("""done < "$PINS"
BJ="{"; sep=""", """done < "$PINS_PRIV"
BJ="{"; sep=""")
rep("""  [ -n "$W" ] && rm -rf "$W"
  if [ "$FINISHED" != 1 ]; then""", """  [ -n "$W" ] && rm -rf "$W"
  [ -n "${PINS_PRIV:-}" ] && rm -f "$PINS_PRIV"
  if [ "$FINISHED" != 1 ]; then""")
rep("""# v3: `--pins FILE` = another pins file of the same format (absolute path; recorded with its sha256 in the JSON result);""",
    """# v2.1: `--pins FILE` = another pins file of the same format (absolute path; parsed from a private copy whose sha256 is recorded in the JSON result);""")


# 6. (v2.2): --hide FILE = the encapsulated replay's hide list (untrusted, availability-only, like --hints)
rep("""#                  [--pins FILE]
#   check-sound.sh --preflight [--pins FILE]""", """#                  [--pins FILE] [--hide FILE]
#   check-sound.sh --preflight [--pins FILE]
#
# v2.2 (decision logic UNCHANGED): `--hide FILE` hands the Lean-kernel leg a list of definitions (one name
#   per line, <= 16 MiB) for the ENCAPSULATED REPLAY of pleanchecker >= D23-E (PCHK_HIDE_FILE): those definitions and every
#   earlier theorem are visible to later kernel checks by their types only - the 4.37 module system's own view - and a kernel
#   error in that environment is re-checked in the full one, which decides. The list is an availability-only input (a wrong
#   list costs time, never a verdict; argument in check/sound/src-437/PChk/Par.lean, D23-E); it is copied into the private
#   work dir and recorded (path + sha256) in the JSON result as `hide`, `hide_sha256`. Without --hide: the plain replay.""")
rep("""    --pins) PINSOPT=${2:-}; shift 2 || decline "--pins needs a value";;""", """    --pins) PINSOPT=${2:-}; shift 2 || decline "--pins needs a value";;
    --hide) HIDE=${2:-}; shift 2 || decline "--hide needs a value";;""")
rep("""T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0; PINSOPT=""", """T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0; PINSOPT=; HIDE=; HIDE_SHA=""")
rep("""  cp -- "$HINTS" "$W/hints" || decline "cannot copy the hints file"
fi""", """  cp -- "$HINTS" "$W/hints" || decline "cannot copy the hints file"
fi
# v2.2: the hide list of the encapsulated replay (D23-E), same discipline as the hints
HIDEENV=
if [ -n "$HIDE" ]; then
  { [ -f "$HIDE" ] && [ "$(stat -c %s -- "$HIDE")" -le 16777216 ]; } || decline "--hide: not a regular file <= 16 MiB: '$HIDE'"
  cp -- "$HIDE" "$W/hide" || decline "cannot copy the hide list"
  HIDE_SHA=$(sha256sum "$W/hide" | cut -d' ' -f1); HIDEENV="PCHK_HIDE_FILE=\\"$W/hide\\" "
fi""")
rep("""PCHK_PRIO_FILE="$W/hints" PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=$PLC_STACK_KB "$2" -j$T -v $attach"\\$@" > "$W/tmp/leg-\\$N.log" 2>&1""",
    """${HIDEENV}PCHK_PRIO_FILE="$W/hints" PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=$PLC_STACK_KB "$2" -j$T -v $attach"\\$@" > "$W/tmp/leg-\\$N.log" 2>&1""")
rep("""  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s,"pins":%s,"pins_sha256":%s,"toolchain":%s}\\n' \\
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \\
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}" \\
    "$(json_str "${PINS:-}")" "$(json_str "${PINS_SHA:-}")" "$(json_str "${TC_VERSION:-}")")""",
    """  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s,"pins":%s,"pins_sha256":%s,"toolchain":%s,"hide":%s,"hide_sha256":%s}\\n' \\
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \\
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}" \\
    "$(json_str "${PINS:-}")" "$(json_str "${PINS_SHA:-}")" "$(json_str "${TC_VERSION:-}")" "$(json_str "${HIDE:-}")" "$(json_str "${HIDE_SHA:-}")")""")
rep("WIRING=check-sound-v2.1-D23   # the wiring version", "WIRING=check-sound-v2.2-D23   # the wiring version")

print("wrote", sys.argv[2])

# 7. the 16 MiB size caps of --hints and --hide must look through symlinks (`stat -L`; `[ -f ]`
#    already follows them), and the usage line names --hide. Availability-only; decision logic unchanged.
rep('''"$(stat -c %s -- "$HINTS")"''', '''"$(stat -L -c %s -- "$HINTS")"''')
rep('''"$(stat -c %s -- "$HIDE")"''', '''"$(stat -L -c %s -- "$HIDE")"''')
rep('''[--pins FILE] | --preflight [--pins FILE]" >&2; decline "usage"; }''', '''[--pins FILE] [--hide FILE] | --preflight [--pins FILE]" >&2; decline "usage"; }''')

open(sys.argv[2], "w", encoding="utf-8").write(s)
