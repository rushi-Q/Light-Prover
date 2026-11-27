#!/bin/bash -p
# fastverify LOW-MEMORY SOUND CHECK (additive, default-off; satisfies soundness conditions (2)-(4) of docs/concepts/soundness.md).
#
#   check-sound-lowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE]
#                         [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none]
#                         [--incr-dir DIR] [--private-inputs] [--integrity-cache DIR] [--mem-budget-mb MB]
#   check-sound-lowmem.sh --preflight [--integrity-cache DIR]
# exit 0 = ACCEPTED, 1 = REJECTED, 2 = no verdict (DECLINED / could not run). Last stdout line = one JSON object.
#
# Design (see check/lowmem/README.md):
#   1. Two-pass low-memory comparison + axiom check (`ccmp-lowmem`, GLIBC_2.17): streams solution.export into lazy
#      MAP_NORESERVE constant-dependency CSR tables (never allocating persistent Lean.Expr heap objects for the
#      ~99.9%+ non-challenge proof terms), checks exact checkAxioms reachability, unmaps the DAG, selectively
#      materializes Lean.Expr ONLY for dom(challenge) u targets, and runs the UNMODIFIED official Lake.Check.compareAt.
#   2. Sequential isolated legs (`max` RSS across legs instead of `sum`):
#      Leg 1 (`compare`): ccmp-lowmem --compare-only in a clean bwrap sandbox -> exits, releasing 100% of RAM;
#      Leg 2 (`lean`):    official Lean 4.36 kernel (pleanchecker, or optional pleanchecker_lowmem pin) -> exits;
#      Leg 3 (`k2`):      independent second kernel (gruszka, or optional gruszka_lowmem pin) -> exits.
#      Any rejection in Leg 1 or Leg 2 short-circuits immediately (fast Day 1-99 feedback on sorry/statement drift!).
#   3. Budget-aware worker-thread capping (verdict-neutral): when `--mem-budget-mb MB` is passed or a finite cgroup v2
#      `memory.max` limit is detected, replay worker threads are capped proportionally so per-thread stacks & caches
#      never starve the cgroup; when unlimited, `--threads N` is used verbatim.
#   4. Hardened v2 leg-scoped verdict & private-inputs-by-default discipline (matching check-sound.sh v2): every leg
#      writes to its own log/rc file, ACCEPTED requires rc=0 + anchored acceptance markers of all 3 legs + selftest +
#      unchanged nanosecond ctime stamps + end-of-run pin sha256 verification. OOM (rc=137 / bad_alloc) -> DECLINED (2).
main() {
q01_env_clean() {  # exactly the clean environment (no caller-settable marker)
  local v
  for v in $(compgen -e); do case "$v" in PATH|LANG|PWD|OLDPWD|SHLVL|_) ;; *) return 1;; esac; done
  [ "$PATH" = /usr/bin:/bin ] && [ "${LANG:-}" = C.UTF-8 ]
}
if ! q01_env_clean; then
  if [ "${1:-}" = --clean-env-reexec ]; then
    printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"environment not clean after the env -i re-exec"}\n' "$(/usr/bin/basename "$0")"
    exit 2
  fi
  exec /usr/bin/env -i PATH=/usr/bin:/bin LANG=C.UTF-8 /bin/bash -p "$(/usr/bin/readlink -f "$0")" --clean-env-reexec "$@"
fi
if [ "${1:-}" = --clean-env-reexec ]; then shift; fi
# macOS: the legs of this script run natively, one after another: check/sound/macos/enter.py publishes the result of
# the driver judge.py, which performs every later step of this script itself (README.md there). It is entered only
# from the clean environment established above. Everything below is for Linux.
if [ "$(/usr/bin/uname -s 2>/dev/null)" = Darwin ]; then
  self=$(/usr/bin/readlink -f "$0") && [ -n "$self" ] && t=$(/usr/bin/python3 -I -c 'import atexit, os, sys; names = {"__name__": "enter", "__file__": sys.argv[1]}; atexit.register(os._exit, 1); exec(compile(open(sys.argv[1], "rb").read(), sys.argv[1], "exec"), names); done = names.get("COMPLETE") is True; print("COMPLETE" if done else "INCOMPLETE", flush=True); os._exit(0 if done else 1)' "${self%/*}/../sound/macos/enter.py") && [ "$t" = COMPLETE ] || { printf '%s\n' '{"checker":"checkSoundUltraLowMem","verdict":"DECLINED","exit":2,"reason":"cannot resolve the path of the judge script, start /usr/bin/python3 or load check/sound/macos/enter.py to its last statement"}'; exit 2; }
  exec /usr/bin/python3 -I "${self%/*}/../sound/macos/enter.py" ultralowmem "$@"
fi
set -u
umask 077
T_START=$(date +%s.%N)
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
PKGROOT=$(cd "$HERE/../.." && pwd)
SELF=checkSoundUltraLowMem
WIRING=check-sound-ultralowmem-v1-D11-D15
FINISHED=0; W=
on_exit() {
  local rc=$?
  [ -n "${ST_PID:-}" ] && kill "$ST_PID" 2>/dev/null && wait "$ST_PID" 2>/dev/null
  [ -n "$W" ] && rm -rf "$W"
  if [ "$FINISHED" != 1 ]; then
    printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc"
    [ -n "${JSONF:-}" ] && printf '{"checker":"%s","verdict":"DECLINED","exit":2,"reason":"internal error (exit %s)"}\n' "$SELF" "$rc" > "$JSONF" 2>/dev/null
    exit 2
  fi
}
trap on_exit EXIT
trap 'exit 2' INT TERM HUP
json_str() { /usr/bin/python3 -I -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$1"; }
LOGF=
log() { if [ -n "$LOGF" ]; then printf '%s\n' "$*" >> "$LOGF"; else printf '%s\n' "$*" >&2; fi; }
finish() {
  local ex=$1 v=$2 why=$3 now wall tj=null effj=null; now=$(date +%s.%N)
  wall=$(echo "$now - $T_START" | bc | sed 's/^\./0./')
  case "${T:-}" in ''|*[!0-9]*|0?*) ;; *) tj=$T;; esac   # a canonical decimal only (else null)
  case "${T_EFF:-}" in ''|*[!0-9]*|0?*) ;; *) effj=$T_EFF;; esac
  log "[$SELF] verdict $v (exit $ex): $why"
  local js; js=$(printf '{"checker":"%s","verdict":"%s","exit":%s,"wall_s":%s,"reason":%s,"ccmp_rc":%s,"threads":%s,"effective_threads":%s,"mode":"sequential-lowmem","version":%s,"wiring":"%s","basis":%s,"binaries_sha256":%s,"leg_ms":%s,"legs":%s,"compare_ms":%s,"inputs":%s,"private_inputs_asserted":%s}\n' \
    "$SELF" "$v" "$ex" "$wall" "$(json_str "$why")" "${CCMP_RC:-null}" "$tj" "$effj" "$(json_str "${SOUND_VERSION:-unknown}")" "$WIRING" \
    "$(json_str "${BASIS:-}")" "${BIN_JSON:-null}" "${LEG_JSON:-null}" "${LEGS_JSON:-null}" "${COMPARE_MS:-null}" "${INPUTS_JSON:-null}" "${PRIVIN:-0}")
  printf '%s\n' "$js"
  if [ -n "${JSONF:-}" ]; then printf '%s\n' "$js" > "$JSONF" || true; fi
  FINISHED=1
  exit "$ex"
}
decline() { finish 2 DECLINED "$1"; }

# ---------- arguments ----------
PREFLIGHT=0
if [ "${1:-}" = --preflight ]; then PREFLIGHT=1; shift; set -- "$HERE/pins-ultralowmem.env" "$HERE/pins-ultralowmem.env" "$HERE/pins-ultralowmem.env" "$@"; fi
[ $# -ge 3 ] || { echo "usage: check-sound-lowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--log FILE] [--timeout S] [--workdir DIR] [--keep-config-kernels] [--hints FILE|none] [--incr-dir DIR] [--private-inputs] [--integrity-cache DIR] [--mem-budget-mb MB] | --preflight [--integrity-cache DIR]" >&2; decline "usage"; }
E_IN=$1; C_IN=$2; CFG_IN=$3; shift 3
T=; WD=; JSONF=; TMO=0; KEEPK=0; HINTS=; INCR=; PRIVIN=0; ICACHE=; MEM_MB=0
while [ $# -gt 0 ]; do
  case "$1" in
    --private-inputs) PRIVIN=1; shift;;
    --threads) T=${2:-}; shift 2 || decline "--threads needs a value";;
    --workdir) WD=${2:-}; shift 2 || decline "--workdir needs a value";;
    --json) JSONF=${2:-}; shift 2 || decline "--json needs a value";;
    --timeout) TMO=${2:-}; shift 2 || decline "--timeout needs a value";;
    --keep-config-kernels) KEEPK=1; shift;;
    --hints) HINTS=${2:-}; shift 2 || decline "--hints needs a value";;
    --incr-dir) INCR=${2:-}; shift 2 || decline "--incr-dir needs a value";;
    --integrity-cache) ICACHE=${2:-}; shift 2 || decline "--integrity-cache needs a value";;
    --mem-budget-mb) MEM_MB=${2:-}; shift 2 || decline "--mem-budget-mb needs a value";;
    --log) LOGF=${2:-}; shift 2 || decline "--log needs a value"; : > "$LOGF" || decline "cannot write log $LOGF";;
    --require-sorried-holes) Q02_RSH=1; shift;;   # Q02: the sorried-hole rule for every release (DECLINED if violated)
    --challenge-sha256) CSHA_PIN=${2:-}; shift 2 || decline "--challenge-sha256 needs a value"; [ -n "$CSHA_PIN" ] || decline "--challenge-sha256 needs a non-empty value";;
    --comparator-sha256) CFGSHA_PIN=${2:-}; shift 2 || decline "--comparator-sha256 needs a value"; [ -n "$CFGSHA_PIN" ] || decline "--comparator-sha256 needs a non-empty value";;
    *) decline "unknown argument '$1'";;
  esac
done
if [ -z "$T" ]; then T=$(nproc 2>/dev/null || echo 1); fi
case "$T" in ''|*[!0-9]*|0) decline "--threads must be a positive number";; esac
# numeric options become plain base-10 integers right after validation (at most 9
# digits; '08' -> 8): the JSON result never carries a zero-padded number and bash arithmetic never reads octal.
[ "${#T}" -le 9 ] || decline "--threads must be a positive number"; T=$((10#$T))
[ "$T" -ge 1 ] || decline "--threads must be a positive number"
case "$TMO" in ''|*[!0-9]*) decline "--timeout must be a number of seconds (0 = none)";; esac
[ "${#TMO}" -le 9 ] || decline "--timeout must be a number of seconds (0 = none)"; TMO=$((10#$TMO))
case "$MEM_MB" in ''|*[!0-9]*) decline "--mem-budget-mb must be a non-negative integer";; esac
[ "${#MEM_MB}" -le 9 ] || decline "--mem-budget-mb must be a non-negative integer"; MEM_MB=$((10#$MEM_MB))

# Detect cgroup v2 memory.max if MEM_MB not explicitly passed (verdict-neutral thread cap only)
if [ "$MEM_MB" = 0 ] && [ -r /proc/self/cgroup ]; then
  cgrel=$(sed -n 's/^0:://p' /proc/self/cgroup | head -1)
  while [ -n "$cgrel" ]; do
    if [ -r "/sys/fs/cgroup$cgrel/memory.max" ]; then
      cgmax=$(cat "/sys/fs/cgroup$cgrel/memory.max" 2>/dev/null || echo max)
      case "$cgmax" in ''|max|*[!0-9]*) ;; *)
        cgmb=$(( cgmax / 1048576 ))
        if [ "$cgmb" -gt 0 ] && { [ "$MEM_MB" = 0 ] || [ "$cgmb" -lt "$MEM_MB" ]; }; then MEM_MB=$cgmb; fi;;
      esac
    fi
    [ "$cgrel" = "/" ] && break
    cgrel=$(dirname "$cgrel")
  done
fi
T_EFF=$T
AS=$(ulimit -v)
if [ "$AS" != unlimited ]; then
  cap=$(( AS / 4194304 )); [ "$cap" -ge 1 ] || cap=1
  if [ "$T_EFF" -gt "$cap" ]; then log "[$SELF] address-space limit ${AS} KB: threads $T_EFF -> $cap"; T_EFF=$cap; fi
fi
if [ "$MEM_MB" -gt 0 ] && [ "$MEM_MB" -lt 65536 ]; then
  mcap=$(( MEM_MB / 256 )); [ "$mcap" -ge 1 ] || mcap=1
  if [ "$mcap" -gt 32 ]; then mcap=32; fi
  if [ "$T_EFF" -gt "$mcap" ]; then
    log "[$SELF] memory budget ${MEM_MB} MB: capping worker threads $T_EFF -> $mcap"
    T_EFF=$mcap
  fi
fi

for f in "$E_IN" "$C_IN" "$CFG_IN"; do
  [ -n "$f" ] || decline "empty input path"
  r=$(readlink -f -- "$f") || decline "cannot resolve '$f'"
  { [ -f "$r" ] && [ ! -p "$r" ] && [ ! -c "$r" ] && [ ! -b "$r" ] && [ ! -S "$r" ]; } || decline "input is not a regular file: '$f'"
done
E_IN=$(readlink -f -- "$E_IN"); C_IN=$(readlink -f -- "$C_IN"); CFG_IN=$(readlink -f -- "$CFG_IN")

# ---------- pinned components ----------
PINS=$HERE/pins-ultralowmem.env
[ -f "$PINS" ] || decline "missing $PINS"
SOUND_VERSION=$(sed -n 's/^SOUND_VERSION=//p' "$PINS" | head -1)
TC36=$(sed -n 's/^TC36=//p' "$PINS" | head -1)
if [ "$TC36" = @components ]; then
  TC36=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' \
         "$PKGROOT/config/components.json" 2>/dev/null) || decline "cannot read comparator.prefix from config/components.json"
fi
[ -n "$TC36" ] && [ -d "$TC36" ] || decline "official Lean 4.36 toolchain not found ($TC36)"
declare -A PIN_PATH PIN_SHA
while read -r tag name sum path; do
  [ "$tag" = PIN ] || continue
  PIN_PATH[$name]=$path; PIN_SHA[$name]=$sum
done < "$PINS"

# Require the ultra-low-memory kernel pins unconditionally (DECLINE if missing; never silently fall back to high-memory legs)
PLC_KEY=pleanchecker_lowmem
GRZ_KEY=gruszka_lowmem

PNAMES=(ccmp_lowmem "$PLC_KEY" "$GRZ_KEY" selftest_comparator selftest_challenge selftest_good selftest_bad)
if [ -n "$INCR" ] && [ -n "${PIN_PATH[pleanchecker_incr]:-}" ]; then PNAMES+=(pleanchecker_incr); fi
PFILES=(); for name in "${PNAMES[@]}"; do PFILES+=("${PIN_PATH[$name]:-/nonexistent/$name}"); done
stamps() {
  { for f in "$PINS" "${PFILES[@]}"; do find "$f" -maxdepth 0 -printf 'F %p %D %i %m %y %s %T@ %C@ %n %l\n'; done
    find "$TC36" -printf 'T %p %D %i %m %y %s %T@ %C@ %n %l\n' | LC_ALL=C sort; } 2>&1 | sha256sum | cut -d' ' -f1
}
ICHIT=0; ICKEY=; ICSTAMP=; ICSYM=
for f in "$PINS" "${PFILES[@]}" "$TC36"; do [ -L "$f" ] && ICSYM=$f; done
if [ -n "$ICACHE" ] && [ -n "$ICSYM" ]; then log "[$SELF] --integrity-cache: $ICSYM is a symlink -> full verification, no record"; fi
if [ -n "$ICACHE" ]; then
  ICACHE=$(readlink -f -- "$ICACHE") || decline "cannot resolve --integrity-cache"
  { [ -d "$ICACHE" ] && [ ! -L "$ICACHE" ] && [ "$(stat -c '%u %a' -- "$ICACHE")" = "$(id -u) 700" ]; } \
    || decline "--integrity-cache: not a directory owned by this user with mode 700: $ICACHE"
  ICKEY=$( { sha256sum < "$PINS"; printf '%s\n' "$TC36" "${PNAMES[@]}"; } | sha256sum | cut -d' ' -f1)
  ICSTAMP=$(stamps)
  ICF=$ICACHE/integrity-ultralowmem.record
  if [ "$PREFLIGHT" != 1 ] && [ -z "$ICSYM" ] && [ -f "$ICF" ] && [ ! -L "$ICF" ] && [ "$(stat -c '%u' -- "$ICF")" = "$(id -u)" ] \
     && [ "$(cat -- "$ICF" 2>/dev/null)" = "$ICKEY $ICSTAMP" ]; then ICHIT=1; fi
fi

BJ="{"; sep=
for name in "${PNAMES[@]}"; do
  p=${PIN_PATH[$name]:-}; [ -n "$p" ] || decline "pins-ultralowmem.env has no PIN for $name"
  [ -f "$p" ] || decline "pinned file missing: $p"
  if [ "$ICHIT" = 1 ]; then got=${PIN_SHA[$name]}; else
    got=$(sha256sum "$p" | cut -d' ' -f1)
    [ "$got" = "${PIN_SHA[$name]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[$name]})"
  fi
  BJ="$BJ$sep\"$name\":\"$got\""; sep=,
done
BIN_JSON="$BJ}"
CCMP_LM=${PIN_PATH[ccmp_lowmem]}; PLC_BIN=${PIN_PATH[$PLC_KEY]}; GRUSZKA=${PIN_PATH[$GRZ_KEY]}
PLC_INCR_BIN=
if [ -n "$INCR" ] && [ -n "${PIN_PATH[pleanchecker_incr]:-}" ]; then
  PLC_INCR_BIN=${PIN_PATH[pleanchecker_incr]}
fi
if [ "$ICHIT" != 1 ]; then
  /usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" leanprover/lean4:v4.36.0 > /dev/null 2>&1 \
    || decline "the official Lean 4.36 toolchain at $TC36 does not verify against fastverify/toolchains"
fi
if [ -n "$ICACHE" ] && [ "$ICHIT" != 1 ] && [ -z "$ICSYM" ]; then
  if [ "$(stamps)" = "$ICSTAMP" ]; then
    ICT=$(mktemp "$ICACHE/.integrity.XXXXXX") && printf '%s %s\n' "$ICKEY" "$ICSTAMP" > "$ICT" && mv -f -- "$ICT" "$ICF" \
      || { rm -f -- "${ICT:-}"; log "[$SELF] could not write integrity record"; }
  else
    ICSTAMP=
  fi
fi

# ---------- private work dir & private inputs ( NEVER on /tmp tmpfs if MEM_MB is constrained! ) ----------
if [ "$PREFLIGHT" = 1 ]; then WD=/tmp; INCR=; fi
if [ -n "$INCR" ]; then
  INCR=$(readlink -f -- "$INCR") || decline "cannot resolve --incr-dir"
  [ -n "$WD" ] || WD=$(dirname "$E_IN")
fi
if [ -z "$WD" ]; then
  # Important for U3 cgroups: tmpfs (/tmp) charges file copies to the cgroup's memory.max! When a memory limit is active
  # or files > 256 MiB, place the workdir on disk next to E_IN if writable, else /scratch, else /tmp.
  if [ "$MEM_MB" -gt 0 ] || [ "$(stat -c %s -- "$E_IN")" -gt 268435456 ] || [ "$(stat -c %s -- "$C_IN")" -gt 268435456 ]; then
    if [ -w "$(dirname "$E_IN")" ]; then WD=$(dirname "$E_IN")
    elif [ -d /scratch ] && [ -w /scratch ]; then WD=/scratch
    else WD=/tmp; fi
  else
    WD=/tmp
  fi
fi
W=$(mktemp -d "$WD/.checkSoundLowMem.XXXXXX" 2>/dev/null) || W=$(mktemp -d "/tmp/checkSoundLowMem.XXXXXX") || decline "cannot create a work dir"
W=$(/usr/bin/realpath -e -- "$W") || decline "cannot resolve the work dir $W"   # absolute: a relative --workdir gave bwrap relative mount destinations
chmod 755 "$W"
mkdir -p "$W/bin" "$W/tmp" "$W/home"

priv() {
  if [ "${3:-}" = link-ok ] && [ "$PRIVIN" = 1 ] && [ "$(stat -c %s -- "$1")" -gt 4294967296 ]; then
    if ln -- "$1" "$2" 2>/dev/null; then echo link; return 0; fi
    log "[$SELF] cannot hard-link $1 into $W: copying instead"
  fi
  cp --reflink=auto -- "$1" "$2" || return 1
  echo copy
}
if [ "$PREFLIGHT" = 1 ]; then
  cp -- "${PIN_PATH[selftest_good]}" "$W/solution.export"; cp -- "${PIN_PATH[selftest_challenge]}" "$W/challenge.export"
  cp -- "${PIN_PATH[selftest_comparator]}" "$W/comparator.orig.json"
else
  PRIV_E=$(priv "$E_IN" "$W/solution.export" link-ok) || decline "cannot copy the export into $W"
  PRIV_C=$(priv "$C_IN" "$W/challenge.export") || decline "cannot copy the challenge export into $W"
  cp -- "$CFG_IN" "$W/comparator.orig.json" || decline "cannot copy the config"
  INPUTS_JSON=$(printf '{"export":{"size":%s,"private":"%s"},"challenge":{"size":%s,"private":"%s"}}' \
    "$(stat -c %s -- "$E_IN")" "$PRIV_E" "$(stat -c %s -- "$C_IN")" "$PRIV_C")
  log "[$SELF] private inputs: export $PRIV_E ($(stat -c %s -- "$E_IN") bytes), challenge $PRIV_C (priv_asserted=$PRIVIN)"
fi
case "$W$INCR$PLC_BIN$PLC_INCR_BIN$GRUSZKA$CCMP_LM$T_EFF" in *[\"\\\$\`]*|*$'\n'*) decline "a path used by the kernel wrappers contains a shell-special character";; esac

: > "$W/hints"
if [ -z "$HINTS" ] && [ -f "$PKGROOT/check/sound/hints/default.txt" ]; then HINTS=$PKGROOT/check/sound/hints/default.txt; fi
if [ "$HINTS" = none ]; then HINTS=; fi
if [ -n "$HINTS" ]; then
  { [ -f "$HINTS" ] && [ "$(stat -c %s -- "$HINTS")" -le 16777216 ]; } || decline "--hints: not a regular file <= 16 MiB: '$HINTS'"
  cp -- "$HINTS" "$W/hints" || decline "cannot copy the hints file"
fi
stamp() { stat -c '%i %s %y %z' -- "$W/solution.export" "$W/challenge.export"; }
STAMP0=$(stamp)

# ---------- strict JSON config validation + wrappers ----------
PLC_STACK_KB=917376
mkplc() {
  local attach=; [ -n "${3:-}" ] && attach="\"--attach=$3\" "
  local lm_flags=; local lm_env=
  if [ "$PLC_KEY" = pleanchecker_lowmem ] && [ -z "${3:-}" ]; then
    lm_flags="--low-mem --evict=smart "
    lm_env="MIMALLOC_PURGE_DELAY=0 MIMALLOC_PURGE_DECOMMITS=1 "
  fi
  cat > "$1" <<EOF
#!/bin/sh
for a do shift; [ "\$a" = --silent ] || set -- "\$@" "\$a"; done
for a do L=\$a; done
case "\$L" in "$W/solution.export") N=lean;; *) N=selftest-lean-\$(basename "\$L");; esac
${lm_env}PCHK_PRIO_FILE="$W/hints" PCHK_SLOW_MS=10000 LEAN_STACK_SIZE_KB=$PLC_STACK_KB "$2" ${lm_flags}-j$T_EFF -v $attach"\$@" > "$W/tmp/leg-\$N.log" 2>&1
rc=\$?; echo "\$rc" > "$W/tmp/leg-\$N.rc"; exit \$rc
EOF
  chmod 755 "$1"
}
mkplc "$W/bin/plc-plain" "$PLC_BIN"
if [ -n "$INCR" ] && [ -z "$PLC_INCR_BIN" ]; then log "[$SELF] --incr-dir given but no PIN pleanchecker_incr: plain replay"; INCR=; fi
if [ -n "$INCR" ]; then
  mkplc "$W/bin/plc" "$PLC_INCR_BIN" "$INCR"
else
  cp "$W/bin/plc-plain" "$W/bin/plc"
fi
GRZ_LM_ARGS=; [ "$GRZ_KEY" = gruszka_lowmem ] && GRZ_LM_ARGS="--low-mem --pack-dir=\"$W/tmp\" "
# the end of the judge's --timeout budget (epoch s; 0 = none) for the gruszka wrapper's retry
DL=0; [ "$TMO" -gt 0 ] && DL=$(( ${T_START%.*} + TMO ))
cat > "$W/bin/gruszka-kernel" <<EOF
#!/bin/sh
[ \$# = 1 ] || { echo "gruszka wrapper: expected 1 argument (the export), got \$#" >&2; exit 2; }
case "\$1" in "$W/solution.export") N=k2;; *) N=selftest-k2-\$(basename "\$1");; esac
# Availability: a gruszka decline ONLY for worker-table room depends on the schedule (a
# declaration that runs before the results it reuses exist evaluates them again and can fill its worker's tables), not on
# the input's validity: the judged export's leg runs gruszka ONCE more with 1 worker (the deterministic schedule:
# file/namespace order) and keeps that answer. Trigger (all of it): the judged export (never a self-test), exit
# status exactly 2, a complete log (non-empty, ends with a newline), every line is 'note: ...' except exactly one
# 'declined: ' line, which is the LAST line and ends ': a worker table is full'. Anything else is never retried (residual:
# gruszka prints names unescaped; a crafted name can at most cause this one extra run). The retry runs only inside the
# REMAINING time of the judge's --timeout (DL; none left: no retry; over it: killed, exit 124/137 = no verdict from
# gruszka), with the judge's own worker count (lowmem: T_EFF, the memory-capped count), and only if the first attempt's log could be archived (leg-<leg>-retries.log; first exit status in
# leg-<leg>.retry -> judge JSON legs.k2.retry). A retry ended by a signal keeps its exit status (128+n): gruszka gave no
# verdict, and the judge's existing rule decides (README). Veto-only (S1(4)): ACCEPTED still needs the official-kernel
# leg and the comparison.
DL=$DL
w=$T_EFF
"$GRUSZKA" ${GRZ_LM_ARGS}"\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
if [ "\$N" = k2 ] && [ "\$rc" -eq 2 ] && [ \$w -gt 1 ] && [ -s "$W/tmp/leg-\$N.log" ] && [ -z "\$(tail -c 1 "$W/tmp/leg-\$N.log")" ] \\
    && awk 'BEGIN { d = 0; bad = 0 } /^declined: / { d++ } { last = \$0; if (\$0 !~ /^(declined|note): /) bad = 1 }
            END { exit !(d == 1 && !bad && last ~ /^declined: .*: a worker table is full\$/) }' "$W/tmp/leg-\$N.log"; then
  left=; [ "\$DL" -gt 0 ] && left=\$(( DL - \$(date +%s) ))
  if [ -n "\$left" ] && [ "\$left" -le 0 ]; then
    { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room: no time left for a 1-worker retry"; } >> "$W/tmp/leg-\$N-retries.log"
  elif ! { cat "$W/tmp/leg-\$N.log"; echo "[gruszka wrapper] declined for worker-table room (first attempt above)"; } >> "$W/tmp/leg-\$N-retries.log"; then
    : # the first attempt could not be archived: no retry (the leg stays DECLINED)
  elif ! echo "\$rc" > "$W/tmp/leg-\$N.retry"; then
    echo "[gruszka wrapper] could not record the first exit status (leg-\$N.retry): no retry" >> "$W/tmp/leg-\$N-retries.log"
  else
    echo "[gruszka wrapper] again with 1 worker\${left:+ (at most \$left s)}" >> "$W/tmp/leg-\$N-retries.log"
    w=1
    if [ -n "\$left" ]; then /usr/bin/timeout --foreground --kill-after=5 "\$left" "$GRUSZKA" ${GRZ_LM_ARGS}"\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?
    else "$GRUSZKA" ${GRZ_LM_ARGS}"\$1" \$w > "$W/tmp/leg-\$N.log" 2>&1; rc=\$?; fi
    [ "\$rc" -le 2 ] || echo "[gruszka wrapper] the 1-worker retry ended with exit \$rc (signal or time limit): no verdict from gruszka" >> "$W/tmp/leg-\$N-retries.log"
  fi
fi
echo "\$rc" > "$W/tmp/leg-\$N.rc"; exit \$rc
EOF
printf '#!/bin/sh\ncommand -v "$1"\n' > "$W/bin/which"
chmod 755 "$W/bin/plc" "$W/bin/gruszka-kernel" "$W/bin/which"

: > "$W/kept.txt"
CFGMSG=$(/usr/bin/python3 -I - "$W/comparator.orig.json" "$W/comparator.json" "$W/bin/gruszka-kernel" "$KEEPK" "$W" <<'PY' 2>&1
import json, os, shlex, sys
src, dst, gk, keep, W = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] == "1", sys.argv[5]
def no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate key in the configuration")
    return dict(pairs)
def bad_const(x):
    raise ValueError("non-standard JSON constant %s" % x)
# The ORIGINAL comparator.json is validated first, exactly as the official 4.36 comparator reads it. The
# block below is the validator from check/notary/check-notary.sh, copied VERBATIM;
# in this judge the challenge's external kernels / enable_nanoda are replaced by the judge's own second kernel (the
# documented rewrite below), which is why the official PATH lookup of the challenge's kernel commands does not apply.
# before anything is checked or rewritten, the file is read EXACTLY as far as the official 4.36
# comparator reads it (src/lean/lake/Lake/CLI/Check.lean runComparator: Json.parse, then the derived FromJson of
# Lake.Check.Config, then "nothing to check", then resolveExternalKernels' configuration checks). Any official
# configuration error (the official comparator exits 2: no verdict) is refused here -> DECLINED; the rewrite below can
# therefore never turn an official configuration error into a verdict. Lean's Json.parse: duplicate keys refused, a
# positive exponent > 100000 refused, a lone surrogate escape becomes U+FFFD (applied here too, before the
# duplicate-key check, as Lean does). Numbers are kept as their literal text (JNum, never converted: the official
# decoder ignores numbers in fields it does not read, and Python's int() has a 4300-digit limit); a resource limit of
# this reader (recursion / memory) is reported as the notary's own limit, not as an official error. Environment-
# dependent checks (an external kernel command that is not on the official host's PATH) are made for the judge's own
# kernel environment below (every kept command must resolve there; the challenge's kernels are run, recorded in
# "config_rewrite").
class JNum:
    __slots__ = ("s",)
    def __init__(self, s):
        self.s = s
def lean_num(x):
    m = x.lower().partition("e")
    e = m[2].lstrip("+").lstrip("0") or "0"
    if m[1] and not m[2].startswith("-") and (len(e) > 6 or (len(e) == 6 and e > "100000")):
        raise ValueError("JSON number exponent too large (Lean's Json.parse refuses it)")
    return JNum(x)
def lean_str(t):
    return "".join("\ufffd" if 0xD800 <= ord(ch) <= 0xDFFF else ch for ch in t)
def lean_val(v):
    if isinstance(v, str):
        return lean_str(v)
    if isinstance(v, list):
        return [lean_val(y) for y in v]
    return v
def lean_pairs(pairs):
    d = {}
    for k, v in pairs:
        k = lean_str(k)
        if k in d:
            raise ValueError("duplicate object key %r" % k)
        d[k] = lean_val(v)
    return d
def jshow(x):
    return json.dumps(x, default=lambda o: o.s if isinstance(o, JNum) else str(o))[:80]
def off_err(msg):
    sys.exit("official comparator configuration error (the official 4.36 comparator stops with exit 2, no verdict): " + msg)
try:
    c = lean_val(json.loads(open(src, "rb").read().decode("utf-8", errors="strict"), object_pairs_hook=lean_pairs,
                            parse_constant=bad_const, parse_float=lean_num, parse_int=lean_num))
except SystemExit:
    raise
except (RecursionError, MemoryError) as e:
    sys.exit("the notary's own resource limit while reading the configuration (%s; not an official error): no verdict" % type(e).__name__)
except Exception as e:
    off_err("malformed configuration: %s" % e)
if not isinstance(c, dict):
    off_err("Lake.Check.Config.challenge_module: String expected (the configuration is not a JSON object)")
def fj_str(k):
    if not isinstance(c.get(k), str):
        off_err("Lake.Check.Config.%s: String expected" % k)
def fj_arr_str(k, optional):
    x = c.get(k)
    if x is None and optional:
        return []
    if not isinstance(x, list):
        off_err("Lake.Check.Config.%s: expected JSON array, got %s" % (k, jshow(x)))
    if not all(isinstance(y, str) for y in x):
        off_err("Lake.Check.Config.%s: String expected" % k)
    return x
fj_str("challenge_module")
fj_str("solution_module")
off_tn = fj_arr_str("theorem_names", False)
off_dn = fj_arr_str("definition_names", True)
fj_arr_str("permitted_axioms", False)
off_en = c.get("enable_nanoda")
if off_en is not None and not isinstance(off_en, bool):
    off_err("Lake.Check.Config.enable_nanoda?: Bool expected")
off_ek = c.get("external_kernels")
if off_ek is not None:
    if not isinstance(off_ek, dict):
        off_err("Lake.Check.Config.external_kernels?: object expected")
    for kn, kc in off_ek.items():
        if not isinstance(kc, list):
            off_err("Lake.Check.Config.external_kernels?: expected JSON array, got %s" % jshow(kc))
        if not all(isinstance(y, str) for y in kc):
            off_err("Lake.Check.Config.external_kernels?: String expected")
if not off_tn and not off_dn:
    off_err("nothing to check: the configuration names no theorems or definitions")
if off_en is True and off_ek:
    off_err("cannot use `enable_nanoda` and `external_kernels` at the same time")
for kn, kc in (off_ek or {}).items():
    if not kc or kc[0].split(chr(0))[0][:1] in ("", "-") or kc[0].split(chr(0))[0].rsplit("/", 1)[-1] in ("", ".", ".."):
        off_err("`%s` has an empty command" % kn)
# end of the verbatim validator block
try:
    c = json.loads(open(src, "rb").read().decode("utf-8", errors="strict"), object_pairs_hook=no_dups,
                   parse_constant=bad_const)
except Exception as e:
    sys.exit("config is not strict JSON (%s)" % e)
if not isinstance(c, dict):
    sys.exit("config is not a JSON object")
def _is_letter_like(c):
    v = ord(c)
    return (
        (0x3B1 <= v <= 0x3C9 and v != 0x3BB)
        or (0x391 <= v <= 0x3A9 and v != 0x3A0 and v != 0x3A3)
        or (0x3CA <= v <= 0x3FB)
        or (0x1F00 <= v <= 0x1FFE)
        or (0x2100 <= v <= 0x214F)
        or (0x1D49C <= v <= 0x1D59F)
        or (0x00C0 <= v <= 0x00FF and v != 0x00D7 and v != 0x00F7)
        or (0x0100 <= v <= 0x017F)
    )

def _is_subscript_alnum(c):
    v = ord(c)
    return (0x2080 <= v <= 0x2089) or (0x2090 <= v <= 0x209C) or (0x1D62 <= v <= 0x1D6A) or v == 0x2C7C

def _is_id_first(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or _is_letter_like(c)

def _is_id_rest(c):
    return (
        ("a" <= c <= "z")
        or ("A" <= c <= "Z")
        or ("0" <= c <= "9")
        or c in ("_", "'", "!", "?")
        or _is_letter_like(c)
        or _is_subscript_alnum(c)
    )

def parse_lean_name(s):
    """Exact mirror of Lean 4 `String.toName` (`Init/Meta/Defs.lean:splitNameLitAux` + `Substring.Raw.toName`).
    Returns a canonical component tuple: `()` for `Name.anonymous`, `(("s", str) | ("n", int), ...)` otherwise."""
    n = len(s)
    if n == 0:
        return ()
    i = 0
    comps = []
    while True:
        if i >= n:
            return ()
        c = s[i]
        if c == "«":
            j = s.find("»", i + 1)
            if j < 0:
                return ()
            comps.append(("s", s[i + 1 : j]))
            i = j + 1
        elif _is_id_first(c):
            j = i + 1
            while j < n and _is_id_rest(s[j]):
                j += 1
            comps.append(("s", s[i:j]))
            i = j
        elif "0" <= c <= "9":
            j = i + 1
            while j < n and ("0" <= s[j] <= "9"):
                j += 1
            comps.append(("n", int(s[i:j])))
            i = j
        else:
            return ()
        if i == n:
            return tuple(comps)
        if s[i] == ".":
            i += 1
        else:
            return ()

def q02_canon(x):
    t = parse_lean_name(x) if isinstance(x, str) else ()
    if not t:
        sys.exit("config: name %r is not a Lean name" % (x,))
    return t
Q02_S1 = set(q02_canon(n) for n in ("propext", "Quot.sound", "Classical.choice"))
Q02_PRIMS = set(q02_canon(n) for n in ("Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
    "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List",
    "eagerReduce", "Nat", "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam", "Quot",
    "Quot.mk", "Quot.lift", "Quot.ind",   # the comparator's primitiveTargets + builtinTargets
    "Nat.zero", "Nat.succ", "List.cons", "List.nil", "Bool", "Bool.true", "Bool.false", "Eq", "Eq.refl", "dontcare",
    "Lean.reduceBool", "Lean.reduceNat"))   # + kernel-implicit names (their closure: xversion/xvcheck.py)
q02_ax = c.get("permitted_axioms")
if not isinstance(q02_ax, list) or not all(isinstance(x, str) for x in q02_ax):
    sys.exit("permitted_axioms is not a list of names")
q02_allow = []
q02_extra = sorted(set(x for x in q02_ax if q02_canon(x) not in Q02_S1))
if set(q02_canon(x) for x in q02_extra) != set(q02_canon(x) for x in q02_allow):
    if q02_extra:
        sys.exit("permitted_axioms %s outside GOAL S1(3) (propext, Quot.sound, Classical.choice)%s" % (
            q02_extra, "" if not q02_allow else "; --extra-axioms lists %s" % sorted(q02_allow)))
    sys.exit("--extra-axioms lists %s but the config permits no axiom outside GOAL S1(3)" % sorted(q02_allow))
q02_dn = c.get("definition_names")
q02_dn = [] if q02_dn is None else q02_dn
q02_tn = c.get("theorem_names")
q02_tn = [] if q02_tn is None else q02_tn
if not isinstance(q02_dn, list) or not all(isinstance(x, str) for x in q02_dn):
    sys.exit("definition_names is not a list of names")
if not isinstance(q02_tn, list) or not all(isinstance(x, str) for x in q02_tn):
    sys.exit("theorem_names is not a list of names")
q02_bad = sorted(x for x in q02_dn if q02_canon(x) in (Q02_PRIMS | set(map(q02_canon, q02_tn)) | set(map(q02_canon, q02_ax))))
if q02_bad:
    sys.exit("definition_names %s overlap the kernel primitives / quotient builtins / theorem_names / permitted_axioms" % q02_bad)
ek = c.get("external_kernels")
if c.get("enable_nanoda") is True and isinstance(ek, dict) and len(ek) > 0:
    sys.exit("enable_nanoda together with external_kernels (the official comparator refuses this)")
if keep:
    kernels = dict(ek) if isinstance(ek, dict) else {}
    if c.get("enable_nanoda") is True:
        kernels["nanoda"] = ["nanoda_bin"]
else:
    kernels = {}
if "gruszka (second kernel)" in kernels:
    sys.exit("config already names a kernel 'gruszka (second kernel)'")
with open(os.path.join(W, "kept.txt"), "w", encoding="utf-8") as kf:
    for i, (name, cmd) in enumerate(sorted(kernels.items())):
        # as Lake - a non-empty executable (cmd[0]); later arguments may be empty strings
        if not (isinstance(cmd, list) and cmd and all(isinstance(x, str) for x in cmd) and cmd[0]):
            sys.exit("external kernel %r has no usable command" % name)
        if "\n" in name or "\t" in name:
            sys.exit("external kernel name with a newline/tab: %r" % name)
        wp = os.path.join(W, "bin", "kept-%d" % i)
        with open(wp, "w", encoding="utf-8") as f:
            f.write("#!/bin/sh\n%s \"$@\" > %s 2>&1\nrc=$?; echo \"$rc\" > %s; exit $rc\n" % (
                " ".join(shlex.quote(x) for x in cmd), shlex.quote(os.path.join(W, "tmp", "leg-kept-%d.log" % i)),
                shlex.quote(os.path.join(W, "tmp", "leg-kept-%d.rc" % i))))
        os.chmod(wp, 0o755)
        kernels[name] = [wp]
        kf.write("%d\t%s\n" % (i, name))
kernels["gruszka (second kernel)"] = [gk]
# only the keys of Lake.Check.Config go to the private config - the official decoder ignores every
# other key, and Python would re-serialize an ignored finite number such as 1e309 as the non-JSON token Infinity
c = {k: v for k, v in c.items() if k in ("challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms",
                                 "enable_nanoda", "external_kernels")}
c.pop("enable_nanoda", None)
c["external_kernels"] = kernels
with open(dst, "w", encoding="utf-8") as f:
    json.dump(c, f, ensure_ascii=False)
PY
) || decline "config refused: $CFGMSG"
# the private copies the legs will read are measured here; with --challenge-sha256 /
# --comparator-sha256 (64 lowercase hex) the caller's pins are verified against THESE copies (no window between the caller's
# check and the judge's copy); a mismatch is no verdict. Skipped only by --preflight (the copies are then the self-test's).
if [ "${PREFLIGHT:-0}" != 1 ]; then
  CSHA_GOT=$(sha256sum "$W/challenge.export" | cut -d' ' -f1); CFGSHA_GOT=$(sha256sum "$W/comparator.orig.json" | cut -d' ' -f1)
  for q02pin in "${CSHA_PIN:-}" "${CFGSHA_PIN:-}"; do
    case "$q02pin" in '') ;; *[!0-9a-f]*) decline "--challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits";; esac
    [ -z "$q02pin" ] || [ "${#q02pin}" = 64 ] || decline "--challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits"
  done
  [ -z "${CSHA_PIN:-}" ] || [ "$CSHA_GOT" = "$CSHA_PIN" ] || decline "challenge export sha256 $CSHA_GOT (private copy) != --challenge-sha256 $CSHA_PIN"
  [ -z "${CFGSHA_PIN:-}" ] || [ "$CFGSHA_GOT" = "$CFGSHA_PIN" ] || decline "comparator config sha256 $CFGSHA_GOT (private copy) != --comparator-sha256 $CFGSHA_PIN"
fi
# cross-version gate on the PRIVATE copies (check/xversion/xvcheck.py): the release
# that exported the challenge must be admitted (releases.json) and its extra comparator rules must hold (4.37: challenge
# definitions sorried). rc 0 + OK -> continue; rc 1 + REJECTED -> REJECTED; anything else -> no verdict.
if [ "${PREFLIGHT:-0}" != 1 ]; then
  XVPY=$PKGROOT/check/xversion/xvcheck.py
  [ -f "$XVPY" ] || decline "xversion gate: check/xversion/xvcheck.py missing"
  /usr/bin/python3 -I "$XVPY" "$W/challenge.export" "$W/comparator.orig.json" --releases "$PKGROOT/check/xversion/releases.json" ${Q02_RSH:+--require-sorried-holes} \
    --json "$W/xversion.json" > "$W/xversion.out" 2>&1
  XV_RC=$?
  XV_V=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("verdict",""))' "$W/xversion.json" 2>/dev/null)
  XV_REASON=$(/usr/bin/python3 -I -c 'import json,sys; print(str(json.load(open(sys.argv[1])).get("reason",""))[:300])' "$W/xversion.json" 2>/dev/null)
  if [ "$XV_RC" = 0 ] && [ "$XV_V" = OK ]; then
    :
  elif [ "$XV_RC" = 1 ] && [ "$XV_V" = REJECTED ]; then
    finish 1 REJECTED "xversion: $XV_REASON"
  else
    decline "xversion gate failed (rc=$XV_RC): $XV_REASON"
  fi
fi

JPATH="$W/bin:$TC36/bin:/usr/bin:/bin"
run_bwrap() {
  local thr=$1; shift
  local ro_extra=()
  [ -n "$INCR" ] && [ -d "$INCR" ] && ro_extra+=(--bind "$INCR" "$INCR")
  env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
    --ro-bind "$TC36" "$TC36" --ro-bind "$W" "$W" \
    --bind "$W/tmp" "$W/tmp" --bind "$W/home" "$W/home" "${ro_extra[@]}" --chdir "$W" \
    --setenv HOME "$W/home" --setenv TMPDIR "$W/tmp" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 \
    --setenv LEAN_NUM_THREADS "$thr" --setenv PATH "$JPATH" --setenv CCMP_LEANCHECKER "${PLC_W:-$W/bin/plc}" \
    -- "$@"
}

# ---------- self-test (sequential before judged legs so 0 MB overlaps with the main legs!) ----------
STCFG=$W/st.json
/usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("enable_nanoda",None); c["external_kernels"]={"gruszka (second kernel)":[sys.argv[3]]}; json.dump(c,open(sys.argv[2],"w"))' \
  "${PIN_PATH[selftest_comparator]}" "$STCFG" "$W/bin/gruszka-kernel" || decline "cannot write the self-test config"
selftest() {
  local g b PLC_W=$W/bin/plc-plain
  # Run selftest with 1 worker thread so its peak RSS is < 100 MB even under strict 512M/1G cgroups
  PCHK_SELFTEST=1 run_bwrap 1 "$CCMP_LM" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_good]}" > "$W/st_good.log" 2>&1; g=$?
  PCHK_SELFTEST=1 run_bwrap 1 "$CCMP_LM" "$TC36" "$STCFG" "${PIN_PATH[selftest_challenge]}" "${PIN_PATH[selftest_bad]}" > "$W/st_bad.log" 2>&1; b=$?
  echo "$g $b" > "$W/st.rc"
}
selftest_ok() {
  local g b; read -r g b < "$W/st.rc" 2>/dev/null || { g=x; b=x; }
  if [ "$g" != 0 ] || ! grep -q '^gruszka (second kernel) kernel accepts the solution$' "$W/st_good.log" \
     || ! grep -q '^Lean default kernel accepts the solution$' "$W/st_good.log" || [ "$b" != 1 ]; then
    log "$(tail -8 "$W/st_good.log" 2>/dev/null)"; log "$(tail -5 "$W/st_bad.log" 2>/dev/null)"
    decline "self-test failed (good rc=$g, bad rc=$b): the pinned binaries cannot run here"
  fi
}
if [ "$PREFLIGHT" = 1 ]; then
  selftest; selftest_ok
  finish 0 PREFLIGHT_OK "pinned lowmem binaries present, sha256 OK, self-test passed"
fi
# Under low-memory mode, run selftest BEFORE the judged legs when MEM_MB > 0 (zero overlap!), else concurrently
if [ "$MEM_MB" -gt 0 ]; then
  selftest; selftest_ok; ST_PID=
else
  selftest & ST_PID=$!
fi

leg_rc() { local f=$W/tmp/leg-$1.rc; [ -f "$f" ] && head -c 16 -- "$f" | tr -cd '0-9' | cut -c1-5; }
DEEP_RE='^(\(kernel\) deep recursion detected|Lean default kernel rejects the solution: deep recursion was detected at |deep recursion was detected at |Stack overflow detected\. Aborting\.)$'
lean_deep() { [ -f "$W/tmp/leg-lean.log" ] && grep -qE "$DEEP_RE" "$W/tmp/leg-lean.log"; }
rem_timeout() {
  if [ "$TMO" -le 0 ]; then echo 0; return 0; fi
  local now el rem; now=$(date +%s); el=$(( now - ${T_START%.*} )); rem=$(( TMO - el ))
  [ "$rem" -ge 1 ] || return 1
  echo "$rem"
}

verify_end_integrity() {
  if [ -n "${ST_PID:-}" ]; then wait "$ST_PID"; ST_PID=; selftest_ok; fi
  [ "$(stamp)" = "$STAMP0" ] || decline "an input file was modified during the check"
  if [ "$ICHIT" = 1 ]; then
    [ "$(stamps)" = "$ICSTAMP" ] || decline "pinned components changed during the run (integrity stamp)"
  else
    for name in "${PNAMES[@]}"; do
      [ "$(sha256sum "${PIN_PATH[$name]}" | cut -d' ' -f1)" = "${PIN_SHA[$name]}" ] || decline "pinned $name changed during the run"
    done
  fi
}

ICBASIS=
if [ -n "$ICACHE" ]; then
  if [ "$ICHIT" = 1 ]; then ICBASIS="integrity: stamp of verified pins + 4.36 tree (--integrity-cache); "; else ICBASIS="integrity: full verification; "; fi
fi
BASIS="${ICBASIS}challenge export as given (sha256 checked by the caller); statements + axioms: official Lean 4.36 comparator judge code via 2-pass low-memory streaming reader (ccmp-lowmem compareAt + checkAxioms); kernel 1: official Lean 4.36 kernel libraries (${PLC_KEY} parallel Lean.Replay walk${INCR:+, incremental/overlapped}); kernel 2: ${GRZ_KEY} (independent); legs executed sequentially in separate sandboxes"

# ---------- Sequential Execution ----------
if [ "$KEEPK" = 1 ]; then
  # Kept external kernels mode (e.g. nanoda): ccmp-lowmem itself runs compare -> kept kernels -> gruszka -> pleanchecker sequentially
  if [ "$TMO" -gt 0 ]; then TPFX=(timeout --kill-after=30 "$TMO"); else TPFX=(); fi
  log "[$SELF] ccmp-lowmem (sequential with kept kernels) start: threads=$T_EFF"
  run_bwrap "$T_EFF" "${TPFX[@]}" "$CCMP_LM" "$TC36" "$W/comparator.json" "$W/challenge.export" "$W/solution.export" > "$W/ccmp.log" 2>&1
  CCMP_RC=$?
  log "$(cat "$W/ccmp.log")"
  for f in "$W"/tmp/leg-*.log; do [ -f "$f" ] || continue; log "--- $(basename "$f") (last 64 KiB) ---"; log "$(tail -c 65536 "$f")"; done
  LEG_JSON=$(/usr/bin/python3 -I -c '
import json, re, sys
d = {}
for ln in open(sys.argv[1], errors="replace"):
    m = re.match(r"^\[ccmp\] (.*?) finished after (\d+) ms(?:\s*\(leg (\d+) ms\))?$", ln.strip())
    if m: d[m.group(1)] = int(m.group(3) if m.group(3) is not None else m.group(2))
print(json.dumps(d))' "$W/ccmp.log" 2>/dev/null) || LEG_JSON=null
  LEGS_JSON=$(/usr/bin/python3 -I - "$W/tmp" "$LEG_JSON" "$W/kept.txt" <<'PY' 2>/dev/null
import json, os, re, sys
d, keptf = sys.argv[1], sys.argv[3]
ms = json.loads(sys.argv[2]) if sys.argv[2] != "null" else {}
def rc(n):
    try: s = open(os.path.join(d, "leg-%s.rc" % n), errors="replace").read(16).strip()
    except OSError: return None
    return int(s) if s.isdigit() else None
def msg(n, pat):
    try: lines = open(os.path.join(d, "leg-%s.log" % n), errors="replace").read(4000000).splitlines()
    except OSError: return None
    for i, ln in enumerate(lines):
        if re.search(pat, ln): return "\n".join(lines[i:i + 2])[:400]
    return lines[-1][:400] if lines else ""
legs = {"lean": {"rc": rc("lean"), "ms": ms.get("kernel Lean default"),
                 "message": msg("lean", r"^(Lean default kernel|Quotient post-check|Stack overflow|deep recursion|\(kernel\))")},
        "k2": {"rc": rc("k2"), "ms": ms.get("kernel gruszka (second kernel)"),
               "message": msg("k2", r"(?i)accept|reject|error|panic|fatal|declin")}}
# a gruszka run retried with 1 worker after a decline for worker-table room is recorded (wrapper: leg-k2.retry)
try:
    _fr = open(os.path.join(d, "leg-k2.retry"), errors="replace").read(16).strip()
    legs["k2"]["retry"] = {"reason": "a worker table is full", "first_rc": int(_fr) if _fr.isdigit() else None, "workers": 1}
except (OSError, KeyError):
    pass
try:
    # records end with "\n" only (a kernel name may contain "\r"; universal newlines would split it)
    for ln in open(keptf, encoding="utf-8", newline="").read().split("\n"):
        if not ln:
            continue
        i, name = ln.split("\t", 1)
        legs["kept-" + i] = {"name": name, "rc": rc("kept-" + i), "ms": ms.get("kernel " + name),
                             "message": msg("kept-" + i, r"(?i)accept|reject|error|panic|fatal")}
except OSError:
    pass
print(json.dumps({"legs": legs, "compare_ms": ms.get("compare (parse, compareAt, checkAxioms)")}))
PY
  ) || LEGS_JSON='{"legs":null,"compare_ms":null}'
  COMPARE_MS=$(/usr/bin/python3 -I -c 'import json,sys; v=json.loads(sys.argv[1]).get("compare_ms"); print("null" if v is None else int(v))' "$LEGS_JSON" 2>/dev/null) || COMPARE_MS=null
  LEGS_JSON=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.loads(sys.argv[1]).get("legs")))' "$LEGS_JSON" 2>/dev/null) || LEGS_JSON=null
  if [ "$TMO" -gt 0 ] && { [ "$CCMP_RC" = 124 ] || [ "$CCMP_RC" = 137 ]; }; then verify_end_integrity; decline "time limit of $TMO s exceeded"; fi
  verify_end_integrity
  case "$CCMP_RC" in
    0) ;;
    1) ERR=$(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-400)
       [ -n "$ERR" ] || decline "ccmp-lowmem exited 1 without an error line"
       LRC=$(leg_rc lean)
       case "$ERR" in
         "error: Lean default exited with 1")
           [ "${LRC:-}" = 1 ] || decline "inconsistent status of official-kernel leg"
           if lean_deep; then decline "the official-kernel leg ran out of stack (deep recursion): no verdict"; fi
           finish 1 REJECTED "$ERR";;
         "error: Lean default exited with "*|"error: Error while interacting with Lean default kernel"*)
           decline "the official-kernel leg could not finish ($ERR): no verdict";;
         "error: gruszka (second kernel) exited with 1")
           finish 1 REJECTED "$ERR";;
         "error: gruszka (second kernel) exited with "*|"error: Error while interacting with gruszka (second kernel) kernel"*)
           if [ "${LRC:-}" = 1 ] && ! lean_deep; then finish 1 REJECTED "$ERR (and the official-kernel leg rejected)"; fi
           decline "the second kernel could not decide ($ERR)";;
         "error: "*" exited with 1") finish 1 REJECTED "$ERR";;
         "error: "*" exited with "*|"error: Error while interacting with "*) decline "a configured kernel could not finish ($ERR): no verdict";;
         *) if printf '%s\n' "$ERR" | grep -qE '^error: (memory allocation of [0-9]+ bytes failed|out of memory|std::bad_alloc|failed to create thread|resource exhausted|Stack overflow detected|deep recursion was detected at |\(kernel\) deep recursion detected)'; then
              decline "ccmp-lowmem could not finish ($ERR): no verdict"
            fi
            finish 1 REJECTED "$ERR";;
       esac;;
    2) decline "ccmp-lowmem could not run: $(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-300)";;
    *) decline "ccmp-lowmem terminated abnormally (rc=$CCMP_RC)";;
  esac
  grep -q '^Your solution is okay!$' "$W/ccmp.log" || decline "ccmp-lowmem rc=0 without the official success line"
  grep -q '^Lean default kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp-lowmem rc=0 but no acceptance line of the Lean kernel"
  grep -q '^gruszka (second kernel) kernel accepts the solution$' "$W/ccmp.log" || decline "ccmp-lowmem rc=0 but no acceptance line of the second kernel"
  [ "$(leg_rc lean)" = 0 ] || decline "official-kernel leg recorded rc != 0"
  [ "$(leg_rc k2)" = 0 ] || decline "second kernel recorded rc != 0"
  while IFS=$'\t' read -r ki kname; do
    [ -n "$ki" ] || continue
    grep -qxF -- "$kname kernel accepts the solution" "$W/ccmp.log" || decline "missing acceptance line of kept kernel '$kname'"
    [ "$(leg_rc "kept-$ki")" = 0 ] || decline "kept kernel '$kname' recorded rc != 0"
  done < "$W/kept.txt"
  finish 0 ACCEPTED "statements + axioms match the challenge (official judge code via ccmp-lowmem); the official Lean 4.36 kernel and gruszka accept every declaration of the export"
fi

# ---------- Standard 3-Process Sequential Mode (0 MB overlap between legs!) ----------
build_status_json() {
  /usr/bin/python3 -I - "$W" "${CMS:-null}" "${LMS:-null}" "${KMS:-null}" <<'PY' 2>/dev/null
import json, os, re, sys
W = sys.argv[1]
cms = None if sys.argv[2] == "null" else int(sys.argv[2])
lms = None if sys.argv[3] == "null" else int(sys.argv[3])
kms = None if sys.argv[4] == "null" else int(sys.argv[4])
def rc(p):
    try: s = open(p, errors="replace").read(16).strip()
    except OSError: return None
    return int(s) if s.isdigit() else None
def msg(p, pat):
    try: lines = open(p, errors="replace").read(4000000).splitlines()
    except OSError: return None
    for i, ln in enumerate(lines):
        if re.search(pat, ln): return "\n".join(lines[i:i + 2])[:400]
    return lines[-1][:400] if lines else ""
leg_ms = {}
if cms is not None: leg_ms["compare (parse, compareAt, checkAxioms)"] = cms
if lms is not None: leg_ms["kernel Lean default"] = lms
if kms is not None: leg_ms["kernel gruszka (second kernel)"] = kms
legs = {
    "compare": {"rc": rc(os.path.join(W, "tmp", "leg-compare.rc")), "ms": cms,
                "message": msg(os.path.join(W, "ccmp.log"), r"^(Comparison and axiom check passed!|error:)")},
    "lean": {"rc": rc(os.path.join(W, "tmp", "leg-lean.rc")), "ms": lms,
             "message": msg(os.path.join(W, "tmp", "leg-lean.log"), r"^(Lean default kernel|Quotient post-check|Stack overflow|deep recursion|\(kernel\))")},
    "k2": {"rc": rc(os.path.join(W, "tmp", "leg-k2.rc")), "ms": kms,
           "message": msg(os.path.join(W, "tmp", "leg-k2.log"), r"(?i)accept|reject|error|panic|fatal|declin")}
}
# a gruszka run retried with 1 worker after a decline for worker-table room is recorded (wrapper: leg-k2.retry)
try:
    _fr = open(os.path.join(W, "tmp", "leg-k2.retry"), errors="replace").read(16).strip()
    legs["k2"]["retry"] = {"reason": "a worker table is full", "first_rc": int(_fr) if _fr.isdigit() else None, "workers": 1}
except (OSError, KeyError):
    pass
print(json.dumps({"leg_ms": leg_ms, "legs": legs, "compare_ms": cms}))
PY
}
refresh_json_vars() {
  local blob; blob=$(build_status_json) || blob='{"leg_ms":null,"legs":null,"compare_ms":null}'
  LEG_JSON=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.loads(sys.argv[1])["leg_ms"]))' "$blob" 2>/dev/null) || LEG_JSON=null
  LEGS_JSON=$(/usr/bin/python3 -I -c 'import json,sys; print(json.dumps(json.loads(sys.argv[1])["legs"]))' "$blob" 2>/dev/null) || LEGS_JSON=null
  COMPARE_MS=${CMS:-null}
}

# --- Leg 1: ccmp-lowmem --compare-only ---
RTMO=$(rem_timeout) || { verify_end_integrity; decline "time limit of $TMO s exceeded"; }
if [ "$RTMO" -gt 0 ]; then TPFX=(timeout --kill-after=15 "$RTMO"); else TPFX=(); fi
T0_C=$(date +%s%3N)
log "[$SELF] leg 1/3 (ccmp-lowmem --compare-only) start: threads=$T_EFF"
run_bwrap "$T_EFF" "${TPFX[@]}" "$CCMP_LM" "$TC36" "$W/comparator.json" "$W/challenge.export" "$W/solution.export" --compare-only > "$W/ccmp.log" 2>&1
CRC=$?
echo "$CRC" > "$W/tmp/leg-compare.rc"
CMS=$(( $(date +%s%3N) - T0_C ))
CCMP_RC=$CRC
log "$(cat "$W/ccmp.log")"
if [ "$CRC" != 0 ]; then
  refresh_json_vars
  if [ "$TMO" -gt 0 ] && [ "$CRC" = 124 ]; then verify_end_integrity; decline "time limit of $TMO s exceeded (compare)"; fi
  verify_end_integrity
  case "$CRC" in
    1) ERR=$(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-400)
       [ -n "$ERR" ] || decline "ccmp-lowmem exited 1 without an error line"
       if printf '%s\n' "$ERR" | grep -qE '^error: (memory allocation of [0-9]+ bytes failed|out of memory|std::bad_alloc|failed to create thread|resource exhausted|Stack overflow detected|deep recursion was detected at |\(kernel\) deep recursion detected)'; then
         decline "ccmp-lowmem could not finish ($ERR): no verdict"
       fi
       finish 1 REJECTED "$ERR";;
    2) decline "ccmp-lowmem could not run: $(grep -m1 -E '^error:' "$W/ccmp.log" | cut -c1-300)";;
    *) decline "ccmp-lowmem terminated abnormally (rc=$CRC)";;
  esac
fi
grep -q '^Comparison and axiom check passed!$' "$W/ccmp.log" || { refresh_json_vars; verify_end_integrity; decline "ccmp-lowmem rc=0 without 'Comparison and axiom check passed!'"; }

# --- Leg 2: Official Lean 4.36 kernel (pleanchecker) ---
RTMO=$(rem_timeout) || { refresh_json_vars; verify_end_integrity; decline "time limit of $TMO s exceeded"; }
if [ "$RTMO" -gt 0 ]; then TPFX=(timeout --kill-after=30 "$RTMO"); else TPFX=(); fi
T0_L=$(date +%s%3N)
log "[$SELF] leg 2/3 ($PLC_KEY) start: threads=$T_EFF"
run_bwrap "$T_EFF" "${TPFX[@]}" "$W/bin/plc" --from-export "$W/solution.export" > "$W/plc_outer.log" 2>&1
LRC_OUT=$?
LMS=$(( $(date +%s%3N) - T0_L ))
[ -f "$W/tmp/leg-lean.log" ] && { log "--- leg-lean.log (last 64 KiB) ---"; log "$(tail -c 65536 "$W/tmp/leg-lean.log")"; }
LRC=$(leg_rc lean)
if [ "$LRC_OUT" != 0 ] || [ "${LRC:-}" != 0 ]; then
  CCMP_RC=1
  refresh_json_vars
  if [ "$TMO" -gt 0 ] && [ "$LRC_OUT" = 124 ]; then verify_end_integrity; decline "time limit of $TMO s exceeded (Lean kernel)"; fi
  verify_end_integrity
  if [ "$LRC_OUT" = 1 ] && [ "${LRC:-}" = 1 ]; then
    if lean_deep; then decline "the official-kernel leg ran out of stack (deep recursion; its stack is smaller than the official walk's): no verdict"; fi
    finish 1 REJECTED "error: Lean default exited with 1"
  fi
  decline "the official-kernel leg could not finish (outer rc=$LRC_OUT, recorded rc=${LRC:-none}): no verdict"
fi
grep -q '^Lean default kernel accepts the solution$' "$W/tmp/leg-lean.log" || { CCMP_RC=2; refresh_json_vars; verify_end_integrity; decline "official-kernel leg rc=0 without acceptance line"; }

# --- Leg 3: Independent second kernel (gruszka) ---
RTMO=$(rem_timeout) || { refresh_json_vars; verify_end_integrity; decline "time limit of $TMO s exceeded"; }
if [ "$RTMO" -gt 0 ]; then TPFX=(timeout --kill-after=30 "$RTMO"); else TPFX=(); fi
T0_K=$(date +%s%3N)
log "[$SELF] leg 3/3 ($GRZ_KEY) start: threads=$T_EFF"
run_bwrap "$T_EFF" "${TPFX[@]}" "$W/bin/gruszka-kernel" "$W/solution.export" > "$W/grz_outer.log" 2>&1
KRC_OUT=$?
KMS=$(( $(date +%s%3N) - T0_K ))
[ -f "$W/tmp/leg-k2.log" ] && { log "--- leg-k2.log (last 64 KiB) ---"; log "$(tail -c 65536 "$W/tmp/leg-k2.log")"; }
[ -f "$W/tmp/leg-k2-retries.log" ] && { log "--- leg-k2-retries.log (last 64 KiB) ---"; log "$(tail -c 65536 "$W/tmp/leg-k2-retries.log")"; }
KRC=$(leg_rc k2)
if [ "$KRC_OUT" != 0 ] || [ "${KRC:-}" != 0 ]; then
  CCMP_RC=1
  refresh_json_vars
  if [ "$TMO" -gt 0 ] && [ "$KRC_OUT" = 124 ]; then verify_end_integrity; decline "time limit of $TMO s exceeded (second kernel)"; fi
  verify_end_integrity
  if [ "$KRC_OUT" = 1 ] && [ "${KRC:-}" = 1 ]; then
    finish 1 REJECTED "error: gruszka (second kernel) exited with 1"
  fi
  decline "the second kernel could not decide (outer rc=$KRC_OUT, recorded rc=${KRC:-none})"
fi

CCMP_RC=0
refresh_json_vars
verify_end_integrity
[ "$(leg_rc compare)" = 0 ] || decline "compare leg recorded rc != 0"
[ "$(leg_rc lean)" = 0 ] || decline "official-kernel leg recorded rc != 0"
[ "$(leg_rc k2)" = 0 ] || decline "second kernel recorded rc != 0"
finish 0 ACCEPTED "statements + axioms match the challenge (official judge code via ccmp-lowmem); the official Lean 4.36 kernel (parallel replay) and the independent kernel gruszka accept every declaration of the export (sequential low-memory check)"
}
main "$@"; exit $?
