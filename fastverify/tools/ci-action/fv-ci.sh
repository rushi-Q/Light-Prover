#!/bin/bash
# fv-ci.sh — Standalone CI / PR merge gate runner for fastverify.
# Works identically in GitHub Actions (action.yml), GitLab CI, Buildkite, or locally.
# Maintains a persistent last-good incremental base in --cache-dir for seconds-level PR verification,
# falling back cleanly to a cold sound run on first run (without ever polluting cache on failure).
set -uo pipefail
# the CI gate (fv-ci.sh, bin/fv ci, the CI action) is EXPERIMENTAL in fastverify
# v0.1: it runs only with --experimental (or FV_EXPERIMENTAL_CI=1); otherwise exit 2 before anything is read or written
FV_CI_EXP=${FV_EXPERIMENTAL_CI:-0}; for _a in "$@"; do [ "$_a" = --experimental ] && FV_CI_EXP=1; done
if [ "$FV_CI_EXP" != 1 ]; then
  echo "fv-ci.sh: the CI gate is EXPERIMENTAL in fastverify v0.1 (its report publication is not yet release grade): pass --experimental or set FV_EXPERIMENTAL_CI=1 to run it" >&2
  exit 2
fi
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV_ROOT=$(cd "$HERE/../.." && pwd)
PROJECT=; CHALLENGE=; PIN=; CFG_PIN=; PACKAGES=; PRESET=sound-auto; PINS=; PINS_FILE=; CACHE_DIR=; OUT_DIR=
CLOSURE_ONLY=0; CONFIRM_REJECT=0; THREADS=; COMMIT=; BUILD_OPT=; EXPORT_DIR=; NO_MERGE=1
FRONTIER=0; ALLOWED_FRONTIER=; FRONTIER_AXIOMS=; FRONTIER_PINNED=; NO_INTEGRITY_CACHE=0
WALL_LIMIT=${FV_CI_WALL:-3600}; DISK_LIMIT=${FV_CI_DISK:-}; MEM_LIMIT=${FV_CI_MEM:-}

while [ $# -gt 0 ]; do
  case "$1" in   # a value option without its value: usage error, exit 2
    --project|--challenge|--challenge-sha256|--comparator-sha256|--packages|--preset|--pins|--build|--export-dir|--cache-dir|\
    --out-dir|--fv-root|--allowed-frontier|--frontier-axioms|--frontier-pinned|--wall|--disk|--mem|--threads|--commit)
      [ $# -ge 2 ] || { echo "fv-ci.sh: $1 needs a value" >&2; exit 2; } ;;
  esac
  case "$1" in   # identity options are given once (a later value never silently wins)
    --project|--challenge|--challenge-sha256|--comparator-sha256|--preset|--pins|--fv-root)
      case "${SEEN_OPTS:- }" in *" $1 "*) echo "fv-ci.sh: $1 given more than once" >&2; exit 2;; esac
      SEEN_OPTS="${SEEN_OPTS:- }$1 " ;;
  esac
  case "$1" in
    --experimental) shift;;
    --project) PROJECT=$2; shift 2;;
    --challenge) CHALLENGE=$2; shift 2;;
    --challenge-sha256) PIN=$2; shift 2;;
    --comparator-sha256) CFG_PIN=$2; shift 2;;
    --packages) PACKAGES=$2; shift 2;;
    --preset) PRESET=$2; shift 2;;
    --pins) PINS=$2; shift 2;;
    --no-integrity-cache) NO_INTEGRITY_CACHE=1; shift;;
    --build) BUILD_OPT=$2; shift 2;;
    --export-dir) EXPORT_DIR=$2; shift 2;;
    --cache-dir) CACHE_DIR=$2; shift 2;;
    --out-dir) OUT_DIR=$2; shift 2;;
    --fv-root) FV_ROOT=$2; shift 2;;
    --closure-only) CLOSURE_ONLY=1; shift;;
    --confirm-reject) CONFIRM_REJECT=1; shift;;
    --frontier) FRONTIER=1; shift;;
    --allowed-frontier) ALLOWED_FRONTIER=$2; shift 2;;
    --frontier-axioms) FRONTIER_AXIOMS=$2; shift 2;;
    --frontier-pinned) FRONTIER_PINNED=$2; shift 2;;
    --wall) WALL_LIMIT=$2; shift 2;;
    --disk) DISK_LIMIT=$2; shift 2;;
    --mem) MEM_LIMIT=$2; shift 2;;
    --threads) THREADS=$2; shift 2;;
    --commit) COMMIT=$2; shift 2;;
    *) echo "fv-ci.sh: unknown arg $1" >&2; exit 2;;
  esac
done
# retire an earlier invocation's reports right after argument parsing, BEFORE any
# refusal (usage, pin format, preset, pins, inputs): a refused run never leaves the previous run's verdict at the output path
if [ -n "$OUT_DIR" ] && [ -d "$OUT_DIR" ]; then
  rm -f "$OUT_DIR/frontier-check.json" "$OUT_DIR/frontier-check.log" "$OUT_DIR/guard-noverdict.json" \
        "$OUT_DIR/result-v1.json" "$OUT_DIR/results.sarif" "$OUT_DIR/summary.md"
fi

# the CI gate runs ONLY the sound family (the verdict must count: fv_schema ACCEPTING_TRUST); an unsafe or
# unofficial preset (fastest, reference, ...) is refused up front instead of being reported as a pass
case "$PRESET" in
  sound|sound-auto|notary) ;;
  *) echo "fv-ci.sh: --preset $PRESET refused: the CI gate accepts only sound, sound-auto or notary (an unsafe / unofficial verdict is never a pass)" >&2
     exit 2;;
esac
case "$BUILD_OPT" in
  ''|B0|B1|B2|B3|official|fast) ;;
  *) echo "fv-ci.sh: --build $BUILD_OPT: expected B0|B1|B2|B3" >&2; exit 2;;
esac
# --comparator-sha256 is required with --challenge-sha256
[ -n "$PROJECT" ] && [ -n "$CHALLENGE" ] && [ -n "$PIN" ] && [ -n "$CFG_PIN" ] && [ -n "$OUT_DIR" ] || {
  echo "usage: fv-ci.sh --project DIR --challenge DIR --challenge-sha256 HEX --comparator-sha256 HEX --out-dir DIR [--cache-dir DIR] [--packages WS] [--preset P] [--closure-only] [--threads N] [--commit SHA]" >&2
  exit 2
}
# both pins are 64 lowercase hex digits (full match: no trailing newline, never empty)
[[ "$PIN" =~ ^[0-9a-f]{64}$ ]] && [[ "$CFG_PIN" =~ ^[0-9a-f]{64}$ ]] || {
  echo "fv-ci.sh: --challenge-sha256 / --comparator-sha256 must be 64 lowercase hex digits" >&2; exit 2; }
PROJECT=$(readlink -f "$PROJECT")
CHALLENGE=$(readlink -f "$CHALLENGE")
PROJ_TC_STR="leanprover/lean4:v4.33.1"
if [ -f "$CHALLENGE/lean-toolchain" ]; then
  PROJ_TC_STR=$(tr -d ' \t\r\n' < "$CHALLENGE/lean-toolchain")
  if [ -f "$PROJECT/lean-toolchain" ]; then
    UNTRUSTED_TC_STR=$(tr -d ' \t\r\n' < "$PROJECT/lean-toolchain")
    if [ "$UNTRUSTED_TC_STR" != "$PROJ_TC_STR" ]; then
      echo "fv-ci.sh: project lean-toolchain ($UNTRUSTED_TC_STR) != challenge lean-toolchain ($PROJ_TC_STR)" >&2
      exit 2
    fi
  fi
elif [ -f "$PROJECT/lean-toolchain" ]; then
  PROJ_TC_STR=$(tr -d ' \t\r\n' < "$PROJECT/lean-toolchain")
fi
if [ -n "$PINS" ]; then
  # Boundary B4: a pins*.env file directly inside this package's check/sound/ (as bin/fastverify): the file
  # is also given to check-frontier.sh, which would otherwise verify the judge binaries against the caller's own hashes
  PINS_DIR=$(readlink -f "$FV_ROOT/check/sound")
  case "$PINS" in
    436|default) PINS_FILE="$PINS_DIR/pins.env";;
    437|4.37|4.37.0-rc1) PINS_FILE="$PINS_DIR/pins-437.env";;
    *) PINS_FILE=$(readlink -f -- "$PINS")
       case "$PINS" in /*) ;; *) [ "$(dirname -- "$PINS_FILE")" = "$PINS_DIR" ] || PINS_FILE=$(readlink -f -- "$FV_ROOT/$PINS");; esac;;
  esac
  PINS_FILE=$(readlink -f -- "$PINS_FILE")
  case "$(basename -- "$PINS_FILE")" in pins*.env) ;; *) PINS_FILE=;; esac
  if [ -z "$PINS_FILE" ] || [ "$(dirname -- "$PINS_FILE")" != "$PINS_DIR" ]; then
    echo "fv-ci.sh: --pins $PINS: must name a pins*.env file in $PINS_DIR (Boundary B4)" >&2
    exit 2
  fi
  if [ ! -f "$PINS_FILE" ]; then
    echo "fv-ci.sh: --pins file not found: $PINS_FILE" >&2
    exit 2
  fi
fi
if [ -n "$CFG_PIN" ]; then
  ACTUAL_CFG_PIN=$(sha256sum "$CHALLENGE/comparator.json" 2>/dev/null | awk '{print $1}')
  if [ "$ACTUAL_CFG_PIN" != "$CFG_PIN" ]; then
    echo "fv-ci.sh: comparator.json sha256 mismatch (got ${ACTUAL_CFG_PIN:-missing}, pinned $CFG_PIN)" >&2
    exit 2
  fi
fi
mkdir -p "$OUT_DIR"
OUT_DIR=$(readlink -f "$OUT_DIR")
[ -n "$THREADS" ] || THREADS=$(nproc 2>/dev/null || echo 4)
if [ -n "$CACHE_DIR" ]; then
  mkdir -p "$CACHE_DIR"
  CACHE_DIR=$(readlink -f "$CACHE_DIR")
fi

T0=$(date +%s.%N)
RUN_DIR="$OUT_DIR/run"
rm -rf "$RUN_DIR"
# retire every report of an earlier invocation first: only this run's reports can be published
rm -f "$OUT_DIR/frontier-check.json" "$OUT_DIR/frontier-check.log" "$OUT_DIR/guard-noverdict.json" \
      "$OUT_DIR/result-v1.json" "$OUT_DIR/results.sarif" "$OUT_DIR/summary.md"
CACHE_MODE=cold
INPUT_KIND=fastverify
INPUT_FILE="$RUN_DIR/result.json"
PREV_V1=""
[ -n "$CACHE_DIR" ] && [ -f "$CACHE_DIR/last-v1.json" ] && PREV_V1="$CACHE_DIR/last-v1.json"

# Optional D07 fvguard wrapper for bounded CI jobs & zero-orphan teardown on cancel/timeout
FVGUARD_PY="$FV_ROOT/tools/guard/fvguard.py"
GUARD_VIOLATED=0
GUARD_STEP_JSON=""
run_guarded() {
  local step=$1; shift
  local gjson="$OUT_DIR/guard.${step}.json"
  rm -f "$gjson"
  if [ -f "$FVGUARD_PY" ] && [ "${WALL_LIMIT:-0}" != "0" ]; then
    local gcmd=(/usr/bin/python3 -I "$FVGUARD_PY" --wall "$WALL_LIMIT" --grace 10 --json "$gjson")
    [ -n "$CACHE_DIR" ] && [ -n "$DISK_LIMIT" ] && gcmd+=(--disk "$CACHE_DIR:$DISK_LIMIT")
    [ -n "$MEM_LIMIT" ] && gcmd+=(--mem "$MEM_LIMIT")
    gcmd+=(-- "$@")
    "${gcmd[@]}"
    local rc=$?
    if [ -f "$gjson" ]; then
      local viol
      viol=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1])).get("violation") or "")' "$gjson" 2>/dev/null || echo "")
      if [ -n "$viol" ]; then
        GUARD_VIOLATED=1
        GUARD_STEP_JSON="$gjson"
        return 125
      fi
    fi
    return "$rc"
  else
    "$@"
    return $?
  fi
}

# Check if we have a valid incremental base in CACHE_DIR (planner-built base/work/proj + base/result.json + log/export-targets.txt + log/build-fast/plan.jsonl)
# Fail-closed: if explicit --pins or Lean 4.37+ toolchain is active while incr-reverify.sh does not support --pins, run cold E24 instead.
USE_INCR=0
INCR_PINS_OK=1
# (v0.1) the CI gate ALWAYS takes the cold path: incremental verification is
# EXPERIMENTAL and never counted, so it is never switched on here (whatever incr-reverify.sh is installed)
INCR_PINS_OK=0
if [ -n "$PINS_FILE" ] || [[ "$PROJ_TC_STR" == *"v4.37"* ]]; then
  grep -q -- '--pins' "$FV_ROOT/tools/incr/incr-reverify.sh" 2>/dev/null || INCR_PINS_OK=0
fi
if [ "$INCR_PINS_OK" = 1 ] && [ -n "$CACHE_DIR" ] && [ -z "$BUILD_OPT" ] && [ -d "$CACHE_DIR/base/work/proj" ] && [ -f "$CACHE_DIR/base/result.json" ] && [ -f "$CACHE_DIR/base/log/export-targets.txt" ] && [ -f "$CACHE_DIR/base/log/build-fast/plan.jsonl" ] && { [ "$PRESET" = "sound" ] || [ "$PRESET" = "sound-auto" ]; }; then
  CUR_CFG_SHA=$(sha256sum "$CHALLENGE/comparator.json" 2>/dev/null | awk '{print $1}')
  BASE_OK=$(/usr/bin/python3 -I -c 'import json,sys
d=json.load(open(sys.argv[1]))
inp=d.get("inputs") or {}
pin=(inp.get("challenge_export") or {}).get("sha256","")
csha=(inp.get("comparator_config") or {}).get("sha256","")
bopt=(d.get("build") or {}).get("option","")
print("yes" if pin == sys.argv[2] and csha == sys.argv[3] and bopt in ("B1","B2","B3") else "no")' "$CACHE_DIR/base/result.json" "$PIN" "$CUR_CFG_SHA" 2>/dev/null || echo "no")
  # the incremental path's checker does not take the caller's comparator pin:
  # use it only when the current config IS the pinned one (else the cold path, which refuses a mismatch)
  # and only when incr-reverify.sh forwards the caller's comparator pin to the judge
  #; otherwise the cold path
  if [ "$BASE_OK" = "yes" ] && [ "$CUR_CFG_SHA" = "$CFG_PIN" ] && \
     grep -q -- '--comparator-sha256)' "$FV_ROOT/tools/incr/incr-reverify.sh" 2>/dev/null; then
    USE_INCR=1
  fi
fi

if [ "$USE_INCR" = 1 ]; then
  CACHE_MODE=incremental
  INPUT_KIND=incr
  INPUT_FILE="$RUN_DIR/summary.json"
  mkdir -p "$RUN_DIR"
  ICACHE="$CACHE_DIR/icache"
  mkdir -p "$ICACHE" && chmod 700 "$ICACHE"
  INCR_TC_PREFIX=$(/usr/bin/python3 -I -c 'import json,sys; print((json.load(open(sys.argv[1])).get("lean_toolchains") or {}).get(sys.argv[2],{}).get("prefix",""))' "$FV_ROOT/config/components.json" "$PROJ_TC_STR" 2>/dev/null || echo "")
  CMD=(env ${INCR_TC_PREFIX:+INCR_TC="$INCR_TC_PREFIX"} FASTVERIFY="$FV_ROOT" "$FV_ROOT/tools/incr/incr-reverify.sh" "$CACHE_DIR/base" "$PROJECT" "$CHALLENGE" "$RUN_DIR"
       --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --threads "$THREADS" --optimistic --integrity-cache "$ICACHE")
  [ -n "$PACKAGES" ] && CMD+=(--packages "$(readlink -f "$PACKAGES")")
  [ "$CLOSURE_ONLY" = 1 ] && CMD+=(--closure-only)
  [ -n "$EXPORT_DIR" ] && [ "$EXPORT_DIR" != "none" ] && CMD+=(--export-dir "$EXPORT_DIR")
  [ "$FRONTIER" = 1 ] && CMD+=(--keep-export)
  run_guarded incr "${CMD[@]}" > "$OUT_DIR/ci-run.log" 2>&1
  RUN_RC=$?
  # Update incremental base ONLY on ACCEPTED (never poison last good base on failed PR!)
  LAST_ATT=$(ls -d "$RUN_DIR"/a[0-9]-* 2>/dev/null | sort | tail -1 || true)
  if [ "$RUN_RC" = 0 ] && [ -n "$LAST_ATT" ] && [ -d "$LAST_ATT/work/proj" ] && [ -f "$LAST_ATT/work/log/plan.jsonl" ]; then
    NEW_BASE="$CACHE_DIR/base.next.$$"
    rm -rf "$NEW_BASE"
    mkdir -p "$NEW_BASE/work" "$NEW_BASE/log/build-fast"
    cp -a --reflink=auto "$CACHE_DIR/base/result.json" "$NEW_BASE/result.json"
    cp -a --reflink=auto "$CACHE_DIR/base/log/export-targets.txt" "$NEW_BASE/log/export-targets.txt"
    cp -a --reflink=auto "$LAST_ATT/work/log/plan.jsonl" "$NEW_BASE/log/build-fast/plan.jsonl"
    for x in fastexact planner; do
      [ -e "$CACHE_DIR/base/log/build-fast/$x" ] && cp -a --reflink=auto "$CACHE_DIR/base/log/build-fast/$x" "$NEW_BASE/log/build-fast/$x"
    done
    cp -a --reflink=auto "$LAST_ATT/work/proj" "$NEW_BASE/work/proj"
    rm -rf "$CACHE_DIR/base.old.$$"
    mv "$CACHE_DIR/base" "$CACHE_DIR/base.old.$$" && mv "$NEW_BASE" "$CACHE_DIR/base"
    rm -rf "$CACHE_DIR/base.old.$$"
  elif [ "$RUN_RC" = 2 ]; then
    # Incremental tool declined / could not run -> fall back cleanly to cold run
    USE_INCR=0
    rm -rf "$RUN_DIR"
  fi
fi

if [ "$USE_INCR" = 0 ]; then
  CACHE_MODE=cold
  INPUT_KIND=fastverify
  INPUT_FILE="$RUN_DIR/result.json"
  # Cold run (for cacheable incremental base, avoid module merging and native-pkg [finding 057 on module-system repos])
  CMD=("$FV_ROOT/bin/fastverify" "$PROJECT" "$CHALLENGE" "$RUN_DIR" --preset "$PRESET"
       --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN" --threads "$THREADS")
  [ -n "$PACKAGES" ] && CMD+=(--packages "$(readlink -f "$PACKAGES")")
  [ -n "$BUILD_OPT" ] && CMD+=(--build "$BUILD_OPT")
  [ -n "$EXPORT_DIR" ] && CMD+=(--export-dir "$EXPORT_DIR")
  [ "$CONFIRM_REJECT" = 1 ] && CMD+=(--confirm-reject)
  [ "$NO_INTEGRITY_CACHE" = 1 ] && CMD+=(--no-integrity-cache)
  [ -n "$PINS_FILE" ] && CMD+=(--pins "$PINS_FILE")
  if [ "$FRONTIER" = 1 ] && [ -z "$FRONTIER_AXIOMS" ]; then
    CMD+=(--modulo-frontier "${ALLOWED_FRONTIER:-auto}")
    [ -n "$FRONTIER_PINNED" ] && CMD+=(--frontier-pin "$(readlink -f "$FRONTIER_PINNED")")
    if [ -n "$CACHE_DIR" ]; then
      mkdir -p "$CACHE_DIR/acache" && chmod 700 "$CACHE_DIR/acache"
      [ -f "$CACHE_DIR/last-frontier.json" ] && CMD+=(--frontier-base "$CACHE_DIR/last-frontier.json")
    fi
  fi
  if [ -n "$CACHE_DIR" ] && [ "$PRESET" = "sound" ] && [ -z "$BUILD_OPT" ]; then
    # Keep unmerged work tree so subsequent commits can re-verify incrementally in seconds (portable PGO first, D21)
    UNSAFE="toolchain-T1=lean4-s01zy-3cf5641cbd-pgo-portable lean4-s01zy-3cf5641cbd-pgo lean4-v4.37.0-rc1-pgo-portable lean4-d5e35ef223-pgo-portable lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo-portable lean4-7586a50cec-nopgo,skip-kernel-tc=except-translate,linter-off,retries,premise-off,fast-exact,sound-fast-path=importarts-empty"
    CMD+=(--unsafe "$UNSAFE" --overlap-targets none --keep-work)
  elif [ -n "$CACHE_DIR" ]; then
    CMD+=(--keep-work)
  fi
  if [ "$FRONTIER" = 1 ]; then
    CMD+=(--keep-work)
  fi
  run_guarded cold "${CMD[@]}" > "$OUT_DIR/ci-run.log" 2>&1
  RUN_RC=$?
  if [ "$RUN_RC" = 0 ] && [ -n "$CACHE_DIR" ] && [ -d "$RUN_DIR/work/proj" ]; then
    rm -rf "$CACHE_DIR/base.old.$$"
    [ -d "$CACHE_DIR/base" ] && mv "$CACHE_DIR/base" "$CACHE_DIR/base.old.$$"
    mkdir -p "$CACHE_DIR/base/work" "$CACHE_DIR/base/log"
    cp -a --reflink=auto "$RUN_DIR/result.json" "$CACHE_DIR/base/result.json"
    cp -a --reflink=auto "$RUN_DIR/work/proj" "$CACHE_DIR/base/work/proj"
    [ -d "$RUN_DIR/log/build-fast" ] && cp -a --reflink=auto "$RUN_DIR/log/build-fast" "$CACHE_DIR/base/log/build-fast"
    [ -f "$RUN_DIR/log/export-targets.txt" ] && cp -a --reflink=auto "$RUN_DIR/log/export-targets.txt" "$CACHE_DIR/base/log/export-targets.txt"
    rm -rf "$CACHE_DIR/base.old.$$"
  fi
fi

# Day 1-99 conditional sorry-frontier mode (--frontier) on INCREMENTAL runs (or cold --frontier-axioms):
# Standard cold runs already ran bin/fastverify --modulo-frontier directly (skipping redundant check-sound).
# On incremental runs (or when a pinned --frontier-axioms file is supplied) where full sound check did not ACCEPT (RUN_RC != 0),
# judge the kept solution.export with D06's check/frontier/check-frontier.sh (--a-cache + --integrity-cache + --base; exit 3 = CONDITIONAL).
if [ "$FRONTIER" = 1 ] && [ "$RUN_RC" != 0 ] && { [ "$USE_INCR" = 1 ] || [ -n "$FRONTIER_AXIOMS" ]; }; then
  SOL_EXP=""
  for cand in "$RUN_DIR/solution.export" "$RUN_DIR"/a[0-9]-*/solution.export; do
    [ -f "$cand" ] && SOL_EXP="$cand"
  done
  if [ -n "$SOL_EXP" ] && [ -f "$CHALLENGE/challenge.export" ] && [ -f "$CHALLENGE/comparator.json" ]; then
    ACTUAL_PIN=$(sha256sum "$CHALLENGE/challenge.export" | awk '{print $1}')
    if [ "$ACTUAL_PIN" = "$PIN" ]; then
      FR_JSON="$OUT_DIR/frontier-check.json"
      FR_LOG="$OUT_DIR/frontier-check.log"
      FR_CMD=("$FV_ROOT/check/frontier/check-frontier.sh" "$SOL_EXP" "$CHALLENGE/challenge.export" "$CHALLENGE/comparator.json"
              --threads "$THREADS" --json "$FR_JSON" --log "$FR_LOG" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN")
      [ -n "$ALLOWED_FRONTIER" ] && FR_CMD+=(--allowed "$(readlink -f "$ALLOWED_FRONTIER")")
      [ -n "$FRONTIER_AXIOMS" ] && FR_CMD+=(--axioms "$(readlink -f "$FRONTIER_AXIOMS")")
      [ -n "$FRONTIER_PINNED" ] && FR_CMD+=(--pinned "$(readlink -f "$FRONTIER_PINNED")")
      if [ -n "$PINS_FILE" ]; then
        FR_CMD+=(--pins "$PINS_FILE")
      elif [[ "$PROJ_TC_STR" == *"v4.37"* ]] && [ -f "$FV_ROOT/check/sound/pins-437.env" ]; then
        FR_CMD+=(--pins "$FV_ROOT/check/sound/pins-437.env")
      fi
      if [ -n "$CACHE_DIR" ]; then
        mkdir -p "$CACHE_DIR/icache" "$CACHE_DIR/acache"
        chmod 700 "$CACHE_DIR/icache" "$CACHE_DIR/acache"
        FR_CMD+=(--integrity-cache "$CACHE_DIR/icache" --a-cache "$CACHE_DIR/acache")
        [ -f "$CACHE_DIR/last-frontier.json" ] && FR_CMD+=(--base "$CACHE_DIR/last-frontier.json")
      fi
      run_guarded frontier "${FR_CMD[@]}" >> "$OUT_DIR/ci-run.log" 2>&1; FR_RC=$?
      # the report counts only if THIS invocation wrote it and its exit agrees with the process status
      FR_REP_EXIT=$( [ -f "$FR_JSON" ] && /usr/bin/python3 -I -c 'import json,sys; e=json.load(open(sys.argv[1])).get("exit"); print(e if type(e) is int else "none")' "$FR_JSON" 2>/dev/null)
      case "$FR_RC" in
        0|1|3) if [ "$FR_REP_EXIT" = "$FR_RC" ]; then INPUT_KIND=frontier; INPUT_FILE="$FR_JSON"; fi;;
      esac
      if [ "$INPUT_KIND" != frontier ]; then
        echo "fv-ci.sh: the frontier check did not complete consistently (exit $FR_RC, report exit ${FR_REP_EXIT:-none}): not used" >> "$OUT_DIR/ci-run.log"
        rm -f "$FR_JSON"
      fi
    fi
  fi
fi

# If fvguard killed any stage due to wall/mem/disk limit (exit 125), map strictly to fail-closed NO-VERDICT (exit 2)
if [ "$GUARD_VIOLATED" = 1 ] && [ -n "$GUARD_STEP_JSON" ] && [ -f "$GUARD_STEP_JSON" ]; then
  /usr/bin/python3 -I - "$FV_ROOT" "$GUARD_STEP_JSON" "$OUT_DIR/guard-noverdict.json" "$PROJECT" "$CHALLENGE" "$PIN" "$T0" <<'PY'
import json, os, sys, time
fv_root, gj_p, out_p, proj, chal, pin, t0 = sys.argv[1:8]
sys.path.insert(0, os.path.join(fv_root, "schemas"))
import fv_schema
gj = json.load(open(gj_p, encoding="utf-8"))
viol = gj.get("violation") or "limit"
detail = gj.get("detail") or f"fvguard resource violation: {viol}"
env = fv_schema.make_envelope(
    mode="project", verdict="NO-VERDICT", trust="sound",
    verdict_basis=f"fvguard CI resource limit exceeded ({viol}): {detail} (fail-closed, never a verdict)",
    total_s=max(0.0, time.time() - float(t0)),
    reason=f"resource_limit:{viol}: {detail}",
    target={"project": proj, "challenge": chal, "challenge_sha256": pin},
    diagnostics=fv_schema.classify_verdict_diagnostic("NO-VERDICT", detail),
    raw={"fvguard": gj},
)
with open(out_p, "w", encoding="utf-8") as f:
    json.dump(env, f, indent=2)
PY
  INPUT_KIND=v1
  INPUT_FILE="$OUT_DIR/guard-noverdict.json"
fi

T1=$(date +%s.%N)
WALL=$(/usr/bin/python3 -I -c "print(round(float('$T1') - float('$T0'), 4))")

RARGS=(
  --input-kind "$INPUT_KIND"
  --input "$INPUT_FILE"
  --out-json "$OUT_DIR/result-v1.json"
  --out-sarif "$OUT_DIR/results.sarif"
  --out-md "$OUT_DIR/summary.md"
  --cache-mode "$CACHE_MODE"
  --project "$PROJECT"
  --challenge "$CHALLENGE"
  --challenge-sha256 "$PIN"
  --wall-s "$WALL"
)
[ -n "$COMMIT" ] && RARGS+=(--commit "$COMMIT")
[ -n "$PREV_V1" ] && RARGS+=(--prev-v1 "$PREV_V1")

/usr/bin/python3 -I "$HERE/render_ci_report.py" "${RARGS[@]}"
OUT_RC=$?
# In Day 1-99 --frontier mode, also advance the untrusted incremental build cache on CONDITIONAL (exit 3)
# so Days 2..99 get seconds-level incremental rebuilds (still NEVER cached on REJECTED/NO-VERDICT!).
if [ "$OUT_RC" = 3 ] && [ "$FRONTIER" = 1 ] && [ -n "$CACHE_DIR" ]; then
  if [ "$CACHE_MODE" = "incremental" ]; then
    LAST_ATT=$(ls -d "$RUN_DIR"/a[0-9]-* 2>/dev/null | sort | tail -1 || true)
    if [ -n "$LAST_ATT" ] && [ -d "$LAST_ATT/work/proj" ] && [ -f "$LAST_ATT/work/log/plan.jsonl" ]; then
      NEW_BASE="$CACHE_DIR/base.next.$$"
      rm -rf "$NEW_BASE"
      mkdir -p "$NEW_BASE/work" "$NEW_BASE/log/build-fast"
      cp -a --reflink=auto "$CACHE_DIR/base/result.json" "$NEW_BASE/result.json"
      cp -a --reflink=auto "$CACHE_DIR/base/log/export-targets.txt" "$NEW_BASE/log/export-targets.txt"
      cp -a --reflink=auto "$LAST_ATT/work/log/plan.jsonl" "$NEW_BASE/log/build-fast/plan.jsonl"
      for x in fastexact planner; do
        [ -e "$CACHE_DIR/base/log/build-fast/$x" ] && cp -a --reflink=auto "$CACHE_DIR/base/log/build-fast/$x" "$NEW_BASE/log/build-fast/$x"
      done
      cp -a --reflink=auto "$LAST_ATT/work/proj" "$NEW_BASE/work/proj"
      rm -rf "$CACHE_DIR/base.old.$$"
      mv "$CACHE_DIR/base" "$CACHE_DIR/base.old.$$" && mv "$NEW_BASE" "$CACHE_DIR/base"
      rm -rf "$CACHE_DIR/base.old.$$"
    fi
  elif [ -d "$RUN_DIR/work/proj" ] && [ -f "$RUN_DIR/result.json" ]; then
    rm -rf "$CACHE_DIR/base.old.$$"
    [ -d "$CACHE_DIR/base" ] && mv "$CACHE_DIR/base" "$CACHE_DIR/base.old.$$"
    mkdir -p "$CACHE_DIR/base/work" "$CACHE_DIR/base/log"
    cp -a --reflink=auto "$RUN_DIR/result.json" "$CACHE_DIR/base/result.json"
    cp -a --reflink=auto "$RUN_DIR/work/proj" "$CACHE_DIR/base/work/proj"
    [ -d "$RUN_DIR/log/build-fast" ] && cp -a --reflink=auto "$RUN_DIR/log/build-fast" "$CACHE_DIR/base/log/build-fast"
    [ -f "$RUN_DIR/log/export-targets.txt" ] && cp -a --reflink=auto "$RUN_DIR/log/export-targets.txt" "$CACHE_DIR/base/log/export-targets.txt"
    rm -rf "$CACHE_DIR/base.old.$$"
  fi
fi
if { [ "$OUT_RC" = 0 ] || [ "$OUT_RC" = 3 ]; } && [ -n "$CACHE_DIR" ]; then
  cp -f "$OUT_DIR/result-v1.json" "$CACHE_DIR/last-v1.json"
  if [ -n "${FR_JSON:-}" ] && [ -f "${FR_JSON:-}" ]; then
    cp -f "$FR_JSON" "$CACHE_DIR/last-frontier.json"
  elif [ "$FRONTIER" = 1 ] && [ -f "$RUN_DIR/result.json" ]; then
    cp -f "$RUN_DIR/result.json" "$CACHE_DIR/last-frontier.json"
  fi
fi
exit "$OUT_RC"
