#!/bin/bash
# tools/incr/incr-reverify.sh — re-verification of an EDITED project after an earlier sound run.
#
#   incr-reverify.sh BASE_OUT NEW_SOURCES CHALLENGE OUT --challenge-sha256 HEX [--threads N] [--packages WS]
#                    [--warm PREV_EXPORT] [--optimistic] [--reuse-plan] [--no-fast-exact] [--orchestrator] [--closure-only]
#
#   BASE_OUT     OUT of an earlier `bin/fastverify ... --preset sound --unsafe <list without merge> --keep-work` run of the
#                same project (its work/proj tree with the built .olean files and log/build-fast/plan.jsonl are reused,
#                read-only: the new tree is a reflink/full copy, or with --hardlink (trusted edits only) a hard-linked copy).
#   NEW_SOURCES  the edited project.   CHALLENGE  dir with comparator.json + the official challenge.export (pinned).
#   OUT          fresh directory.
#   --warm PREV_EXPORT  WARM VERIFIER: a `pleanchecker --incremental` server (the pinned pleanchecker_incr in full mode,
#                started exactly by overlap/incr-server.sh) is given PREV_EXPORT (e.g. the base run's export) as an UNTRUSTED
#                snapshot and is warmed up BEFORE the edit is timed (warm-up time reported separately); the Lean-kernel leg
#                of the check then attaches to it (check-sound.sh --incr-dir): only constants that are new or differ from
#                checked ones (and their dependents) are replayed. ccmp and gruszka judge the whole export as always.
#   DEFAULT (v0.1): the COLD sound path - bin/fastverify --preset sound on NEW; BASE_OUT is not used, the options
#                below only steer the EXPERIMENTAL incremental machinery and are ignored without --experimental-incremental.
#   --experimental-incremental  EXPERIMENTAL (not part of v0.1): the incremental machinery below; its ACCEPTED is never
#                counted (NO VERDICT, "provisional": "ACCEPTED", trust none). Its own default is EXACT:
#                every reverse dependency of every changed module is rebuilt (what a fresh build rebuilds);
#                tools/incr/incr-build.py also forces a full build on non-module changes or elaboration-time code and
#                verifies that the outputs are the submitted tree's (else exit 2 = no verdict).
#   --optimistic EXPERIMENTAL: first rebuild only the edited modules (importers keep their outputs) and check. A kept importer
#                can hold what it obtained at elaboration time from the OLD module (macros, tactics, instances), so an
#                ACCEPTED of such a build is only provisional: it is confirmed by an exact build (that verdict is final);
#                a non-ACCEPTED is retried exactly too.
#   --optimistic-only  EXPERIMENTAL: the first attempt only: a REJECT is final (trust none); an ACCEPTED of a build that kept
#                importers is NOT counted (NO VERDICT, "provisional": "ACCEPTED").
#   --interface  EXPERIMENTAL: Lake-like waves (the edited modules, then only importers of modules whose PUBLIC artifacts
#                changed); a non-ACCEPTED, or an ACCEPTED of a build that kept importers, is redone exactly.
#   --reuse-plan skip Lake's planner when only .lean bodies changed (import headers unchanged).
#   --integrity-cache DIR  the check runs as check/sound/check-sound-svc.sh --integrity-cache DIR (the service variant:
#                the pins + 4.36 tree are fully verified once, later runs compare a stamp; judge unchanged).
#   --closure-only  rebuild only modules in the import closure of the comparator's solution module (what the official
#                4.36 `lake comparator` builds); edits outside it cost nothing but the export + check.
#   --orchestrator  check through bin/fastverify - CHALLENGE OUT --from-export ... --preset sound (adds its preflight,
#                ~10 s); default: check/sound/check-sound.sh after comparing challenge.export with the pin.
#   --packages WS  the trusted Lake workspace with materialized dependencies (default: $FV_PACKAGES, else
#                <repository root>/verify/challenge).
#
# Stages per attempt: (1) tools/incr/incr-build.py (UNTRUSTED: sound-preset transforms skip-kernel-tc, linter-off, the
# base run's T1 toolchain and fast-exact plugin), (2) export/export.sh (E1, untrusted, closure guard), (3) the TRUSTED sound
# check. The verdict is the trusted check's on the export (README 1b: build and export are untrusted).
# Output: OUT/summary.json (+ last stdout line); exit = the final check's exit (0 ACCEPTED, 1 REJECTED, 2 no verdict).
set -u
# v0.1: by default NEW is verified by the COLD sound path - bin/fastverify --preset sound on NEW
# (its own toolchain resolution, fresh build, export and trusted check); BASE_OUT and every incremental artefact are unused.
# Options that only steer the incremental machinery are ignored (listed in summary.json "ignored"); the machinery itself
# runs only with --experimental-incremental, and its ACCEPTED is never counted (NO VERDICT, "provisional").
cold_path() {
  [ -n "$CSHA" ] || { echo "incr-reverify: --challenge-sha256 is required (sound mode)" >&2; return 2; }
  mkdir -p "$OUT" && OUT=$(readlink -f "$OUT") || return 2
  [ -z "$(ls -A "$OUT")" ] || { echo "incr-reverify: $OUT not empty" >&2; return 2; }
  local xa=() t0 t1 rc csha
  [ -n "$EXPD" ] && xa+=(--export-dir "$EXPD")
  # scheme 2: the CALLER's pin (required, checked above) is compared with the config passed and forwarded
  csha=$(sha256sum < "$CH/comparator.json" 2>/dev/null | cut -c1-64)
  [ -n "$csha" ] || { echo "incr-reverify: $CH/comparator.json unreadable" >&2; return 2; }
  if [ "$CMPSHA" != "$csha" ]; then
    echo "incr-reverify: comparator config sha256 $csha != --comparator-sha256 $CMPSHA: refused (no verdict)" >&2; return 2
  fi
  xa+=(--comparator-sha256 "$CMPSHA")
  # options that steer only the incremental machinery: ignored here (recorded)
  case "$OPT" in 1) IGN+=(--optimistic) ;; 2) IGN+=(--optimistic-only) ;; 3) IGN+=(--interface) ;; esac
  [ ${#RP[@]} -gt 0 ] && IGN+=(--reuse-plan); [ ${#XA2[@]} -gt 0 ] && IGN+=(--hardlink); [ -n "$LEANX" ] && IGN+=(--lean)
  [ "$NOKTC" = 1 ] && IGN+=(--no-skip-kernel-tc); [ "$CLOS" = 1 ] && IGN+=(--closure-only); [ -n "$ICACHE" ] && IGN+=(--integrity-cache)
  [ -n "$WARM" ] && IGN+=(--warm); [ "$FX" = 0 ] && IGN+=(--no-fast-exact); [ "$ORCH" = 1 ] && IGN+=(--orchestrator)
  [ "$KEEPX" = 1 ] && IGN+=(--keep-export)
  t0=$(date +%s.%N)
  # NEW is staged ONCE (only bin/fastverify's own exclusion, the top-level .lake): every attempt of the cold
  # run (incl. its official confirmation build) reads this private copy, never the caller's live directory again
  rsync -a --exclude=/.lake "$NEW/" "$OUT/src/" 2> "$OUT/stage.err" || { echo "incr-reverify: cannot stage $NEW (no verdict)" >&2; return 2; }
  "$PKG/bin/fastverify" "$OUT/src" "$CH" "$OUT/cold" --preset sound --threads "$T" --packages "$WS" --challenge-sha256 "$CSHA" \
    "${xa[@]}" > "$OUT/cold.log" 2>&1
  rc=$?; t1=$(date +%s.%N)
  python3 -I - "$OUT" "$rc" "$t0" "$t1" "${IGN[*]:-}" <<'PYCOLD'
import json, os, sys
out, rc, t0, t1, ign = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
try:
    res = json.load(open(os.path.join(out, "cold", "result.json")))
except (OSError, ValueError):
    res = {}
want = {0: "ACCEPTED", 1: "REJECTED"}.get(rc)
v = res.get("verdict")
if want is None or v != want:   # the exit and the recorded verdict must agree; anything else is no verdict
    rc, verdict = 2, "NO VERDICT"
else:
    verdict = want
r = {"verdict": verdict, "exit": rc, "mode": "cold", "total_s": round(t1 - t0, 2), "attempts": [],
     "cold": {"result": os.path.join(out, "cold", "result.json"), "verdict": v, "exit": int(sys.argv[2]),
              "reason": str(res.get("verdict_basis") or res.get("reason") or res.get("why") or "")[:500]}}
if ign:
    r["ignored"] = ign.split()
try:   # the summary first; a failed write is no verdict (exit 2), never a stray exit 1
    with open(os.path.join(out, "summary.json"), "w") as f:
        json.dump(r, f, indent=1)
except OSError as e:
    r = {"verdict": "NO VERDICT", "exit": 2, "mode": "cold", "why": f"cannot write summary.json: {e}"}
    rc = 2
print(json.dumps(r))
sys.exit(rc)
PYCOLD
}
main() {
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); PKG=${FASTVERIFY:-$(cd "$H/../.." && pwd)}   # FASTVERIFY = package root
[ $# -ge 4 ] || { sed -n 3,5p "$0" >&2; exit 2; }
# strict path resolution: an empty argument or a path that does not resolve (e.g. a missing
# parent) is a usage error (exit 2); never '' (which would make the staging copy '/' ) or a guessed directory
[ -n "$1" ] && [ -n "$2" ] && [ -n "$3" ] && [ -n "$4" ] || { echo "incr-reverify: empty path argument (no verdict)" >&2; exit 2; }
NEW=$(readlink -e -- "$2") && [ -d "$NEW" ] && [ "$NEW" != / ] || { echo "incr-reverify: NEW_SOURCES '$2' does not resolve to a project directory (no verdict)" >&2; exit 2; }
CH=$(readlink -e -- "$3") && [ -d "$CH" ] && [ "$CH" != / ] || { echo "incr-reverify: CHALLENGE '$3' does not resolve to a directory (no verdict)" >&2; exit 2; }
BASE=$(readlink -f -- "$1"); OUT=$4; shift 4   # BASE: read only by the EXPERIMENTAL path (checked there)
EXPINC=0; IGN=(); CMPSHA=
T=$(nproc); WS=${FV_PACKAGES:-$(dirname "$PKG")/verify/challenge}; CSHA=; WARM=; WDAEMON=; WMAN=; WBINS=/scratch/fastverify-next/warm/v1; WSRC=; FX=1; ORCH=0; OPT=0; RP=(); LEANX=; EXPD=; KEEPX=0; XA2=(); NOKTC=0; CLOS=0; ICACHE=
while [ $# -gt 0 ]; do
  case "$1" in   # an option without its value is a usage error (exit 2), never `set -u`'s exit 1
    --threads|--packages|--challenge-sha256|--warm|--warm-manifest|--warm-bins|--warm-src|--lean|--export-dir|--integrity-cache|--toolchain)
      [ $# -ge 2 ] || { echo "incr-reverify: $1 needs a value" >&2; exit 2; } ;;
  esac
  case "$1" in
    --threads) T=$2; shift 2 ;;
    --experimental-incremental) EXPINC=1; shift ;;   # EXPERIMENTAL: the incremental machinery (never counted)
    --comparator-sha256) [ $# -ge 2 ] || { echo "incr-reverify: $1 needs a value" >&2; exit 2; }; CMPSHA=$2; shift 2 ;;   # the caller's pin of CHALLENGE/comparator.json (cold path); same value check as the block above
    --packages) WS=$2; shift 2 ;;
    --challenge-sha256) CSHA=$2; shift 2 ;;
    --warm) WARM=$(readlink -f "$2"); shift 2 ;;
    --warm-daemon) echo "incr-reverify: --warm-daemon is not available in this release (the served base tree and the warm daemon can desynchronise); run without it" >&2; exit 2 ;; # opt-in persistent 3-leg fvcheckd state dir (delta export + warm check)
    --warm-manifest) WMAN=$(readlink -f "$2"); IGN+=(--warm-manifest); shift 2 ;;   # optional base_consts.txt for Tier-2 --exclude retry
    --warm-bins) WBINS=$(readlink -f "$2"); IGN+=(--warm-bins); shift 2 ;;      # dir with lean4export-delta (default: the install prefix /scratch/fastverify-next/warm/v1)
    --warm-src) WSRC=$(readlink -f "$2"); IGN+=(--warm-src); shift 2 ;;        # dir with fvcheckd.py (default $PKG/check/warm)
    --no-fast-exact) FX=0; shift ;;
    --orchestrator) ORCH=1; shift ;;
    --optimistic) OPT=1; shift ;;
    --optimistic-only) OPT=2; shift ;;
    --interface) OPT=3; shift ;;          # Lake-like waves (module system: importers only if the public artifacts changed); full rebuild if not ACCEPTED    # no second attempt (e.g. candidate proofs of a FIXED statement: a reject is final)
    --reuse-plan) RP=(--reuse-plan); shift ;;
    --hardlink) XA2+=(--hardlink); shift ;;   # trusted edits only: hard-linked instead of reflink/full copy
    --lean) LEANX=$2; shift 2 ;;          # lean binary for the rebuilt modules (default: the base run's T1 toolchain)
    --export-dir) EXPD=$2; shift 2 ;;     # write the (untrusted) exports there (e.g. /dev/shm), removed at the end
    --keep-export) KEEPX=1; shift ;;
    --no-skip-kernel-tc) NOKTC=1; shift ;;
    --closure-only) CLOS=1; shift ;;      # rebuild only within the import closure of the solution module (= what lake comparator builds)
    --integrity-cache) ICACHE=$2; shift 2 ;;   # check via check-sound-svc.sh --integrity-cache DIR (the service variant)
    *) echo "incr-reverify: unknown argument $1" >&2; exit 2 ;;
  esac
done
# comparator pin scheme 2: wherever --challenge-sha256 is required or given, the CALLER must give
# --comparator-sha256 (64 hex); a wrapper never computes it from the file it is about to judge; an empty pin is a usage error
if [ -n "$CSHA" ] || [ "$EXPINC" != 1 ]; then
  [[ "$CMPSHA" =~ ^[0-9a-f]{64}$ ]] || { echo "incr-reverify: --comparator-sha256 HEX (64 hex, the caller's pin of CHALLENGE/comparator.json) is required with --challenge-sha256 (scheme 2)" >&2; exit 2; }
fi
if [ "$EXPINC" != 1 ]; then cold_path; exit $?; fi   # (v0.1 default) the COLD sound verification of NEW
[ -n "$BASE" ] && [ -d "$BASE" ] && [ "$BASE" != / ] || { echo "incr-reverify: BASE_OUT '$BASE' is not a directory (no verdict)" >&2; exit 2; }   # strict path check
[ -n "$CSHA" ] || { echo "incr-reverify: --challenge-sha256 is required (sound mode)" >&2; exit 2; }
[ -d "$WS" ] || { echo "incr-reverify: no trusted package workspace at $WS (pass --packages WS or set FV_PACKAGES)" >&2; exit 2; }
mkdir -p "$OUT" && OUT=$(readlink -f "$OUT") || exit 2
[ -z "$(ls -A "$OUT")" ] || { echo "incr-reverify: $OUT not empty" >&2; exit 2; }
[ "$(sha256sum "$CH/challenge.export" | cut -d' ' -f1)" = "$CSHA" ] || { echo "incr-reverify: challenge export != pin" >&2; exit 2; }
TC=${INCR_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}   # official 4.33.1 prefix (planner, E1); node-local copy via INCR_TC
UNS=$(python3 -I -c 'import json,sys; print(",".join(json.load(open(sys.argv[1]))["build"]["attempts"][0]["stage"]["unsafe"]))' "$BASE/result.json" 2>/dev/null)
T1=$(printf '%s' "$UNS" | tr ',' '\n' | sed -n 's/^toolchain-T1://p')
# build transforms of the rebuilt modules: the base run's (B3) items skip-kernel-tc / linter-off; a B1/B2 base (no items)
# gets both (the sound preset's); --no-skip-kernel-tc drops the first (e.g. Mathlib as the project: @[to_dual] needs the
# build-time kernel check)
XA=()
if [ -z "$UNS" ] || printf '%s' "$UNS" | tr ',' '\n' | grep -qx 'skip-kernel-tc'; then [ "$NOKTC" = 1 ] || XA+=(--extra-arg=-Ddebug.skipKernelTC=true); fi
# the base's skip-kernel-tc=except-translate: skip it too, except in modules that mention to_additive / to_dual
if printf '%s' "$UNS" | tr ',' '\n' | grep -qx 'skip-kernel-tc=except-translate' && [ "$NOKTC" != 1 ]; then XA+=(--extra-arg=-Ddebug.skipKernelTC=true --ktc-exempt-translate); fi
if [ -z "$UNS" ] || printf '%s' "$UNS" | tr ',' '\n' | grep -qx 'linter-off'; then XA+=(--extra-arg=-Dlinter.all=false); fi
if [ -n "$LEANX" ]; then XA+=(--lean "$LEANX")
elif [ -n "$T1" ] && [ -x "/scratch/fastverify-next/tc/$T1/bin/lean" ]; then XA+=(--lean "/scratch/fastverify-next/tc/$T1/bin/lean"); fi
PL=$BASE/log/build-fast/fastexact/libLightFastExact.so
[ "$FX" = 1 ] && [ -f "$PL" ] && grep -q '^active' "$BASE/log/build-fast/fastexact/STATUS" 2>/dev/null && XA+=(--plugin "$PL")
PLANNER=$BASE/log/build-fast/planner/planner; [ -x "$PLANNER" ] && XA+=(--planner "$PLANNER")
CM=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$CH/comparator.json")
[ "$CLOS" = 1 ] && XA+=(--closure-of "$CM")
# a base built with sound-fast-path=importarts-empty is re-planned the same way (else the planner walks every
# module's transitive importArts: formal-conjectures 485 s, 4.7 GB plan)
printf '%s' "$UNS" | tr ',' '\n' | grep -qx 'sound-fast-path=importarts-empty' && XA+=(--import-arts-empty)
cp "$BASE/log/export-targets.txt" "$OUT/targets.txt" || exit 2   # theorem names + the comparator's primitives/axioms
ET=$T; [ "$ET" -gt 128 ] && ET=128
CSH=$PKG/check/sound/check-sound.sh; CSX=()
if [ -n "$ICACHE" ]; then CSH=$PKG/check/sound/check-sound-svc.sh; CSX=(--integrity-cache "$ICACHE"); fi
# ---- warm verifier (before the edit is timed)
SPID=; HOLD=; tw0=$(date +%s.%N)
if [ -n "$WARM" ]; then
  PLC=$(awk '$1=="PIN" && $2=="pleanchecker_incr" {print $4}' "$PKG/check/sound/pins.env")
  mkdir -p "$OUT/incr"
  INCR_NICE=0 "$PKG/overlap/incr-server.sh" "$OUT/incr" "$PLC" "$T" > /dev/null 2>&1 & SPID=$!
  for i in $(seq 1 100); do [ -p "$OUT/incr/cmd" ] && break; sleep 0.1; done
  ( exec 3> "$OUT/incr/cmd"; printf 'snap %s\n' "$WARM" >&3; exec sleep infinity ) & HOLD=$!
  while ! grep -q 'snapshot 1 ingested\|snapshot dropped' "$OUT/incr/server.log" 2>/dev/null; do
    kill -0 $SPID 2>/dev/null || { echo "incr-reverify: warm server died (see $OUT/incr/server.log)" >&2; break; }; sleep 0.2; done
fi
tw1=$(date +%s.%N)
stop_server() { [ -n "$HOLD" ] && kill "$HOLD" 2>/dev/null; [ -n "$SPID" ] && { pkill -P "$SPID" 2>/dev/null; kill "$SPID" 2>/dev/null; }; HOLD=; SPID=; }
trap stop_server EXIT
attempt() {  # attempt DIR [--optimistic] -> DIR/{build.json,export.json,check.json,times}; returns the check's exit
  local d=$1; shift; mkdir -p "$d"
  local a0 a1 a2 a3 brc erc crc
  a0=$(date +%s.%N)
  python3 -I "$H/incr-build.py" --base "$BASE/work/proj" --base-plan "$BASE/log/build-fast/plan.jsonl" --src "$NEW" \
    --work "$d/work" --packages "$WS" --tc "$TC" --threads "$T" "${XA[@]}" "${XA2[@]}" "${RP[@]}" "$@" --json "$d/build.json" \
    > "$d/build.out" 2>&1
  brc=$?; a1=$(date +%s.%N)
  if [ $brc != 0 ]; then echo "$a0 $a1 $a1 $a1 build$brc" > "$d/times"; return $([ $brc = 1 ] && echo 1 || echo 2); fi
  if [ -n "$WDAEMON" ]; then
    local wsrc=${WSRC:-$PKG/check/warm}
    local exsh=$PKG/tools/delta-export/export-delta.sh
    [ -x "$exsh" ] || exsh=$wsrc/export-delta.sh
    local dm_f=$d/dirty_mods.txt
    python3 -I - "$d/work/log" "$dm_f" <<'PYDM'
import glob, json, os, sys
logd, outp = sys.argv[1], sys.argv[2]
mods = []
seen = set()
for fp in sorted(glob.glob(os.path.join(logd, "plan-incr*.jsonl"))):
    with open(fp, "r", encoding="utf-8", errors="replace") as f:
        for ln in f:
            try:
                o = json.loads(ln)
            except Exception:
                continue
            nm = o.get("name")
            if nm and nm not in seen:
                seen.add(nm)
                mods.append(nm)
open(outp, "w", encoding="utf-8").write("\n".join(mods) + ("\n" if mods else ""))
PYDM
    local dx=$d/delta.ndjson
    if [ -s "$dm_f" ]; then
      "$exsh" "$d/work/proj" "@$dm_f" "$dx" --packages "$WS" --toolchain "$TC" --bin "$WBINS/lean4export-delta" --threads 1 > "$d/export.out" 2>&1
      erc=$?
    else
      printf '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"version":"4.33.1"}}}\n' > "$dx"
      erc=0
    fi
    a2=$(date +%s.%N)
    if [ $erc = 0 ] && [ -s "$dx" ]; then
      chmod 444 "$dx"
      python3 -I "$wsrc/fvcheckd.py" check-delta --state "$WDAEMON" --delta "$dx" --config "$CH/comparator.json" > "$d/check.json" 2> "$d/check.out"
      crc=$?
      # Tier-2 auto-retry if a newly-used Mathlib lemma is missing from base
      if [ $crc = 1 ] && [ -n "$WMAN" ] && [ -f "$WMAN" ] && [ -s "$dm_f" ] \
         && grep -qiE 'not found|unknown constant|missing constant|unknown declaration' "$d/check.json"; then
        local dx2=$d/delta_t2.ndjson
        "$exsh" "$d/work/proj" "@$dm_f" "$dx2" --packages "$WS" --toolchain "$TC" --bin "$WBINS/lean4export-delta" --threads "$ET" --exclude "$WMAN" >> "$d/export.out" 2>&1
        if [ $? = 0 ] && [ -s "$dx2" ]; then
          chmod 444 "$dx2"; dx=$dx2; a2=$(date +%s.%N)
          python3 -I "$wsrc/fvcheckd.py" check-delta --state "$WDAEMON" --delta "$dx" --config "$CH/comparator.json" > "$d/check.json" 2> "$d/check.out"
          crc=$?
        fi
      fi
      # Only fall through to full cold export + check if FALLBACK_REQUIRED
      if ! grep -q '"FALLBACK_REQUIRED"' "$d/check.json" 2>/dev/null; then
        a3=$(date +%s.%N)
        echo "$a0 $a1 $a2 $a3 check$crc" > "$d/times"
        stat -L -c %s "$dx" > "$d/export.size" 2>/dev/null
        return $crc
      fi
    fi
  fi
  local xo=$d/solution.export
  if [ -n "$EXPD" ]; then xo=$(mktemp -d "$EXPD/incr-export.XXXXXX")/solution.export; ln -s "$xo" "$d/solution.export"; fi
  "$PKG/export/export.sh" --lean-path "$(cat "$d/work/log/lean_path.txt")" --module "$CM" --targets-nl "$OUT/targets.txt" \
    --toolchain "$TC" --project "$d/work/proj" --binds "$d/work/log/binds.tsv" --out "$xo" \
    --threads "$ET" --json "$d/export.json" > "$d/export.out" 2>&1
  erc=$?; a2=$(date +%s.%N)
  if [ $erc != 0 ]; then echo "$a0 $a1 $a2 $a2 export$erc" > "$d/times"; return 2; fi
  chmod 444 "$xo"
  if [ "$ORCH" = 1 ]; then
    "$PKG/bin/fastverify" - "$CH" "$d/check" --from-export "$d/solution.export" --preset sound --threads "$T" \
      --challenge-sha256 "$CSHA" > "$d/check.out" 2>&1
  elif [ -n "$SPID" ] && kill -0 "$SPID" 2>/dev/null; then
    "$CSH" "$d/solution.export" "$CH/challenge.export" "$CH/comparator.json" --threads "$T" "${CSX[@]}" \
      --incr-dir "$OUT/incr" --json "$d/check.json" --log "$d/check.log" > "$d/check.out" 2>&1
  else
    "$CSH" "$d/solution.export" "$CH/challenge.export" "$CH/comparator.json" --threads "$T" "${CSX[@]}" \
      --json "$d/check.json" --log "$d/check.log" > "$d/check.out" 2>&1
  fi
  crc=$?; a3=$(date +%s.%N)
  echo "$a0 $a1 $a2 $a3 check$crc" > "$d/times"
  stat -L -c %s "$d/solution.export" > "$d/export.size" 2>/dev/null
  if [ -n "$EXPD" ] && [ "$KEEPX" = 0 ]; then rm -f "$xo"; rmdir "$(dirname "$xo")" 2>/dev/null; fi
  return $crc
}
# a build that kept importers of a changed module is not exact; its ACCEPTED is never final
inexact() { ! grep -q '"exact": true' "$1/build.json" 2>/dev/null; }
PROVISIONAL=
if [ "$OPT" = 3 ]; then
  attempt "$OUT/a1-interface" --interface; rc=$?
  if { [ $rc != 0 ] && ! grep -q ' build1$' "$OUT/a1-interface/times"; } || { [ $rc = 0 ] && inexact "$OUT/a1-interface"; }; then
    stop_server
    attempt "$OUT/a2-full"; rc=$?
  fi
elif [ "$OPT" != 0 ]; then
  attempt "$OUT/a1-optimistic" --optimistic; rc=$?
  if [ "$OPT" = 1 ] && [ $rc != 0 ] && grep -q '"optimistic": true' "$OUT/a1-optimistic/build.json" 2>/dev/null \
     && ! grep -q ' build1$' "$OUT/a1-optimistic/times"; then
    # not accepted with stale importers: rebuild them too (the server, if any, judged the first export and exited)
    stop_server
    attempt "$OUT/a2-full"; rc=$?
  elif [ $rc = 0 ] && inexact "$OUT/a1-optimistic"; then
    if [ "$OPT" = 1 ]; then   # a provisional ACCEPTED: confirmed (or not) by the exact build
      stop_server
      attempt "$OUT/a2-full"; rc=$?
    else                      # --optimistic-only: no confirmation run -> not counted
      PROVISIONAL=ACCEPTED; rc=2
    fi
  fi
else
  attempt "$OUT/a1-full"; rc=$?
fi
stop_server
if [ $rc = 0 ]; then PROVISIONAL=ACCEPTED; rc=2; fi   # --experimental-incremental: never a counted ACCEPTED
if [ $rc = 1 ]; then PROVISIONAL=REJECTED; rc=2; fi   # nor a counted REJECTED: nothing of it is sound
python3 -I - "$OUT" "$tw0" "$tw1" "$rc" "${WARM:-}" "$OPT" "$PROVISIONAL" <<'EOF'
import json, sys, os, glob
out, tw0, tw1, rc, warm = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
r = {"verdict": {0: "ACCEPTED", 1: "REJECTED"}.get(rc, "NO VERDICT"), "exit": rc, "warm": bool(warm),
     "warmup_s": round(tw1 - tw0, 2), "attempts": []}
r["mode"] = {"0": "exact", "1": "optimistic", "2": "optimistic-only", "3": "interface"}.get(sys.argv[6], sys.argv[6]) + \
    " (EXPERIMENTAL incremental)"
r["trust"] = "none"
if sys.argv[7]:   # an ACCEPTED of a build that kept importers, not confirmed: never counted
    r["provisional"] = sys.argv[7]
    r["trust"] = "none"
tot = 0.0
for d in sorted(glob.glob(os.path.join(out, "a[0-9]-*"))):
    t = open(os.path.join(d, "times")).read().split()
    a0, a1, a2, a3 = map(float, t[:4])
    x = {"attempt": os.path.basename(d), "outcome": t[4], "build_s": round(a1 - a0, 2), "export_s": round(a2 - a1, 2),
         "check_s": round(a3 - a2, 2), "total_s": round(a3 - a0, 2)}
    tot += a3 - a0
    try:
        b = json.load(open(os.path.join(d, "build.json")))
        x.update({k: b.get(k) for k in ("optimistic", "exact", "full_build_why", "stale", "interface_waves", "plan_reused", "modules", "seed", "dirty", "dirty_full", "copy_s",
                                         "sync_s", "plan_s", "sum_module_wall_s", "max_module_wall_s", "changed")})
    except Exception:  # noqa: BLE001
        pass
    try:
        x["export_bytes"] = int(open(os.path.join(d, "export.size")).read())
    except Exception:  # noqa: BLE001
        pass
    for f in ("check.json", "check/result.json"):
        try:
            c = json.load(open(os.path.join(d, f)))
            x["check"] = {k: c.get(k) for k in ("verdict", "exit", "reason", "trust", "verdict_basis") if k in c}
            break
        except Exception:  # noqa: BLE001
            pass
    r["attempts"].append(x)
r["total_s"] = round(tot, 2)
if warm:
    try:
        r["server_tail"] = [l.strip()[:300] for l in open(os.path.join(out, "incr", "server.log")) if "[incr]" in l][-5:]
    except OSError:
        pass
print(json.dumps(r))
with open(os.path.join(out, "summary.json"), "w") as f:
    json.dump(r, f, indent=1)
EOF
exit $rc
}
main "$@"
