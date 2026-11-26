#!/bin/bash
# Integrated full-RH pipeline (organization; optional LEAN_TC / LEAN4EXPORT_BIN from the harness).
# usage: pipeline.sh PRISTINE WORK  -> WORK/solution.export   (env: EVAL_CPUS, EVAL_THREADS, [LEAN_TC], [LEAN4EXPORT_BIN])
# Base = the c1 pipeline, made full-RH safe:
#  * prepare = prep.py: copies ONLY PRISTINE/src (+ lakefile.toml/lake-manifest.json/lean-toolchain), never PRISTINE/.lake
#    (the rh-full pristine contains the reference build); ktc_guard on the pristine text; deny line at EOF (the
#    leak-free line, generality guard = only modules whose imports reach Mathlib/Lean.LibrarySuggestions; Statements/Main
#    protected); deps.json for the scheduler.
#  * build = sched_r.py (c1 scheduler, inside bwrap): ORIGINAL module structure, reference lakefile args, no -i/-c, EARLY_RELEASE,
#    EARLY_KILL, LEAN_EXTRA = -Ddebug.skipKernelTC=true (not for ktc_guard modules) -Dlinter.all=false;
#    RETRY_PRISTINE: a failing module is restored to its exact pristine text and rebuilt once with the reference args only.
#  * packages bound read-only (trusted Mathlib cache) + one symlink LEAN_PATH dir (bind mode).
#  * export: $LEAN4EXPORT_BIN (if given; byte-identical native exporter) else the official lean4export v4.33.0; if the native
#    exporter fails (rc != 0 / no output) the official exporter is run (export.sh).
#  * checkers: ONE comparator config (Lean kernel + nanoda), nanoda_threads from checkers.json.
# Knobs (files next to this script): jobs.txt (default EVAL_THREADS-8), sched_extra.json, deny.txt (eof|off).
# No project data is shipped; everything is computed from PRISTINE inside the run.
set -euo pipefail
PRISTINE=$(readlink -f "$1"); W=$(readlink -f "$2"); D=$(cd "$(dirname "$0")" && pwd); R=$LIGHT_LEAN; E=$R/env
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
PKGSRC=$R/verify/challenge/.lake/packages
NT=${EVAL_THREADS:-160}
T0=$(date +%s.%N)
ts() { echo "[$(date -u +%FT%TZ)] +$(echo "$(date +%s.%N) - $T0" | bc | cut -c1-7)s $*"; }
JOBS=$(( NT > 16 ? NT - 8 : NT )); [ -f "$D/jobs.txt" ] && JOBS=$(cat "$D/jobs.txt")
PJ=$(( NT < 64 ? NT : 64 ))
mkdir -p "$W/proj/.lake" "$W/log/bin"
ts "start jobs=$JOBS nproc=$(nproc) LEAN_TC=${LEAN_TC:-official} LEAN4EXPORT_BIN=${LEAN4EXPORT_BIN:-official}"

# toolchain for the BUILD: official wrapped (rusage logging) or the harness-built LEAN_TC (stage1 root)
if [ -n "${LEAN_TC:-}" ]; then
  TCW=$W/tcw; mkdir -p "$TCW"; ln -sfn "$LEAN_TC/bin" "$TCW/bin"; ln -sfn "$LEAN_TC/lib" "$TCW/lib"; TCLIB=$LEAN_TC/lib/lean
else
  TCW=$E/tc-v4.33.1-wrapped; TCLIB=$T33/lib/lean
fi

# packages: bound read-only, LEAN_PATH gets ONE dir of symlinks to the top-level entries of every package lib dir
export SBX_RO=$PKGSRC
for f in lakefile.toml lake-manifest.json lean-toolchain; do [ -e "$PRISTINE/$f" ] && cp -a "$PRISTINE/$f" "$W/proj/"; done
mkdir -p "$W/proj/src" "$W/proj/.lake/pkglib"
symlink_pkglib() {
  rm -rf "$W/proj/.lake/pkglib"; mkdir -p "$W/proj/.lake/pkglib"
  ( set -e; for p in "$PKGSRC"/*/.lake/build/lib/lean; do for e in "$p"/*; do
      t="$W/proj/.lake/pkglib/$(basename "$e")"; [ -e "$t" ] && { echo "collision $t"; exit 1; }; ln -s "$e" "$t"; done; done ) \
    || { echo "symlink pkglib failed"; exit 1; }
}
PKGMODE=$(cat "$D/pkgmode.txt" 2>/dev/null || echo local); CPIDS=
if [ "$PKGMODE" = local ]; then
  # NUMA: REAL copies of the trusted package oleans and of the build toolchain's lib/lean, made under the slot's
  # numactl --membind => node-local page cache for every lean (the reference copies packages into its proj too). Same bytes,
  # same LEAN_PATH dir name => oleans/export unchanged. In the background during prep.py; on any failure -> symlink mode.
  for p in "$PKGSRC"/*/.lake/build/lib/lean; do ls -A "$p"; done | sort | uniq -d > "$W/log/pkg_collisions.txt"
  [ -s "$W/log/pkg_collisions.txt" ] && { echo "pkglib collision: $(head -3 "$W/log/pkg_collisions.txt")"; exit 1; }
  ( for p in "$PKGSRC"/*/.lake/build/lib/lean; do for e in "$p"/*; do printf '%s\0' "$e"; done; done \
      | xargs -0 -P 16 -I{} cp -a {} "$W/proj/.lake/pkglib/" ) > "$W/log/pkgcopy.log" 2>&1 & CPIDS="$!"
  mkdir -p "$W/proj/.lake/tclib"; cp -a "$TCLIB/." "$W/proj/.lake/tclib/" > "$W/log/tccopy.log" 2>&1 & CPIDS="$CPIDS $!"
else
  symlink_pkglib
fi
PKGLIB="$W/proj/.lake/pkglib"
# native package code (native.txt on|off, default on): the package-cache .c compiled with the official leanc into one lib in
# the background (native.sh: bwrap, -O1, --no-undefined, all-or-nothing, with LEAN_TC every undefined symbol must exist in
# LEAN_TC's libs and the lib must load in LEAN_TC's lean), used (--load-dynlib) by every lean started after it is ready.
# T0028 7586a50cec + natives = 48/48 oleans identical, -5% CPU.
NATIVE_MODE=$(cat "$D/native.txt" 2>/dev/null || echo on); NPID=
if [ "$NATIVE_MODE" = on ]; then bash "$D/native.sh" "$PKGSRC" "$W/log/native" "$NT" "$W/log/native.ready" "${LEAN_TC:-}" > "$W/log/native.log" 2>&1 & NPID=$!; fi
DENY=$(cat "$D/deny.txt" 2>/dev/null || echo eof)
python3 -I "$D/prep.py" "$PRISTINE/src" "$W/proj/src" "$W/log" "$PJ" $([ "$DENY" = eof ] || echo --no-deny)
LOCALTC=
if [ "$PKGMODE" = local ]; then
  okc=1; for p in $CPIDS; do wait "$p" || okc=0; done
  if [ $okc = 1 ]; then LOCALTC=$W/proj/.lake/tclib; else echo "local package/toolchain copy FAILED -> symlink mode"; tail -3 "$W/log/pkgcopy.log" "$W/log/tccopy.log"; rm -rf "$W/proj/.lake/tclib"; symlink_pkglib; PKGMODE=symlink-fallback; fi
fi
# with LEAN_TC the official 4.33.1 toolchain is also bound (read-only) for the RETRY_OFFICIAL fallback
[ -n "${LEAN_TC:-}" ] && export SBX_RO2=$T33
export T33
ts "prepared (pkgmode=$PKGMODE native=$NATIVE_MODE)"

cp "$D/sched_r.py" "$W/log/bin/"
python3 -I - "$W" "$D" "$PKGLIB" "$NATIVE_MODE" "$LOCALTC" <<'PY'
import json, os, sys
W, D, PKGLIB, NM, LOCALTC = sys.argv[1:6]
cfg = {"NO_ILEAN": "1", "NO_C": "1", "EARLY_RELEASE": "1", "EARLY_KILL": "1", "KTC_GUARD": f"{W}/log/ktc_guard.txt",
       "PKG_LIB": PKGLIB, "DEPS_JSON": f"{W}/log/deps.json", "DENY_SIZES": f"{W}/log/deny_sizes.json", "RETRY_PRISTINE": "1",
       "LEAN_EXTRA": "-Ddebug.skipKernelTC=true -Dlinter.all=false"}
if LOCALTC: cfg["LEAN_PATH_PRE"] = LOCALTC   # node-local Init/Lean/Std copy first on LEAN_PATH (same bytes)
if os.environ.get("LEAN_TC"): cfg["OFFICIAL_LEAN"] = os.environ["T33"] + "/bin/lean"   # RETRY_OFFICIAL fallback
if NM == "on": cfg["NATIVE_READY"] = f"{W}/log/native.ready"
x = os.path.join(D, "sched_extra.json")
if os.path.exists(x): cfg.update(json.load(open(x)))
json.dump(cfg, open(f"{W}/log/sched_config.json", "w"), indent=1); print(json.dumps(cfg))
PY
ts build
set +e
"$D/sbx.sh" "$W/proj" "$W/log" "$TCW" -- /usr/bin/python3 -I "$W/log/bin/sched_r.py" "$W/proj" "$W/log" "$JOBS" 100 "$TCW/bin/lean" > "$W/log/sched.stdout" 2>&1
set -e
grep -E '^(START|SUMMARY|EXIT)|NOTE|RETRY' "$W/log/sched.log" | cut -c1-600 || true
if ! grep -q '^EXIT 0' "$W/log/sched.log"; then
  ts "BUILD FAILED"; tail -5 "$W/log/sched.log"; tail -20 "$W/log/sched.stdout"
  python3 -I -c 'import json,sys
for l in open(sys.argv[1]):
    r=json.loads(l)
    if r["rc"]!=0: print("=== FAILED", r["module"]); print(r.get("output_head","")[:1500])' "$W/log/modules.jsonl" | head -100
  exit 1
fi
ts export
python3 -I "$D/buildsum.py" "$W/log" > "$W/log/buildsum.txt" 2>&1 &   # build summary, overlapped with the export
BSP=$!
# export always reads the official 4.33.1 core library (Init/Lean/Std) like the reference export
LP="$PKGLIB:$W/proj/.lake/build/lib/lean:$T33/lib/lean"
bash "$D/export.sh" "$W" "$LP" "$E/tools/lean4export/.lake/build/bin/lean4export" "$R/verify/challenge/export-targets.txt"
ts "export done: $(stat -c %s "$W/solution.export") bytes"
wait $BSP || true; cat "$W/log/buildsum.txt"
if [ -n "$NPID" ]; then wait $NPID || true; fi; cat "$W/log/native.log" 2>/dev/null; grep -c '"native": true' "$W/log/modules.jsonl" | sed 's/^/native modules: /' || true
ts done
