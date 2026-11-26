#!/bin/bash
# tools/ci/official-incr.sh STATE NEW_SOURCES CHALLENGE OUT --targets FILE [--packages WS] [--fv FASTVERIFY] [--no-check]
#                           [--solution-only]
#
# BASELINE of the CI benchmark: the OFFICIAL per-commit flow of a CI job that keeps Lake's build directory between
# commits (the usual "cache .lake" CI setup): the new commit's sources are synced into the persistent project STATE/proj
# (everything outside .lake replaced, deleted files removed; .lake/build kept), then the unmodified release `lake build`
# (default targets; Lake's own traces decide what is rebuilt) runs in exactly build/official-build.sh's sandbox (bwrap,
# no network, read-only /, dependency packages read-only from WS), then the official lean4export (pinned, sandboxed,
# LEAN_ABORT_ON_PANIC=1) exports the challenge targets, then the unmodified Lean 4.36 `lake comparator` judges
# (check/official/check.sh). A first call with an empty STATE is a cold official build.
# Nothing here is trusted or new: it only strings the official tools together the way a CI job would, to measure them.
# Output: OUT/summary.json {build_s, export_s, check_s, total_s, verdict, lake_built, lake_jobs, ...}; exit 0/1/2 like
# the comparator (a failed lake build = REJECTED, as in the official flow).
set -u
STATE=$1 NEW=$(readlink -f "$2") CH=$(readlink -f "$3") OUT=$4; shift 4
FV=${FASTVERIFY:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}; WS=; TG=; NOCHECK=0; SOLONLY=0
while [ $# -gt 0 ]; do case "$1" in
  --targets) TG=$(readlink -f "$2"); shift 2 ;; --packages) WS=$2; shift 2 ;; --fv) FV=$2; shift 2 ;;
  --no-check) NOCHECK=1; shift ;; --solution-only) SOLONLY=1; shift ;; *) echo "official-incr: unknown argument $1" >&2; exit 2 ;; esac; done
[ -n "$TG" ] || { echo "official-incr: --targets FILE (export targets, one per line) required" >&2; exit 2; }
WS=${WS:-$CH}
cfg() { python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); t=c["lean_toolchains"][sys.argv[2]]; print(t["prefix"] if sys.argv[3]=="tc" else t["official_lean4export"]["path"])' "$FV/config/components.json" "$@"; }
TCN=$(tr -d ' \n' < "$NEW/lean-toolchain"); TC=$(cfg "$TCN" tc) || exit 2; EXP=$(cfg "$TCN" exp) || exit 2
mkdir -p "$STATE/proj" "$OUT"; STATE=$(readlink -f "$STATE"); OUT=$(readlink -f "$OUT"); P=$STATE/proj
SOLMOD=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$CH/comparator.json")
sandbox() { local args=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home
  --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind "$TC" "$TC" --ro-bind "$EXP" "$EXP" --bind "$P" "$P")
  while IFS=$'\t' read -r src dst; do [ -n "$src" ] || continue; mkdir -p "$dst"; args+=(--ro-bind "$src" "$dst"); done < "$OUT/binds.tsv"
  args+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8)
  while [ "${1:-}" = --env ]; do args+=(--setenv "$2" "$3"); shift 3; done
  env -i /usr/bin/bwrap "${args[@]}" --unshare-all --die-with-parent --new-session --chdir "$P" -- "$@"; }
t0=$(date +%s.%N)
rsync -a --delete --checksum --exclude=/.lake "$NEW/" "$P/" || exit 2
python3 -I "$FV/lib/manifest.py" "$P" "$WS" > "$OUT/binds.tsv" 2> "$OUT/manifest.err" || { echo "official-incr: manifest" >&2; exit 2; }
t1=$(date +%s.%N)
if [ $SOLONLY = 1 ]; then sandbox --env LEAN_ABORT_ON_PANIC 1 "$TC/bin/lake" build "$SOLMOD" > "$OUT/build.log" 2>&1; brc=$?
else sandbox "$TC/bin/lake" build > "$OUT/build.log" 2>&1; brc=$?; fi
t2=$(date +%s.%N)
erc=-1; crc=-1; t3=$t2; t4=$t2
if [ $brc = 0 ]; then
  LP=$(sandbox "$TC/bin/lake" env printenv LEAN_PATH 2>> "$OUT/build.log" | tr -d '\n')
  mapfile -t TGA < "$TG"
  t3a=$(date +%s.%N)
  sandbox --env LEAN_PATH "$LP" --env LEAN_ABORT_ON_PANIC 1 "$EXP" "$SOLMOD" -- "${TGA[@]}" > "$OUT/solution.export" 2> "$OUT/export.err"; erc=$?
  t3=$(date +%s.%N)
  if [ $erc = 0 ] && [ $NOCHECK = 0 ]; then
    "$FV/check/official/check.sh" "$OUT/solution.export" "$CH/challenge.export" "$CH/comparator.json" --json "$OUT/check.json" > "$OUT/check.out" 2>&1; crc=$?
  fi
  t4=$(date +%s.%N)
fi
SOLONLY=$SOLONLY python3 -I - "$OUT" "$t0" "$t1" "$t2" "${t3a:-$t2}" "$t3" "$t4" "$brc" "$erc" "$crc" <<'PY'
import json, os, re, sys
out = sys.argv[1]; t0, t1, t2, t3a, t3, t4 = map(float, sys.argv[2:8]); brc, erc, crc = map(int, sys.argv[8:11])
log = open(os.path.join(out, "build.log"), errors="replace").read()
built = len(re.findall(r"(?m)^. \[\d+/\d+\] Built ", log)); jobs = re.findall(r"(?m)^. \[\d+/(\d+)\]", log)
if brc != 0: v, rc = "REJECTED", 1
elif erc != 0: v, rc = ("REJECTED", 1) if erc == 1 else ("ERROR", 2)
elif crc in (0, 1): v, rc = ("ACCEPTED", "REJECTED")[crc], crc
elif crc == -1: v, rc = "NOT_CHECKED", 2
else: v, rc = "ERROR", 2
r = {"flow": "official-incremental" + ("-solution-only" if os.environ.get("SOLONLY") == "1" else ""), "verdict": v, "sync_s": round(t1 - t0, 2), "build_s": round(t2 - t1, 2),
     "leanpath_s": round(t3a - t2, 2), "export_s": round(t3 - t3a, 2), "check_s": round(t4 - t3, 2),
     "total_s": round(t4 - t0, 2), "build_exit": brc, "export_exit": erc, "check_exit": crc, "lake_built": built,
     "lake_jobs": int(jobs[-1]) if jobs else 0}
try: r["export_bytes"] = os.path.getsize(os.path.join(out, "solution.export"))
except OSError: pass
json.dump(r, open(os.path.join(out, "summary.json"), "w"), indent=1); print(json.dumps(r)); sys.exit(rc)
PY
