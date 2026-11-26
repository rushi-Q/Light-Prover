#!/bin/bash
# amd_job.sh LABEL [PHASES]  — whole-node fvserve measurement. Run it (directly or through a batch scheduler) with the
# current directory holding: fv/ (the package, trimmed), fvserve/ (tools/fvserve), this script.
# Env: FV_SCRATCH (work root, required unless WORKROOT is set: results in WORKROOT/LABEL, default WORKROOT =
#   $FV_SCRATCH/fvserve-bench), FV_PACKAGES (trusted Lake workspace, required unless WSROOT is set), THREADS (default 192),
#   TCROOT / ELANH (elan toolchains dir / elan home, default ~/.elan), LLROOT (passed to tools/configure.py --light-lean
#   if set), NPROB (default 6), SMOKE=1 (a quick test of the script).
# PHASES (default "setup base bv svc"): setup = corpus + OFFICIAL BATCH challenge export + attempts (bench/setup.sh);
#   base = official per-proof flow (--preset reference, challenge pinned) + --preset sound + --preset sound --build B0
#          on N problems, one at a time on the whole node; bv = tools/batchverify.py on 1 attempt at a time;
#   svc  = fvserve: start-up cost, sequential latency (fork compile + svc check / plain check-sound), best-of-16,
#          108-attempt burst, the 1,000-attempt stream at several concurrencies.
set -u
LABEL=${1:?label}; shift; PH=${*:-setup base bv svc}
HERE=$(pwd); FV=$HERE/fv; FS=$HERE/fvserve
T=${THREADS:-192}
W=${WORKROOT:-${FV_SCRATCH:?node-local work root (required unless WORKROOT is set)}/fvserve-bench}/$LABEL; mkdir -p "$W"; R=$W/res; mkdir -p "$R"
TC=${TCROOT:-$HOME/.elan/toolchains}/leanprover--lean4---v4.33.1
WS=${WSROOT:-${FV_PACKAGES:?trusted Lake workspace with materialized dependencies (required unless WSROOT is set)}}
N=${NPROB:-6}; SM=${SMOKE:-0}; SN=""; [ "$SM" = 1 ] && { N=1; SN="--n 24"; }   # SMOKE=1: a quick test of the script
echo "== $(hostname) $(date -u +%FT%TZ) threads=$T phases: $PH"
LLA=(); [ -n "${LLROOT:-}" ] && LLA=(--light-lean "$LLROOT")
python3 -I "$FV/tools/configure.py" --elan-home "${ELANH:-$HOME/.elan}" ${LLA[@]+"${LLA[@]}"} | tail -2
B=$W/b
if [[ " $PH " == *" setup "* ]]; then
  t0=$(date +%s)
  bash "$FS/bench/setup.sh" "$B" "$FV" "$WS" 64
  echo "setup_s $(( $(date +%s) - t0 ))"
  bash "$FS/fork/build.sh" "$TC" "$W/fvfork" | tail -1
fi
SHA=$(cut -c1-64 "$B/pset/challenge.export.sha256")
PROBS=$(ls "$B/att-pos" | sed 's/\.lean$//' | awk 'NR%18==1' | head -$N)
echo "problems: $PROBS"
if [[ " $PH " == *" base "* ]]; then
  : > "$W/q.txt"
  for c in $PROBS; do echo "$c reference src" >> "$W/q.txt"; done
  for c in $PROBS; do printf '%s reference pin\n%s sound pin\n%s sound pin @b0 --build B0\n' "$c" "$c" "$c" >> "$W/q.txt"; done
  env R="$W/base" CORPUS="$B/corpus" FV_PKG="$FV" THREADS=$T WS="$WS" bash "$FV/bench/throughput/runq.sh" "$W/q.txt" 1
  python3 -I "$FV/bench/throughput/table.py" "$W/base" > "$R/base.tsv" 2>/dev/null; cp "$W/base/runs/done.tsv" "$R/base-done.tsv"
  echo "== base (tag case preset mode rc wall)"; cat "$R/base-done.tsv"
fi
if [[ " $PH " == *" bv "* ]]; then
  echo "== batchverify, one attempt at a time (snapshot reused after the first)"
  for c in $PROBS; do
    rm -rf "$W/bva" "$W/bvo"; mkdir -p "$W/bva"; cp "$B/att-pos/$c.lean" "$W/bva/"
    s=$(date +%s.%N)
    python3 -I "$FV/tools/batchverify.py" --pset "$B/pset" --attempts "$W/bva" --out "$W/bvo" --challenge-sha256 "$SHA" \
      --threads $T --packages "$WS" --toolchain "$TC" --fv "$FV" --snapshot-cache "$W/bvsnap" > /dev/null 2>&1
    e=$(date +%s.%N)
    printf 'bv\t%s\t%s\t%s\n' "$c" "$(python3 -c "print(round($e-$s,2))")" "$(python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["summary"])' "$W/bvo/batch.json")"
  done | tee "$R/bv.tsv"
fi
svc() {  # svc NAME THREADS ARGS... : start a service, wait for ready
  local st=$W/$1; local thr=$2; shift 2; rm -rf "$st"
  python3 -I "$FS/fvserve.py" serve --state "$st" --pset "batch=$B/pset:$SHA" --threads "$thr" --packages "$WS" \
    --toolchain "$TC" --fv "$FV" --warmup "batch:alg_cube_expand:$B/att-pos/alg_cube_expand.lean" "$@" > "$W/$(basename "$st").log" 2>&1 &
  for i in $(seq 1 300); do grep -q '"ready"' "$W/$(basename "$st").log" 2>/dev/null && break; sleep 1; done
  grep '"ready"' "$W/$(basename "$st").log"
}
stop() { python3 -I "$FS/fvserve.py" stop --state "$W/$1" > /dev/null 2>&1; sleep 2; }
cli() { python3 -I "$FS/fvclient.py" "$@"; }
if [[ " $PH " == *" svc "* ]]; then
  mkdir -p "$W/seqatt"; for c in $PROBS; do cp "$B/att-pos/$c.lean" "$W/seqatt/"; done
  echo "== fvserve A: fork compile + check-sound-svc (integrity cache)"
  svc sA $T --svc-check --fork-server "$W/fvfork/fvfork" --max-inflight 4
  cli seq --state "$W/sA" --pset batch "$W/seqatt" --out "$R/svcA-seq.tsv" | tail -1
  [ "$SM" = 1 ] || cli seq --state "$W/sA" --pset batch "$B/att-pos" --n 24 --out "$R/svcA-seq24.tsv" | tail -1
  # best-of-16: 16 attempts of one theorem at once (honest + not compiling + cheats from the stream generator)
  BO=$W/bestof; rm -rf "$BO"; mkdir -p "$BO"
  python3 -I - "$B/stream/labels.json" "$B/stream" "$BO" <<'PY'
import json, os, shutil, sys, collections
lab = json.load(open(sys.argv[1])); src, out = sys.argv[2], sys.argv[3]
by = collections.defaultdict(list)
for b in sorted(lab):
    for th, (kind, exp) in lab[b].items():
        by[th].append((kind, exp, os.path.join(src, b, th + ".lean")))
th, lst = max(by.items(), key=lambda kv: (len({k for k, _, _ in kv[1]}), len(kv[1])))
for i, (kind, exp, p) in enumerate(lst[:16]):
    shutil.copyfile(p, os.path.join(out, f"{i:02d}-{kind}.lean"))
open(os.path.join(out, "THEOREM"), "w").write(th)
PY
  cli bestof --state "$W/sA" --pset batch --theorem "$(cat "$BO/THEOREM")" "$BO"/*.lean --out "$R/svcA-bestof.tsv" | tail -1
  cli burst --state "$W/sA" --pset batch "$B/att-pos" $SN --conc 108 --out "$R/svcA-burst108.tsv" | tail -1
  for c in 8 32 96; do
    cli stream --state "$W/sA" --pset batch "$B/stream" $SN --conc $c --out "$R/svcA-stream-c$c.tsv" | tail -2
  done
  python3 -I "$FS/fvserve.py" stats --state "$W/sA"
  stop sA
  echo "== fvserve B: official lean compile (snapshot) + unchanged check-sound.sh"
  svc sB $T --max-inflight 4
  cli seq --state "$W/sB" --pset batch "$W/seqatt" --out "$R/svcB-seq.tsv" | tail -1
  cli stream --state "$W/sB" --pset batch "$B/stream" $SN --conc 32 --out "$R/svcB-stream-c32.tsv" | tail -2
  stop sB
  echo "== fvserve C: fork compile + unchanged check-sound.sh"
  svc sC $T --fork-server "$W/fvfork/fvfork" --max-inflight 4
  cli seq --state "$W/sC" --pset batch "$W/seqatt" --out "$R/svcC-seq.tsv" | tail -1
  stop sC
fi
echo "== results"; for f in "$R"/*.tsv; do echo "--- $f"; cat "$f"; done
echo "== done $(date -u +%FT%TZ)"
