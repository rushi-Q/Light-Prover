#!/bin/bash
# tools/ci/ci-chain.sh MODE START END [extra args]  — verify commits START..END of a fetched history, one flow per call
#   (CI benchmark driver; nothing trusted here: every verdict is the official comparator's or the trusted check's).
#   MODE   off-incr       official flow with a cached .lake: lake build (default targets) + lean4export + lake comparator
#          off-sol        the same with `lake build <solution_module>` (= what the 4.36 `lake comparator` builds)
#          snd-incr       sound mode, incremental on the previous commit's build (tools/ci/sound-incr.sh)
#          snd-clos       ... restricted to the solution module's import closure (--closure-only)
#          snd-warm / snd-clos-warm   ... + warm Lean-kernel leg fed with the previous commit's export
#          ...-svc (suffix)  the check as check-sound-svc.sh --integrity-cache R/icache (integrity checks once)
#   env    R      root: R/commits/NNN-sha (tools/ci/ci-fetch.sh), R/challenge (comparator.json + pinned challenge.export
#                 + challenge.export.sha256), R/targets.txt (export targets: theorem names + the comparator's primitives)
#          FV     package (default: this one)   WS  trusted dependency workspace   T  threads (default 48)
#          BASE   (snd-*) the cold `--preset sound --keep-work` OUT of commit START-1 (no merge)
#          INCR_TC official 4.33.1 prefix (node-local copy)   TAG  run-dir suffix   TSV  result table (one row per commit)
#          LIST   explicit commit indices instead of START..END (a jump verifies all changes since the previous index)
#   Output: R/ci/MODE[-TAG]/NNN-sha/ (per commit), TSV rows: index, commit, exit, wall seconds, summary JSON.
set -u
MODE=$1 S=$2 E=$3; shift 3
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV:-$(cd "$H/../.." && pwd)}
: "${R:?R=root}" "${WS:?WS=packages workspace}"; T=${T:-48}; CH=$R/challenge
HEX=$(cut -d' ' -f1 < "$CH/challenge.export.sha256" 2>/dev/null)
OUTD=$R/ci/$MODE${TAG:+-$TAG}; mkdir -p "$OUTD"; TSV=${TSV:-$OUTD/results.tsv}
prev=${BASE:-}
for i in ${LIST:-$(seq "$S" "$E")}; do
  c=$(ls -d "$R"/commits/$(printf %03d "$i")-* | head -1); o=$OUTD/$(basename "$c"); rm -rf "$o"
  t0=$(date +%s.%N)
  case $MODE in
    off-incr) FASTVERIFY=$FV "$FV/tools/ci/official-incr.sh" "$OUTD/state" "$c" "$CH" "$o" --targets "$R/targets.txt" --packages "$WS" "$@" > "$o.out" 2>&1 ;;
    off-sol)  FASTVERIFY=$FV "$FV/tools/ci/official-incr.sh" "$OUTD/state" "$c" "$CH" "$o" --targets "$R/targets.txt" --packages "$WS" --solution-only "$@" > "$o.out" 2>&1 ;;
    snd-*)
      [ -n "$prev" ] || { echo "ci-chain: BASE= (cold sound OUT) required for $MODE" >&2; exit 2; }
      X=(); case $MODE in *clos*) X+=(--closure-only);; esac; case $MODE in *warm*) X+=(--warm-prev);; esac
      case $MODE in *svc*) mkdir -p "$R/icache" && chmod 700 "$R/icache"; X+=(--integrity-cache "$R/icache");; esac
      FASTVERIFY=$FV "$FV/tools/ci/sound-incr.sh" "$prev" "$c" "$CH" "$o" --challenge-sha256 "$HEX" --threads "$T" \
        --packages "$WS" --export-dir /dev/shm "${X[@]}" "$@" > "$o.out" 2>&1
      rc=$?; prev=$o; (exit $rc) ;;
    *) echo "ci-chain: unknown MODE $MODE" >&2; exit 2 ;;
  esac
  rc=$?; w=$(echo "$(date +%s.%N) - $t0" | bc)
  printf '%s\t%s\t%s\t%s\t%s\n' "$i" "$(basename "$c")" "$rc" "$w" "$(tail -1 "$o.out" | tr '\t' ' ' | cut -c1-3000)" >> "$TSV"
  # disk: drop build trees + exports of commits three steps back, unless the chain still builds on them
  case $MODE in snd-*) if [ "$i" -ge 3 ]; then old=$(ls -d "$OUTD"/$(printf %03d $((i - 3)))-* 2>/dev/null | grep -v '\.out$' | head -1)
    if [ -n "$old" ] && ! readlink -f "$prev/next-base" | grep -q "^$old"; then
      for x in "$old"/a*/solution.export; do [ -L "$x" ] && rm -f "$(readlink -f "$x")"; done; rm -rf "$old"/a*/work; fi; fi;; esac
done
