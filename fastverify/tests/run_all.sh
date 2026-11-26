#!/bin/bash
# run_all.sh [options] [IDS...]   -- run the fastverify regression suite (one test per numbered finding + generality
#                                     tests + stage component tests + RH-subset tests)
#   --heavy           also run the tests tagged '# heavy' (Mathlib-sized inputs, minutes each)
#   --only-heavy      only the heavy tests
#   --jobs J          tests in parallel (default 4); each test uses EVAL_THREADS threads (default 8)
#   --work DIR        node-local work dir (default $FV_TEST_WORK/<stamp>-<label>; one of the two is required); logs
#                     DIR/NNN.log, rows DIR/NNN.tsv. Prefer a directory outside /tmp, /home, /var and /run (the kernel
#                     sandbox of the trusted check hides those) with tens of GB free
#   --fv BIN          entry point to test (default: a SNAPSHOT of <package>/bin/fastverify, see --no-snapshot)   (= env FV_BIN)
#   --no-snapshot     test the live package tree instead of a private snapshot copy (WORK/pkg) taken at the start
#   --standin         harness self-test: FV_BIN = lib/standin-official.sh (the OFFICIAL flow as the "fast" one: all PASS)
#   --deployed        e2e tests with the original (attacked) fast flow (fastflow.deployed.sh): shows the original divergences
#   --fv-args "ARGS"  package options under test (menu flags, e.g. "--preset reference", "--build B2 --check C3,C0",
#                     "--build B3 --unsafe skip-kernel-tc --check C3,C0"); default "--check C3,C0" (on B1+E1;
#                     formerly "--check both" = C1,C3,C0 - check A (C1) was retired, 'both' is now refused)
#   --unsafe-run      the options under test are UNSAFE opt-ins: FAIL rows are reported as UNSAFE-FAIL-* (documented breakage)
#   --label NAME      label of the results file (default: package|standin|deployed)
#   --list            list the tests and exit
# IDS = test ids (3-digit finding numbers or suite names; default: all). Results: tests/results/<UTC stamp>-<label>.tsv (+ .json with
# the run's metadata: host, options, package snapshot digest) copied from DIR/results.tsv.
# Must run on a machine with the official toolchains (Lean 4.33.1 + 4.36.0 under ~/.elan, official lean4export), e.g.
#   FV_TEST_WORK=/local/disk/fvtests fastverify/tests/run_all.sh --jobs 12
# Each row: id case official_rc fast_rc official_sha16 fast_sha16 result note (see README.md). Exit 0 iff no FAIL*/ERROR row.
# The package is snapshotted (rsync to WORK/pkg, tests/ and non-package directories excluded) so that edits to the live tree during a
# long run cannot break or change it; FV_ROOT/FV_BIN point the tests at the snapshot.
{ # whole script parsed before it runs (safe against edits while running)
set -u
T=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
HEAVY=0; ONLYH=0; J=4; WORK=""; LABEL=""; LIST=0; IDS=""; SNAP=1
while [ $# -gt 0 ]; do case $1 in
  --heavy) HEAVY=1;; --only-heavy) HEAVY=1; ONLYH=1;; --jobs) J=$2; shift;; --work) WORK=$2; shift;;
  --fv) export FV_BIN=$(readlink -f "$2"); SNAP=0; shift;; --no-snapshot) SNAP=0;;
  --standin) export FV_BIN=$T/lib/standin-official.sh; SNAP=0; LABEL=${LABEL:-standin};;
  --deployed) export FV_FAST=deployed; SNAP=0; LABEL=${LABEL:-deployed};; --label) LABEL=$2; shift;; --list) LIST=1;;
  --fv-args) export FV_ARGS="$2" FV_ARGS_EXPORT="$2"; shift;; --unsafe-run) export FV_UNSAFE_RUN=1;;
  -h|--help) sed -n 2,25p "$0"; exit 0;; *) IDS="$IDS $1";; esac; shift; done
LABEL=${LABEL:-package}; STAMP=$(date -u +%Y%m%dT%H%M%SZ)
tests=""
# the suites run here: every numbered finding test NNN-* plus the generality, stage-component and RH-subset tests below
SUITES="lake-config challenge-config odd-layouts challenge-variants smallproofs batchverify incr-reverify seam-sandbox cheat-bench-quick shapes confirm-reject exe-dep-readonly escaped-package-name other-releases multi-claims stage-checkb-wrapper stage-prechk stage-export stage-build build-artifacts-identity orchestrator-package lean436-projects checkb-definition-names build-merge build-zygote build-j1-hints build-importarts-empty retired-checka rh-minif-export"
tid() { local b; b=$(basename "$1"); case $b in [0-9][0-9][0-9]-*) echo "${b:0:3}";; *) echo "$b";; esac; }   # test id: NNN or the dir name
for d in "$T"/[0-9][0-9][0-9]-*/ $(for s in $SUITES; do echo "$T/$s/"; done); do [ -d "$d" ] || continue; d=${d%/}; id=$(tid "$d")
  [ -x "$d/test.sh" ] || continue
  if [ -n "$IDS" ]; then case " $IDS " in *" $id "*) ;; *) continue;; esac; fi
  h=0; grep -q '^# heavy' "$d/test.sh" && h=1
  [ -z "$IDS" ] && [ $h = 1 ] && [ $HEAVY = 0 ] && continue
  [ -z "$IDS" ] && [ $h = 0 ] && [ $ONLYH = 1 ] && continue
  tests="$tests $d"
done
if [ $LIST = 1 ]; then for d in $tests; do printf '%s  %s\n' "$(basename "$d")" "$(grep -m1 "^# finding:" "$d/test.sh" | cut -c12-120)"; done; exit 0; fi
[ -n "$WORK" ] || [ -n "${FV_TEST_WORK:-}" ] || { echo "run_all.sh: no work directory: pass --work DIR or set FV_TEST_WORK" >&2; exit 2; }
WORK=${WORK:-$FV_TEST_WORK/$STAMP-$LABEL}; mkdir -p "$WORK"; WORK=$(readlink -f "$WORK")
PKGD=-
if [ $SNAP = 1 ]; then
  rsync -a --exclude=/tests/ --exclude=/pipeline/ --exclude='/review-*/' --exclude=__pycache__/ "$T/../" "$WORK/pkg/"
  ln -sfn "$T" "$WORK/pkg/tests"   # test inputs (finding snapshots etc.) are read from the live tests/ dir
  export FV_ROOT=$WORK/pkg FV_BIN=$WORK/pkg/bin/fastverify
  PKGD=$(cd "$WORK/pkg" && find . -path ./tests -prune -o -type f ! -name '*.pyc' -print | LC_ALL=C sort | xargs -d '\n' sha256sum | tee "$WORK/pkg.sha256" | sha256sum | cut -c1-16)
fi
export FV_RUN_ID=$STAMP-$LABEL FV_HEAVY=$HEAVY; export EVAL_THREADS=${EVAL_THREADS:-8}
. "$T/lib/paths.sh"   # FV_T33 FV_T36 FV_OFFICIAL_EXPORTER FV_PACKAGES from the package's config/components.json
echo "fastverify regression suite: $(echo $tests | wc -w) tests, jobs=$J, EVAL_THREADS=$EVAL_THREADS, work=$WORK, label=$LABEL"
echo "official tools: FV_T33=$FV_T33 FV_T36=$FV_T36 FV_OFFICIAL_EXPORTER=$FV_OFFICIAL_EXPORTER FV_PACKAGES=$FV_PACKAGES"
echo "FV_BIN=${FV_BIN:-$T/../bin/fastverify} FV_FAST=${FV_FAST:-package} FV_ARGS='${FV_ARGS:---check C3,C0}' unsafe_run=${FV_UNSAFE_RUN:-0} snapshot=$SNAP package_digest=$PKGD host=$(hostname) start=$STAMP"
python3 -I -c 'import json,sys; json.dump(dict(zip(["stamp","label","host","fv_bin","fv_fast","snapshot","package_digest","jobs","threads","heavy","fv_args","unsafe_run","tests"], sys.argv[1:13] + [sys.argv[13].split()])), open(sys.argv[14], "w"), indent=1)' \
  "$STAMP" "$LABEL" "$(hostname)" "${FV_BIN:-$T/../bin/fastverify}" "${FV_FAST:-package}" "$SNAP" "$PKGD" "$J" "$EVAL_THREADS" "$HEAVY" \
  "${FV_ARGS:---check C3,C0}" "${FV_UNSAFE_RUN:-0}" "$(for d in $tests; do tid "$d"; done | tr '\n' ' ')" "$WORK/run.json"
t0=$(date +%s)
printf '%s\n' $tests | xargs -P "$J" -I{} bash -c 'd={}; id=$(basename "$d"); case $id in [0-9][0-9][0-9]-*) id=${id:0:3};; esac; s=$(date +%s);
  timeout ${FV_TEST_TIMEOUT:-7200} "$d/test.sh" "$0/$id" > "$0/$id.out" 2>&1; rc=$?
  [ -s "$0/$id.tsv" ] || printf "%s\t-\t-\t-\t-\t-\tERROR\ttest exit %s, no result rows (see %s.out)\n" "$id" "$rc" "$0/$id" > "$0/$id.tsv"
  echo "  done $id rc=$rc $(( $(date +%s) - s )) s: $(cut -f7 "$0/$id.tsv" | sort | uniq -c | tr -s " \n" " ")"' "$WORK"
{ printf 'id\tcase\tofficial_rc\tfast_rc\tofficial_sha16\tfast_sha16\tresult\tnote\n'
  for d in $tests; do id=$(tid "$d"); cat "$WORK/$id.tsv" 2>/dev/null; done; } > "$WORK/results.tsv"
SUMLINE=$(tail -n +2 "$WORK/results.tsv" | cut -f7 | sort | uniq -c | tr -s ' \n' ' ')
python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); r["seconds"]=int(sys.argv[2]); r["summary"]=sys.argv[3].strip(); json.dump(r, open(sys.argv[1],"w"), indent=1)' \
  "$WORK/run.json" "$(( $(date +%s) - t0 ))" "$SUMLINE"
mkdir -p "$T/results" 2>/dev/null && cp "$WORK/results.tsv" "$T/results/$STAMP-$LABEL.tsv" 2>/dev/null && cp "$WORK/run.json" "$T/results/$STAMP-$LABEL.json" 2>/dev/null
echo; column -t -s$'\t' "$WORK/results.tsv" | cut -c1-220
echo; echo "SUMMARY ($LABEL, $(( $(date +%s) - t0 )) s, package $PKGD): $SUMLINE"
echo "results: $WORK/results.tsv (copy: tests/results/$STAMP-$LABEL.tsv)"
! tail -n +2 "$WORK/results.tsv" | cut -f7 | grep -qE "^(FAIL|ERROR)"
exit $?
}
