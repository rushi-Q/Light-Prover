#!/bin/bash
# threekernel437.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON OUTDIR [THREADS] [PKG]  - for the PR #348 / community-RH
# three-kernel record: (A) the plain 4.37 trusted check (official 4.37 kernel + gruszka, ccmp-437
# statements/axioms vs the pinned official 4.37 challenge); (B) the same with con-leche --verified as a KEPT extra leg
# (--keep-config-kernels; ACCEPTED only if all three accept; a con-leche decline = no verdict); (C) con-leche --verified and
# --trusted and con-ron --verified standalone on the export (exit code, wall, peak RSS) with the binaries' sha256 and versions.
# Env: CS= (wiring script), PINS437= (pins file), HIDE= (hide list for the encapsulated replay). Everything is recorded in OUTDIR/threekernel.tsv + the JSON results; nothing is interpreted beyond exit codes.
set -u
LIGHT_LEAN=${LIGHT_LEAN:-$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)}   # repository root unless set
E=$1; C=$2; CFG=$3; O=$4; T=${5:-$(nproc)}; PKG=${6:-$LIGHT_LEAN/fastverify}
CS=${CS:-$PKG/check/sound/check-sound.sh}; P37=${PINS437:-$PKG/check/sound/pins-437.env}; HIDEARG=(); [ -n "${HIDE:-}" ] && HIDEARG=(--hide "$HIDE")   # CS= / PINS437= / HIDE= env overrides (encapsulated replay)
TC=$(/usr/bin/python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.37.0-rc1"]["prefix"])' "$PKG/config/components.json")
mkdir -p "$O"; TSV=$O/threekernel.tsv; echo -e "run\trc\tverdict\tseconds\tdetail" > "$TSV"
row() { echo -e "$1\t$2\t$3\t$4\t$5" | tee -a "$TSV"; }
js() { /usr/bin/python3 -I -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j.get("verdict")); print(json.dumps({k:(v.get("rc"),v.get("ms")) for k,v in (j.get("legs") or {}).items()}), "toolchain", j.get("toolchain"), (j.get("reason") or "")[:100])' "$1" 2>/dev/null; }
echo "[3k] versions: $(sha256sum $TC/bin/con-leche | cut -c1-16) con-leche, $(sha256sum $TC/bin/con-ron | cut -c1-16) con-ron, $(sha256sum $TC/bin/leanchecker | cut -c1-16) leanchecker ($($TC/bin/lean --version))" | tee "$O/versions.txt"
# (A) plain two-kernel 4.37 check
t0=$(date +%s); "$CS" "$E" "$C" "$CFG" --threads "$T" --json "$O/A.json" --log "$O/A.log" --private-inputs --pins "$P37" "${HIDEARG[@]}" > "$O/A.out" 2>&1; rc=$?
row A-plain-437 $rc "$(js "$O/A.json" | head -1)" $(( $(date +%s) - t0 )) "$(js "$O/A.json" | tail -1)"
# (B) three kernels: con-leche --verified kept as an extra leg
/usr/bin/python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); c.pop("enable_nanoda",None); c.pop("enable_nanoda?",None)
c["external_kernels"]={"con-leche --verified (extra)":["con-leche","--verified","--jobs=%s" % sys.argv[3]]}; json.dump(c,open(sys.argv[2],"w"),indent=1)' "$CFG" "$O/comparator-conleche.json" "$T"
t0=$(date +%s); "$CS" "$E" "$C" "$O/comparator-conleche.json" --threads "$T" --json "$O/B.json" --log "$O/B.log" --private-inputs --pins "$P37" "${HIDEARG[@]}" --keep-config-kernels > "$O/B.out" 2>&1; rc=$?
row B-three-kernel-conleche-kept $rc "$(js "$O/B.json" | head -1)" $(( $(date +%s) - t0 )) "$(js "$O/B.json" | tail -1)"
# (C) standalone runs (sandboxed like the legs: bwrap, no network)
sb() { /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc --ro-bind "$TC" "$TC" --ro-bind "$(dirname "$E")" "$(dirname "$E")" --clearenv --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LEAN_ABORT_ON_PANIC 1 --setenv LANG C.UTF-8 -- "$@"; }
for spec in "con-leche --verified" "con-leche --trusted" "con-ron --verified"; do
  set -- $spec; n="$1-${2#--}"; t0=$(date +%s)
  sb /usr/bin/time -f "%e s %M KB" "$TC/bin/$1" "$2" "--jobs=$T" "$E" > "$O/$n.out" 2> "$O/$n.err"; rc=$?
  row "C-$n" $rc "$( [ $rc = 0 ] && echo accepted || { [ $rc = 1 ] && echo rejected || { [ $rc = 2 ] && echo declined || echo error; }; })" $(( $(date +%s) - t0 )) "$(tail -1 "$O/$n.err" | tr '\t' ' ' | cut -c1-120) | $(grep -m1 -E '^con-(leche|ron): (accepted|rejected|declined)' "$O/$n.out" "$O/$n.err" | head -1 | cut -c1-120)"
done
echo "[3k] done"; cat "$TSV"
