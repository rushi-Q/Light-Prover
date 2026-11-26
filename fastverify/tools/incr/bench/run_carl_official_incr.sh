#!/bin/bash
# OFFICIAL incremental comparison on Carleson: (1) --preset reference --keep-work (official lake build + lean4export +
# lake comparator), (2) the K2 edit applied to a reflink copy of the kept tree and the OFFICIAL `lake build` re-run there in
# the same bwrap sandbox as build/official-build.sh (Lake's own traces decide what to rebuild). The official export and
# comparator are whole-project steps (their times from (1) apply unchanged to every edit).
set -u
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
P=$V/bp/projects/carleson; CHX=$V/carlchx; WS=$V/bp/ws/carleson
FV=$V/local/fv; TC=$V/local/elan/toolchains/leanprover--lean4---v4.33.1
R=$V/carlref; rm -rf $R
/usr/bin/time -f "WALL %e" $FV/bin/fastverify $P $CHX $R --preset reference --threads 96 --packages $WS --keep-work > $V/carlref.log 2>&1
echo "REF EXIT $?"; python3 -c "import json;r=json.load(open('$R/result.json'));print(r['verdict'],r['stage_seconds'])"
# (2) Lake's incremental rebuild after the K2 edit
I=$V/carlref-incr; rm -rf $I; cp -a --reflink=auto $R/work/proj $I
F=Carleson/ToMathlib/BoundedCompactSupport.lean; rm -f $I/$F; cp $V/carl-edits/K2/$F $I/$F
python3 -I $FV/lib/manifest.py $I $WS > $V/carlref-binds.tsv
args=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp --dir /tmp/home --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv --ro-bind $TC $TC --bind $I $I)
while IFS=$'\t' read -r src dst; do [ -n "$src" ] && { mkdir -p "$dst"; args+=(--ro-bind "$src" "$dst"); }; done < $V/carlref-binds.tsv
args+=(--setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8 --unshare-all --die-with-parent --new-session --chdir $I)
s=$(date +%s.%N)
env -i /usr/bin/bwrap "${args[@]}" -- $TC/bin/lake build > $V/carlref-incr.log 2>&1; rc=$?
echo "official incremental lake build: exit $rc, $(echo "$(date +%s.%N) - $s" | bc) s, rebuilt $(grep -c 'Built ' $V/carlref-incr.log) jobs: $(grep -m3 'Built Carleson' $V/carlref-incr.log | tr '\n' ' ' | cut -c1-200)"
s=$(date +%s.%N)
env -i /usr/bin/bwrap "${args[@]}" -- $TC/bin/lake build > $V/carlref-noop.log 2>&1; rc=$?
echo "official no-op lake build: exit $rc, $(echo "$(date +%s.%N) - $s" | bc) s"
