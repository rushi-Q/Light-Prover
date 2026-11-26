#!/bin/bash
# fix validation for 062: the deployed pipeline with retries disabled via its own knob file sched_extra.json
# ({"RETRY_PRISTINE": "0", "OFFICIAL_LEAN": ""}; natives off), (1) with the deny line ON (deployed default deny.txt=eof) and
# (2) with deny.txt=off. Cases: proj-second (must be REJECTED like official), an honest control (ACCEPTED), proj-meta (valid
# module-system project whose Lean access is meta-import only: official ACCEPTS; the R4 deny line cannot elaborate there,
# and RETRY_PRISTINE is what rescues it in the deployed pipeline - see tests/pkg/user_attr).
# proj-lint (valid project with an ordinary #guard_msgs test that EXPECTS an unused-variable linter warning: official ACCEPTS;
# -Dlinter.all=false (R5, in LEAN_EXTRA) suppresses the warning, RETRY_PRISTINE rescues it today).
# Configurations: A = retries off; B = retries off + deny.txt=off; C = retries off + deny off + LEAN_EXTRA '' (no transforms).
# Any x86-64 host (+FAST_TC=7586 where that build exists).
D=$(cd "$(dirname "$0")" && pwd); W=${1:-${TMPDIR:-/tmp}/$USER-fixval-062}; R=$LIGHT_LEAN
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; CE=$W/challenge/challenge.export
mkdir -p "$W/control/src"; cp "$D/proj-second/lakefile.toml" "$D/proj-second/lean-toolchain" "$W/control/"
grep -v '^run_cmd\|^  ' "$D/proj-second/src/Main.lean" | grep -v '^--' > "$W/control/src/Main.lean"
cp -a "$D/proj-second" "$D/proj-meta" "$D/proj-lint" "$W/"
for cfg in A:eof B:off C:off; do
  c=${cfg%%:*}; deny=${cfg#*:}
  P=$W/pipeline-$c; cp -a $R/fastverify/pipeline "$P"; echo off > "$P/native.txt"; echo symlink > "$P/pkgmode.txt"
  echo $deny > "$P/deny.txt"; if [ $c = C ]; then echo '{"RETRY_PRISTINE": "0", "OFFICIAL_LEAN": "", "LEAN_EXTRA": ""}' > "$P/sched_extra.json"
  else echo '{"RETRY_PRISTINE": "0", "OFFICIAL_LEAN": ""}' > "$P/sched_extra.json"; fi
  for tc in "" /scratch/fast-tc/7586; do
    [ -n "$tc" ] && [ ! -x "$tc/bin/lean" ] && continue
    for p in proj-second control proj-meta proj-lint; do
      FAST_PIPELINE_DIR=$P FAST_TC=$tc bash "$D/fastflow.sh" "$W/$p" "$W/fast-$p" "$CE" > "$W/f.log" 2>&1; frc=$?
      echo "$p (cfg $c: retries off, deny=$deny$([ $c = C ] && echo ", LEAN_EXTRA=''"), FAST_TC=${tc:-unset}): fast_rc=$frc $(grep -E '^FAST:' $W/f.log) $(grep -c RETRY $W/f.log) RETRY lines"
    done
  done
done
echo "official (for reference): proj-second REJECTED (rc 1), control ACCEPTED (0), proj-meta ACCEPTED (0), proj-lint ACCEPTED (0)"
rm -rf "$W"
