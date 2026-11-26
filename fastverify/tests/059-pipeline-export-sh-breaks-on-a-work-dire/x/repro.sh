#!/bin/bash
# Repro (~30 s): the same valid trivial project, both flows run in a work directory whose path contains a
# space. Official flow (lake build + lean4export + lake comparator): ACCEPTED. Fast flow (fastverify/pipeline/pipeline.sh +
# pchk): build EXIT 0, then export.sh fails ('cd: too many arguments') -> pipeline rc=1 -> REJECTED.
D=$(cd "$(dirname "$0")" && pwd); W="${1:-${TMPDIR:-/tmp}/$USER-repro-059}/sp ace"   # always a path with a space
rm -rf "$W"; mkdir -p "$W"; cp -a "$D/challenge" "$W/challenge"; cp -a "$D/proj" "$W/proj"
echo "=== OFFICIAL flow (work dir: '$W')"; bash "$D/officialflow.sh" "$W/proj" "$W/official" "$W/challenge"; orc=$?
echo "=== FAST flow"; bash "$D/fastflow.sh" "$W/proj" "$W/fast" "$W/challenge/challenge.export"; frc=$?
grep -m1 "too many arguments" "$W/fast/pipeline.log"
echo "=== SUMMARY official_rc=$orc fast_rc=$frc  (0 = ACCEPTED)"
