#!/bin/bash
# Runs a command while holding the shared measure.lock (waits for it).
S=${GRUSZKA_WORK:-${TMPDIR:-/tmp}/gruszka-work}
LOCK=$S/measure.lock
until mkdir $LOCK 2>/dev/null; do sleep 5; done
trap 'rmdir $LOCK' EXIT
"$@"
