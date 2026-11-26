#!/bin/bash
# tests/orchestrator-verdicts/run.sh [FV_ROOT]: the orchestrator verdict paths preset.sh misses
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${1:-$(cd "$H/../.." && pwd)}
bash "$H/cs-decline.sh" "$FV"; a=$?
bash "$H/toctou.sh" "$FV"; b=$?
[ $a = 0 ] && [ $b = 0 ]
