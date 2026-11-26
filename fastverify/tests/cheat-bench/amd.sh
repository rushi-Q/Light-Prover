#!/bin/bash
# amd.sh [PRESETS] : the cheat benchmark on an AMD host with the DEPLOYED package (zygote + PGO toolchains usable there).
# Usage: bash amd.sh in a copy of this directory with the package under test at fv/
cd "$(dirname "$(readlink -f "$0")")"
R=${FV_SCRATCH:-${TMPDIR:-/tmp}}/cheat-amd-$(date -u +%Y%m%dT%H%M%S)
FV_UNDER_TEST=$PWD/fv EXCLUDE='^F(24|32)-' ./run.sh "$R" 12 16 "${1:-sound reference}"
env -i HOME=$HOME PATH=/usr/bin:/bin $PWD/fv/bin/fastverify x y z --preset sound --preflight-only 2>&1 | tail -3
echo "=== RUNDIR $R"; echo "=== SUMMARY"; cat "$R/summary.md"; echo "=== TSV"; cat "$R/summary.tsv"
echo "=== TOOLCHAINS (sound runs)"; for f in "$R"/runs/*.sound/result.json; do python3 -I -c 'import json,sys; r=json.load(open(sys.argv[1])); m=r.get("mode",{}); print(sys.argv[1].split("/")[-2], [u for u in m.get("unsafe",[]) if "toolchain" in u or "zygote" in u], r.get("warnings"))' "$f"; done
echo "=== PROBES"; grep -rah "PROBE\|SWAP" "$R"/runs/F2[789]-*.sound/log 2>/dev/null | head -60
