#!/bin/bash
# official-export.sh DIR OUT [ELAN_LOCAL WS_LOCAL EXPORTER]
#   The OFFICIAL lean4export (v4.33.0 tag, the package's pinned E0 binary) on a build tree shipped from another node:
#   DIR = lib/ (the project's .olean files, copied from the build host) + lean_path.txt +
#   export-targets.txt + result.json of the run that built them (fast-exact = official lean per module, Lake's plan).
#   LEAN_PATH = the run's lean_path.txt with the project's lib dir mapped to DIR/lib and the trusted workspace / toolchain
#   mapped to node-local copies (same files: bench/shapes/mklocal.sh). Runs in bwrap (read-only /, no network,
#   LEAN_ABORT_ON_PANIC=1 as in the 4.36 lake comparator), stdout to OUT; prints wall time, sha256, size and whether the
#   sha256 equals the run's E1 export (result.json export.sha256) = byte identity of E1 with the official exporter.
set -u
D=$(readlink -f "$1"); OUT=$2
EL=${3:-/scratch/$USER/local/elan}; WSL=${4:-/scratch/$USER/local/ws}
EXP=${5:-/scratch/$USER/local/ll/env/tools/lean4export/.lake/build/bin/lean4export}
H=$HOME
TC=$EL/toolchains/leanprover--lean4---v4.33.1
LP=$(python3 -I - "$D" "$EL" "$WSL" <<'PY'
import sys, re
d, el, wsl = sys.argv[1:]
out = []
for p in open(d + "/lean_path.txt").read().strip().split(":"):
    if "/work/proj/.lake/build/lib/lean" in p and "/packages/" not in p:
        p = d + "/lib"
    p = re.sub(r"^/home/[^/]+/light_lean/verify/challenge", wsl, p)
    p = re.sub(r"^/home/[^/]+/\.elan", el, p)
    out.append(p)
print(":".join(out))
PY
)
mapfile -t TGT < "$D/export-targets.txt"
MOD=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["inputs"].get("solution_module") or "Solution")' "$D/result.json" 2>/dev/null)
[ -n "$MOD" ] || MOD=Solution
WANT=$(python3 -I -c 'import json,sys; print((json.load(open(sys.argv[1])).get("export") or {}).get("sha256"))' "$D/result.json")
echo "LEAN_PATH entries: $(echo "$LP" | tr ':' '\n' | wc -l); module $MOD; ${#TGT[@]} targets; E1 sha256 $WANT"
t0=$(date +%s.%N)
env -i /usr/bin/bwrap --ro-bind / / --tmpfs /home --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc --unshare-all \
  --die-with-parent --bind "$(dirname "$(readlink -f "$OUT")")" "$(dirname "$(readlink -f "$OUT")")" \
  --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LEAN_PATH "$LP" --setenv LEAN_ABORT_ON_PANIC 1 \
  -- "$EXP" "$MOD" -- "${TGT[@]}" > "$OUT" 2> "$OUT.stderr"
rc=$?; t1=$(date +%s.%N)
sha=$(sha256sum "$OUT" | cut -d' ' -f1)
echo "official lean4export rc=$rc wall=$(echo "$t1 - $t0" | bc) s size=$(stat -c %s "$OUT") sha256=$sha identical_to_E1=$([ "$sha" = "$WANT" ] && echo yes || echo NO)"
