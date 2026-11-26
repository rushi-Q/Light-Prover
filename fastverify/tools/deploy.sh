#!/bin/bash
# tools/deploy.sh HOST [SRC_NODE]
# Installs this package on HOST exactly as it is here (e.g. a large machine whose home directory is a local disk that
# does not have the package):
#   1. package: rsync to PKG.new on HOST, then directory swap (previous copy kept as PKG.prev). The live copy is never edited
#      in place (a running stage script would break: bash reads scripts incrementally). Same absolute path, so
#      config/components.json and every stage's pins stay valid.
#   2. binaries: rsync of the node-local fast binaries under their pinned install prefix /scratch/fastverify-next/ from
#      SRC_NODE (default: this host), then every SHA256SUMS file under it is verified ON HOST.
#   2b. the notary judge: every PIN of check/notary/pins.env (node-local binaries under /scratch/fastverify-next/notary/v2
#      + the self-test files) must exist on HOST with its pinned sha256, then `check/notary/check-notary.sh --preflight`
#      runs on HOST (pins + self-test + 3-leg digest); exit != 0 = deploy failed.
#   3. `bin/fastverify --preset sound --preflight-only` on HOST with the RH inputs (sha256 pins, whole official toolchain
#      trees, every stage's --preflight, host limits; exit 0 iff all usable; a run without --preset/--check
#      is refused). RH_PROJECT / RH_CHALLENGE
#      name the RH project and its challenge workspace (paths on HOST; defaults <repository root>/alpoge-rh/lean and
#      <repository root>/verify/challenge).
# The official toolchains (~/.elan/toolchains/leanprover--lean4---v4.33.1, ...-v4.36.0), the official lean4export
# (env/tools/lean4export) and the challenge workspace's .lake/packages must already be on HOST at the same paths; the
# preflight verifies them file by file / by sha256 and refuses on any difference. Nothing heavy runs on HOST.
# Re-run after ANY change of the package or of a binary, right before a large run.
set -euo pipefail
HOST=${1:?usage: deploy.sh HOST [SRC_NODE]}; SRC=${2:-$(hostname)}
PKG=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
R=$(dirname "$PKG")   # repository root
RP=${RH_PROJECT:-$R/alpoge-rh/lean}; RC=${RH_CHALLENGE:-$R/verify/challenge}
SSH=(ssh -o BatchMode=yes -o ConnectTimeout=20)
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
echo "deploy: package $PKG -> $HOST:$PKG ($STAMP, from $(hostname))"
"${SSH[@]}" "$HOST" "mkdir -p '$PKG.new'"
rsync -a --delete --exclude 'tests/results/' --exclude '__pycache__/' --exclude '*.pyc' -e "${SSH[*]}" "$PKG/" "$HOST:$PKG.new/"
"${SSH[@]}" "$HOST" "set -e; rm -rf '$PKG.prev'; if [ -d '$PKG' ]; then mv '$PKG' '$PKG.prev'; fi; mv '$PKG.new' '$PKG'; echo '$STAMP from $(hostname)' > '$PKG/DEPLOYED'"
echo "deploy: binaries $SRC:/scratch/fastverify-next/ -> $HOST:/scratch/fastverify-next/"
"${SSH[@]}" "$HOST" "mkdir -p /scratch/fastverify-next && chmod -R u+w /scratch/fastverify-next"
if [ "$SRC" = "$(hostname)" ]; then
  rsync -a --delete -e "${SSH[*]}" /scratch/fastverify-next/ "$HOST:/scratch/fastverify-next/"
else
  "${SSH[@]}" "$SRC" "rsync -a --delete -e 'ssh -o BatchMode=yes' /scratch/fastverify-next/ '$HOST:/scratch/fastverify-next/'"
fi
"${SSH[@]}" "$HOST" "cd /scratch/fastverify-next && n=0 && for s in \$(find . -name SHA256SUMS); do (cd \"\$(dirname \"\$s\")\" && sha256sum -c --quiet SHA256SUMS) || { echo \"deploy: SHA256 MISMATCH in \$s\"; exit 1; }; n=\$((n+1)); done; echo \"deploy: \$n SHA256SUMS files verified on $HOST\""
echo "deploy: notary pins + preflight on $HOST"
# the notary's pins name node-local files; a missing directory used to surface only when a notary run declined
"${SSH[@]}" "$HOST" "set -e; n=0; while read -r tag name sum path; do [ \"\$tag\" = PIN ] || continue; [ -f \"\$path\" ] || { echo \"deploy: notary pin \$name missing on $HOST: \$path\"; exit 1; }; [ \"\$(sha256sum \"\$path\" | cut -d' ' -f1)\" = \"\$sum\" ] || { echo \"deploy: notary pin \$name sha256 differs on $HOST: \$path\"; exit 1; }; n=\$((n+1)); done < '$PKG/check/notary/pins.env'; echo \"deploy: \$n notary pins verified on $HOST\""
"${SSH[@]}" "$HOST" "'$PKG/check/notary/check-notary.sh' --preflight --threads 4 | tail -n 1 | grep -q '\"verdict\":\"PREFLIGHT_OK\"'" || { echo "deploy: check-notary.sh --preflight failed on $HOST"; exit 1; }
echo "deploy: preflight on $HOST"
"${SSH[@]}" "$HOST" "rm -rf /tmp/fv-deploy-pf && '$PKG/bin/fastverify' '$RP' '$RC' /tmp/fv-deploy-pf --preset sound --preflight-only --comparator-config '$RC/comparator.nanoda.json' --comparator-sha256 \$(sha256sum '$RC/comparator.nanoda.json' | cut -c1-64); rc=\$?; rm -rf /tmp/fv-deploy-pf; exit \$rc"
echo "deploy: done ($STAMP)"
