#!/bin/bash
# visible_workdir.sh (sourced): fv_visible_workdir NAME [EXPLICIT_DIR] sets FV_WORKDIR to a writable directory for a test's work
# directory that the package's sandboxes still show: they hide /tmp, /home, /root, /var and /run, so fixtures that the
# judge must run (staged packages, mock kernels) cannot live there. Tried in order: EXPLICIT_DIR (if given),
# <repository>/fastverify/tests/.work/NAME, ${XDG_CACHE_HOME:-$HOME/.cache}/light-prover/NAME, then
# <D>/$USER/light-prover/NAME and <D>/light-prover/NAME for an existing writable top-level directory D among /scratch,
# /data, /work, /srv, /opt, /mnt. The first candidate outside the hidden directories that can be created is used.
# Returns 1 with the reason in FV_WORKDIR_WHY when there is none (the caller SKIPs).
fv_hidden_dir() { case "$(readlink -m "$1")/" in /tmp/*|/home/*|/root/*|/var/*|/run/*) return 0 ;; esac; return 1; }
fv_visible_workdir() {
  local name=$1 explicit=${2:-} fvroot c d
  fvroot=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
  FV_WORKDIR=; FV_WORKDIR_WHY=
  if [ -n "$explicit" ]; then
    if fv_hidden_dir "$explicit"; then FV_WORKDIR_WHY="$explicit is hidden inside the sandboxes (under /tmp, /home, /root, /var or /run)"; return 1; fi
    mkdir -p "$explicit" 2>/dev/null && [ -w "$explicit" ] && { FV_WORKDIR=$explicit; return 0; }
    FV_WORKDIR_WHY="$explicit cannot be created or is not writable"; return 1
  fi
  local cands=("$fvroot/tests/.work/$name" "${XDG_CACHE_HOME:-${HOME:-/nonexistent}/.cache}/light-prover/$name")
  for d in /scratch /data /work /srv /opt /mnt; do
    [ -d "$d" ] || continue
    [ -n "${USER:-}" ] && cands+=("$d/$USER/light-prover/$name")
    cands+=("$d/light-prover/$name")
  done
  for c in "${cands[@]}"; do
    fv_hidden_dir "$c" && continue
    mkdir -p "$c" 2>/dev/null && [ -w "$c" ] && { FV_WORKDIR=$c; return 0; }
  done
  FV_WORKDIR_WHY="no writable directory outside /tmp, /home, /root, /var and /run (tried ${cands[*]}); set the work directory explicitly"
  return 1
}
