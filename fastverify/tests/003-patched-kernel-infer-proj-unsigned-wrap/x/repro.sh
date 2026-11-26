#!/bin/bash
# 003 repro: patched-kernel infer_proj fast path (k/src/kernel/type_checker.cpp:313-330, pchk d876802) computes
# `unsigned n = nparams + idx`, which wraps for idx = 2^32 - nparams. Input: structure S (α : Type) := (x : α) and
#   def bad : S Nat -> Type := fun s => .proj S 4294967295 s        (wrap.ndjson; 4294967295 = 2^32 - 1, nparams = 1)
# OFFICIAL Lean 4.36 kernel (leanchecker --from-export, = the kernel step of `lake comparator`): REJECT (invalid projection).
# FAST pleanchecker-k (pchk's Lean-kernel replay): ACCEPT (types the projection as `Type` = the type of parameter α).
# Needs ~300 GB RAM (the fast path materialises 2^32-1 `mk_proj` objects + a 32 GB substitution buffer) and ~5-15 min.
# Usage: bash repro.sh            (4 CPUs are enough)
set -u
D=$(cd "$(dirname "$0")" && pwd)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
PLCK=${PLCK:-/scratch/fastverify/checkers/pchk/.lake/build/bin/pleanchecker-k}
if ldd "$PLCK" 2>&1 | grep -q "not found"; then
  echo "NOTE: $PLCK does not run on this host (built on the AMD server against glibc 2.38);"
  PLCK=${FV_REPRO_BIN:-$LIGHT_LEAN/repro-bin}/pleanchecker-k
  echo "      using the identical-source rebuild $PLCK (pchk d876802 build_k.sh steps, see rebuild_pleanchecker_k.sh)"
fi
sbx() {  # like the krun sandbox: no network, home hidden, private /tmp; finding dir + binaries read-only
  T=$(mktemp -d /tmp/x02sbx.XXXXXX)
  env -i bwrap --unshare-all --die-with-parent --new-session \
    --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
    --ro-bind /etc/ld.so.cache /etc/ld.so.cache --proc /proc --dev /dev --tmpfs /home --bind "$T" /tmp \
    --ro-bind "$D" "$D" --ro-bind "$TC" "$TC" --ro-bind "$(dirname "$PLCK")" "$(dirname "$PLCK")" \
    --setenv HOME /tmp --setenv PATH /usr/bin:/bin --setenv LEAN_ABORT_ON_PANIC 1 --chdir /tmp "$@"
  rc=$?; rm -rf "$T"; return $rc
}
for f in ctl0 idx1 wrap; do
  echo "=== $f.ndjson: $(grep -o '"proj":{[^}]*}' "$D/$f.ndjson")"
  sbx "$TC/bin/leanchecker" --from-export "$D/$f.ndjson"; echo "OFFICIAL leanchecker (Lean 4.36 kernel): rc=$?"
  sbx /usr/bin/time -f "  [pleanchecker-k peak RSS %M KB, %e s]" "$PLCK" --from-export "$D/$f.ndjson"; echo "FAST pleanchecker-k (patched kernel):   rc=$?"
done
echo "(rc 0 = accept, 1 = reject). Divergence iff wrap.ndjson: OFFICIAL rc=1 and FAST rc=0."
