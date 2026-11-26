#!/bin/bash
# tests/notary-repro/run.sh [WORKDIR] - regression test of notary reproducibility and deployment pins:
#  (1) the pinned ccmp-notary rebuilds byte-identically from check/notary/src-ccmp-388abf3d and pleanchecker-notary from
#      check/notary/src (official Lean 4.36 toolchain, offline, bwrap without network; skipped without the toolchain/bwrap);
#  (2) every notary binary PIN names the node-local install prefix /scratch/fastverify-next/notary/ (never the package tree,
#      never a path the deployment does not create), and tools/deploy.sh verifies those pins and runs check-notary.sh
#      --preflight on the target host;
#  (3) optional (F3_GRUSZKA_BUNDLE=DIR with docker + the offline Rust bundle): tools/reproduce/portable-gruszka.sh rebuilds
#      gruszka-r7 (notary) and the sound judges' gruszka byte-identically.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); N=$FV/check/notary
W=${1:-$(mktemp -d /tmp/notary-repro-test.XXXXXX)}; mkdir -p "$W"; P=0; F=0
ok() { if [ "$2" = 0 ]; then echo "PASS $1"; P=$((P+1)); else echo "FAIL $1 ${3:-}"; F=$((F+1)); fi; }
pin() { awk -v n="$2" '$1=="PIN" && $2==n {print $'"${3:-3}"'}' "$1"; }
TC36=${TC36:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
if [ -x "$TC36/bin/lake" ] && command -v bwrap > /dev/null; then
  for spec in "src-ccmp-388abf3d:ccmp-notary:ccmp_notary" "src:pleanchecker-notary:pleanchecker_notary"; do
    IFS=: read -r d t p <<< "$spec"; B=$W/$d; rm -rf "$B"; mkdir -p "$B"
    (cd "$N/$d" && tar --exclude=.lake -cf - .) | tar -xf - -C "$B"
    env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind /usr /usr --symlink usr/bin /bin \
      --symlink usr/lib /lib --symlink usr/lib64 /lib64 --proc /proc --dev /dev --tmpfs /tmp --tmpfs /home \
      --ro-bind "$TC36" "$TC36" --bind "$B" "$B" --chdir "$B" --setenv PATH "$TC36/bin:/usr/bin:/bin" --setenv HOME /tmp \
      --setenv LANG C.UTF-8 /bin/bash -c "lake build $t" > "$W/$t.build.log" 2>&1
    got=$(sha256sum "$B/.lake/build/bin/$t" 2>/dev/null | cut -d' ' -f1); want=$(pin "$N/pins.env" "$p")
    [ "$got" = "$want" ]; ok "rebuild $t from check/notary/$d = pin ${want:0:8}" $? "(got ${got:-none})"
  done
else echo "SKIP rebuild (no official 4.36 toolchain at $TC36 or no bwrap)"; fi
for p in ccmp_notary pleanchecker_notary gruszka_r7; do
  case "$(pin "$N/pins.env" "$p" 4)" in /scratch/fastverify-next/notary/*) r=0;; *) r=1;; esac; ok "PIN $p under /scratch/fastverify-next/notary/" $r
done
grep -q "check/notary/pins.env" "$FV/tools/deploy.sh" && grep -q "check-notary.sh' --preflight" "$FV/tools/deploy.sh"; ok "tools/deploy.sh verifies the notary pins + preflight on the host" $?
if [ -n "${F3_GRUSZKA_BUNDLE:-}" ]; then
  GS=${F3_GRUSZKA_SRC:-$FV/../publish/Light-Prover/sources/gruszka}
  for v in notary default; do
    "$FV/tools/reproduce/portable-gruszka.sh" $v "$GS" "$W/gz-$v" "$F3_GRUSZKA_BUNDLE" > "$W/gz-$v.log" 2>&1
    got=$(cut -c1-64 "$W/gz-$v/bin/SHA256SUMS" 2>/dev/null)
    want=$([ $v = notary ] && pin "$N/pins.env" gruszka_r7 || pin "$FV/check/sound/pins.env" gruszka)
    [ "$got" = "$want" ]; ok "portable-gruszka.sh $v = pin ${want:0:8}" $? "(got ${got:-none})"
  done
else echo "SKIP gruszka rebuild (set F3_GRUSZKA_BUNDLE=DIR: docker + offline Rust 1.97.1 bundle)"; fi
echo "notary-repro: $P passed, $F failed"; [ -n "${1:-}" ] || rm -rf "$W"; [ $F = 0 ]
