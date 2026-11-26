#!/bin/bash
# exportenv.sh PROJLIB OUT MODULE [TARGETS...] : official lean4export (v4.33) of MODULE's environment (all constants if no
# TARGETS) from an (untrusted) build tree PROJLIB (= .../work/proj/.lake/build/lib/lean), deps from the trusted workspace;
# run in bwrap without network, home hidden, everything read-only except OUT's directory.
set -u
PL=$1; OUT=$2; M=$3; shift 3
WS=$LIGHT_LEAN/verify/challenge/.lake/packages
T33=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
LP=""; for p in Cli batteries Qq aesop proofwidgets importGraph LeanSearchClient plausible; do LP="$LP$WS/$p/.lake/build/lib/lean:"; done
LP="$LP$PL:$T33/lib/lean"
OD=$(dirname "$(realpath -m "$OUT")"); mkdir -p "$OD"
bwrap --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc --bind "$OD" "$OD" --ro-bind "$PL" "$PL" \
  --ro-bind $WS $WS --ro-bind $T33 $T33 --ro-bind $EXP $EXP --clearenv --setenv PATH $T33/bin:/usr/bin:/bin \
  --setenv LEAN_PATH "$LP" --setenv LEAN_ABORT_ON_PANIC 1 --unshare-all --die-with-parent --new-session --chdir /tmp \
  -- $EXP "$M" ${1:+--} "$@" > "$OUT"
