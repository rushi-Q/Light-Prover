#!/bin/bash
# tests/toolchain/regress_toolchain.sh CANDIDATE_TC_ROOT  -- the toolchain regression, package-local copy.
# Adapted from the original toolchain regression script: same 22 cases for findings 004 014 020 031 037 040 050 061
# (+ 052 info); inputs are read from the package's own snapshots tests/NNN-*/x/ instead of the original tree; the official
# Lean 4.33.1 and the official lean4export come from the package's pins (lib/toolchain.py resolve, config/components.json);
# the candidate must start natively on this host (no docker wrapper). One line per case: SAME (= official) or DIFFERENT.
main() {
set -u
FTC_ROOT=${1:?usage: regress_toolchain.sh CANDIDATE_TC_ROOT}; FTC=$FTC_ROOT/lib/lean
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=$(cd "$H/../.." && pwd); F=$FV/tests
PJ=$(mktemp -d /tmp/fv-rt-proj.XXXXXX); echo 'leanprover/lean4:v4.33.1' > $PJ/lean-toolchain
T33=$(python3 -I $FV/lib/toolchain.py resolve $PJ) || { echo "official Lean 4.33.1 not available/verified"; exit 2; }; rm -rf $PJ
EXP=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["official_lean4export"]["path"])' $FV/config/components.json)
export PATH=$T33/bin:$PATH
W=$(mktemp -d /tmp/xregress.XXXXXX); trap 'rm -rf "$W"' EXIT; mkdir -p $W/src $W/off $W/fast; export FL_BIND="$W"
if "$FTC_ROOT/bin/lean" --version > /dev/null 2>&1; then FL="$FTC_ROOT/bin/lean"; MODE=native
else echo "candidate $FTC_ROOT does not start on this host"; exit 2; fi
echo "candidate: $FTC_ROOT ($MODE)"
for d in 037 014 031 040 020 004 061; do cp $F/$d-*/x/src/*.lean $W/src/; done; cp $F/040-*/x/src/Probe.lean $W/src/Probe040.lean; cp $F/020-*/x/src/Probe.lean $W/src/Probe.lean
cp $F/050-*/x/gen.py $W/; cp $F/020-*/x/Dump.lean $W/src/
cd $W/src
off() { LEAN_PATH=$W/off:$T33/lib/lean timeout ${TO:-300} $T33/bin/lean "$@"; }
fast() { LEAN_PATH=$W/fast:$FTC timeout ${TO:-300} "$FL" "$@"; }
bld() { for m in "$@"; do off -o $W/off/$m.olean $m.lean > /dev/null 2>&1; fast -o $W/fast/$m.olean $m.lean > /dev/null 2>&1; done; }
cmpout() { # name, file: compare stdout+rc of both
  o=$(off $2 2>&1; echo "rc=$?"); f=$(fast $2 2>&1; echo "rc=$?")
  if [ "$o" = "$f" ]; then echo "SAME       $1"; else echo "DIFFERENT  $1   official: $(echo "$o" | tr '\n' ' ' | cut -c1-70) | candidate: $(echo "$f" | tr '\n' ' ' | cut -c1-70)"; fi; }
cmprc() { # name, file: compare exit codes only
  off $2 > /dev/null 2>&1; o=$?; fast $2 > /dev/null 2>&1; f=$?
  if [ $o = $f ]; then echo "SAME       $1 (rc $o)"; else echo "DIFFERENT  $1   official rc=$o | candidate rc=$f"; fi; }
bld A B HA HB BigFn LA LB1 LB2
cmpout "004(1) closed-term caching: def x1/x2/x3 := tick" C.lean
cmprc  "004(3) proof needing a fresh counter (tick_or_fail)" E.lean
cmprc  "004(4) pure-code heartbeat budget (maxHeartbeats 800)" HC.lean
cmpout "004(5) per-thread heartbeat nondeterminism (24 tight theorems)" ND.lean
cmpout "014(a) activeScopes marker visible" Scopes.lean
cmprc  "014(b) raw State.state read (segfault)" RawState.lean
LEAN_ABORT_ON_PANIC=1 cmprc "014(c) official test binopInfoTree (Task.get panic, abort on panic)" BinopInfoTree.lean
cmpout "014(d) scoped instance under the marker namespace" ScopedMarker.lean
TO=60 cmprc "014(e) liveness: lazy import of a diverging user extension (60 s)" LC.lean
cmpout "020 env.contains of a fast-only core constant" Probe.lean
cmprc  "020 #check of a fast-only core constant" UsesNewApi.lean
o=$(off --run Dump.lean | sha256sum | cut -c1-16); f=$(fast --run Dump.lean | sha256sum | cut -c1-16)
[ "$o" = "$f" ] && echo "SAME       020 core library constants (types/values) identical" || echo "DIFFERENT  020 core library constants differ (sha $o vs $f)"
cmpout "031 Lean.libUVVersion" UV.lean
cmpout "031 libuv constrainedMemory" UVMem.lean
python3 -I -c "
import sys; b=bytearray(open('$W/off/A.olean','rb').read()); i=b.find(b'819816b2e0a3bf405af45ae5c7af2491d8f5bee6'); b[i:i+8]=b'deadbeef'; open('$W/foreign.olean','wb').write(b)"
mkdir -p $W/foreign; mv $W/foreign.olean $W/foreign/A.olean; printf 'import A\n#check cnt\n' > Fo.lean
o=$(LEAN_PATH=$W/foreign:$T33/lib/lean $T33/bin/lean Fo.lean > /dev/null 2>&1; echo $?); f=$(LEAN_PATH=$W/foreign:$FTC "$FL" Fo.lean > /dev/null 2>&1; echo $?)
[ $o = $f ] && echo "SAME       037 foreign-version olean (rc $o)" || echo "DIFFERENT  037 foreign-version olean   official rc=$o | candidate rc=$f"
cmprc  "040 getFunInfo on a big shared type (heartbeats)" Probe040.lean
o=$($T33/bin/lean --version); f=$("$FL" --version)
[ "$o" = "$f" ] && echo "SAME       061 lean --version (incl. target triple)" || echo "DIFFERENT  061 lean --version   official: $o | candidate: $f"
bld Tgt; cd $W; LEAN_PATH=$W/off:$T33/lib/lean $EXP Tgt -- buildTarget > e.off 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP Tgt -- buildTarget > e.fast 2>/dev/null; cd $W/src
[ -s $W/e.off ] && cmp -s $W/e.off $W/e.fast && echo "SAME       061 export of def buildTarget := elab-time System.Platform.target" || echo "DIFFERENT  061 export of def buildTarget := elab-time System.Platform.target"
cmprc  "061 theorem (platform% : String) = \"x86_64-pc-linux-gnu\" := rfl" Flip.lean
cmprc  "061 #guard_msgs in #version (toolchain-pin test)" Ver.lean
cmpout "061 Lean.Compiler.FFI.getLinkerFlags/getInternalLinkerFlags" Flags.lean
python3 -I $W/gen.py 398500 > Deep.lean; cmprc "050 stack band (398,500 nested parentheses)" Deep.lean
c=0; for m in A B HA HB; do cmp -s $W/off/$m.olean $W/fast/$m.olean || c=$((c+1)); done
echo "INFO       052 oleans of the 4 helper modules byte-different: $c/4 (official lean4export of their constants is what matters)"
}
main "$@"; exit $?
