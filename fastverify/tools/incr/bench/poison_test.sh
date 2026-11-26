#!/bin/bash
# does a hostile edit's elaboration-time code reach the BASE tree through the hard-linked copy? (isolation check of tools/incr)
set -u
FVR=$(cd "$(dirname "$(readlink -f "$0")")/../../.." && pwd)   # this package
V=${FV_SCRATCH:?node-local work root of the incremental benchmarks (required, layout in README.md)}
TINY=${TINY_PROJ:-$FVR/tests/incr-reverify/x/tiny}   # the tiny two-module project (Tiny.A, Tiny.B)
B=$V/tinybase-poison; rm -rf $B $V/poison-src $V/poison-out
cp -a $V/tinybase $B
mkdir -p $V/poison-src; cp -a $TINY/. $V/poison-src/
cat > $V/poison-src/Solution.lean <<'LEAN'
import Tiny.B
#eval show IO Unit from do
  let cwd ← IO.currentDir
  let p := cwd / ".lake" / "build" / "lib" / "lean" / "Tiny" / "A.olean"
  try
    IO.FS.writeFile p "poisoned by a hostile edit"
    IO.println s!"wrote {p}"
  catch e => IO.println s!"write failed: {e}"
theorem foo : (2 : Nat) + 2 = 4 := by
  have h := tinyB
  rw [tinyA] at h
LEAN
md5sum $B/work/proj/.lake/build/lib/lean/Tiny/A.olean
$FVR/tools/incr/incr-reverify.sh $B $V/poison-src $V/tinych $V/poison-out --challenge-sha256 90e564989a690de0828822d18c07ac8f4535c4432f160af0c1edf465af2df32a --threads 8 | tail -1 | cut -c1-300
echo "base A.olean after:"; md5sum $B/work/proj/.lake/build/lib/lean/Tiny/A.olean; head -c 60 $B/work/proj/.lake/build/lib/lean/Tiny/A.olean; echo
grep -h "wrote\|write failed" $V/poison-out/a1-full/work/log/sched.out | head -3 | cut -c1-300
