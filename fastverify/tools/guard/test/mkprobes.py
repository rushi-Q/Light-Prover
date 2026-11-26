#!/usr/bin/python3 -I
"""mkprobes.py CORPUS OUT [--scale K] : bounded resource probes for the service-guard test (tools/guard).

Every probe is an HONEST attempt of one problem of the small-proof corpus (bench/throughput/corpus/gen.py output: CORPUS/projects/
<name>/Solution.lean) with one resource-heavy `#eval` inserted after the imports. Each probe is BOUNDED: it ends by itself
within seconds and stays within the stated maximum even if no limit stops it, so the test is safe on a shared node.
Without limits each probe would be ACCEPTED (the proof is honest); with limits it must end in NO-VERDICT (resource limit
or timeout), never ACCEPTED and never REJECTED. The remaining problems get their honest attempt unchanged (must stay
ACCEPTED under the limits: no false NO-VERDICT for normal work).

Writes OUT/<theorem>.lean and OUT/expect.json = {theorem: {"probe": kind, "max": what it uses unguarded}}.
"""
import json, os, sys

# (problem, kind, max use, Lean #eval block)
PROBES = [
    ("nt_prime_1009", "mem", "4 GB heap in 100 MB steps", '''
#eval show IO Unit from do
  let mut keep : Array (Array Nat) := #[]
  for i in [0:40] do
    keep := keep.push (Array.replicate 12500000 i)
    IO.sleep 50
  IO.println s!"kept {keep.size} blocks"
'''),
    ("lia_chicken", "tmpfs", "1 GB written to the sandbox's /tmp (official-lean path); the fork-server path refuses the write (Landlock) -> compile error", '''
#eval show IO Unit from do
  let chunk := ByteArray.mk (Array.replicate (1024 * 1024) (0 : UInt8))
  for i in [0:10] do
    let h ← IO.FS.Handle.mk s!"/tmp/d07probe{i}" .write
    for _ in [0:100] do h.write chunk
    IO.sleep 100
'''),
    ("ineq_amgm2", "output", "100 MB of messages", '''
#eval show IO Unit from do
  let line := String.mk (List.replicate 50000 'x')
  for _ in [0:2000] do IO.println line
'''),
    ("rfl_nat_mul", "procs", "100 sleeping child processes for 3 s", '''
#eval show IO Unit from do
  let mut cs := #[]
  for _ in [0:100] do
    cs := cs.push (← IO.Process.spawn { cmd := "/bin/sleep", args := #["3"] })
  for c in cs do discard <| c.wait
'''),
    ("an_pi_gt3", "threads", "300 sleeping threads for 3 s", '''
#eval show IO Unit from do
  let mut ts := #[]
  for _ in [0:300] do
    ts := ts.push (← IO.asTask (prio := .dedicated) (IO.sleep 3000))
  for t in ts do discard <| IO.wait t
'''),
    ("dec_zmod", "spin", "one core for 90 s", '''
def d07BusyUntil (deadline : Nat) : IO Nat := do
  let mut i := 0
  while (← IO.monoMsNow) < deadline do
    i := i + 1
  return i

#eval show IO Unit from do
  let t ← IO.monoMsNow
  let n ← d07BusyUntil (t + 90000)
  IO.println s!"spun {n}"
'''),
]


def main():
    corpus, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    exp = {}
    probed = set()
    for name, kind, mx, block in PROBES:
        src = open(os.path.join(corpus, "projects", name, "Solution.lean")).read()
        lines = src.split("\n")
        k = 0
        while k < len(lines) and (lines[k].startswith("import ") or not lines[k].strip()):
            k += 1
        txt = "\n".join(lines[:k]) + "\n" + block + "\n" + "\n".join(lines[k:])
        open(os.path.join(out, name + ".lean"), "w").write(txt)
        exp[name] = {"probe": kind, "max": mx}
        probed.add(name)
    for name in sorted(os.listdir(os.path.join(corpus, "projects"))):
        if "--" in name or name == "BATCH" or name in probed:
            continue
        p = os.path.join(corpus, "projects", name, "Solution.lean")
        if os.path.isfile(p):
            open(os.path.join(out, name + ".lean"), "w").write(open(p).read())
            exp[name] = {"probe": None}
    json.dump(exp, open(os.path.join(out, "expect.json"), "w"), indent=1)
    print(f"{len(probed)} probes + {len(exp) - len(probed)} honest attempts -> {out}")


if __name__ == "__main__":
    main()
