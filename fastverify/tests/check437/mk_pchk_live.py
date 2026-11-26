#!/usr/bin/env python3
# mk_pchk_live.py PAR_LEAN - DIAGNOSTIC-ONLY patch of PChk/Par.lean (encapsulated-replay source): with PCHK_LIVE_MS=<ms> in the environment a
# monitor thread prints every <ms> the jobs that have been running for at least <ms> ("[pchk-live] NAME (walk index I) running
# for T ms"). Walk code only; no kernel change; not for pinning (the deciding binaries stay the pinned ones).
import sys
p = sys.argv[1]; s = open(p).read()
def rep(old, new, n=1):
    global s
    assert s.count(old) == n, (old[:60], s.count(old))
    s = s.replace(old, new)
rep("    (logMinNs : Nat := 0) :\n    IO (JobChan × JobChan × Array IO.CancelToken ×",
    "    (logMinNs : Nat := 0) (liveMs : Nat := 0) :\n    IO (JobChan × JobChan × Array IO.CancelToken ×")
rep("""  let mut slots : Array (IO.CancelToken × IO.Ref Nat) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)))
  let mut ts := #[]
  for (tk, cur) in slots do
""", """  let mut slots : Array (IO.CancelToken × IO.Ref Nat × IO.Ref (Name × Nat)) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)), (← IO.mkRef ((Name.anonymous, 0) : Name × Nat)))
  -- DIAGNOSTIC (PCHK_LIVE_MS): report long-running jobs while they run; stops when every worker has returned
  let active ← IO.mkRef nw
  if liveMs > 0 then
    let _ ← IO.asTask (prio := .dedicated) do
      repeat
        IO.sleep liveMs.toUInt32
        if (← active.get) == 0 then break
        let now ← IO.monoNanosNow
        let mut cnt := 0
        for (_, cur, lv) in slots do
          let (n, a) ← lv.get
          if a > 0 && now - a >= liveMs * 1000000 then
            cnt := cnt + 1
            IO.eprintln s!"[pchk-live] {n} (walk index {← cur.get}) running for {(now - a) / 1000000} ms"
        IO.eprintln s!"[pchk-live] {cnt} job(s) over {liveMs} ms; {← active.get} worker(s) active"
  let mut ts := #[]
  for (tk, cur, lv) in slots do
""")
rep("""              cur.set idx
              let a ← IO.monoNanosNow
              let r := f tk js[k]
              out := out.push (idx, r)
""", """              cur.set idx
              let a ← IO.monoNanosNow
              lv.set (js[k].name, a)
              let r := f tk js[k]
              lv.set (Name.anonymous, 0)
              out := out.push (idx, r)
""")
rep("""                for (tk', cur') in slots do
                  if (← cur'.get) > c then tk'.set
""", """                for (tk', cur', _) in slots do
                  if (← cur'.get) > c then tk'.set
""")
rep("""        | none => break
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, pch, slots.map (·.1), ts)
""", """        | none => break
      active.modify (· - 1)
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, pch, slots.map (·.1), ts)
""")
rep("""  let (ch, pch, tks, workers) ← startPools nw (fun tk j => runJob tk j) .cancelled decided (logMinMs * 1000000)
""", """  let liveMs := ((← IO.getEnv "PCHK_LIVE_MS").bind String.toNat?).getD 0
  let (ch, pch, tks, workers) ← startPools nw (fun tk j => runJob tk j) .cancelled decided (logMinMs * 1000000) liveMs
""")
open(p, "w").write(s); print("patched", p)
