#!/usr/bin/python3 -I
"""mk_pchk_budget.py SRCDIR - the replay-budget edit of the encapsulated replay: exact, reviewable edits of
the encapsulated-replay sources (PChk/Par.lean 7387b667, Main.lean 3a139fe0). (1) Every encapsulated kernel attempt runs under its
OWN cancel token, set by a pool watchdog after PCHK_ENCAP_BUDGET_MS (default 600000 ms) or when the worker itself is cancelled;
an interrupted or failed attempt is never a verdict - the full-environment check under the global token decides, exactly as
before. (2) The same watchdog names the jobs running longer than PCHK_LIVE_MS (if set) on stderr while they run. Walk code
only; no kernel change. Every pattern must match exactly once."""
import sys, os
d = sys.argv[1]
def patch(path, reps):
    s = open(path, encoding="utf-8").read()
    for old, new in reps:
        n = s.count(old); assert n == 1, (path, n, old[:80])
        s = s.replace(old, new)
    open(path, "w", encoding="utf-8").write(s); print("patched", path)
patch(os.path.join(d, "PChk/Par.lean"), [
("""@[noinline] def runJob (tk : IO.CancelToken) (j : Job) : JobResult :=
  match j.encap with
  | none => runJobFull tk j
  | some ee =>
    -- D23-E: the unmodified kernel in the encapsulated environment first (fewer delta rules: an ACCEPT here is valid in
    -- env); a kernel error is not a verdict - the full environment re-checks and decides
    match ee.addDeclCore 0 0 j.decl (cancelTk? := some tk) with
    | .ok _ => .ok
    | .error .interrupted => .cancelled
    | .error _ => runJobFull tk j
""", """@[noinline] def runJob (tk etk : IO.CancelToken) (j : Job) : JobResult :=
  match j.encap with
  | none => runJobFull tk j
  | some ee =>
    -- D23-E: the unmodified kernel in the encapsulated environment first (fewer delta rules: an ACCEPT here is valid in
    -- env); a kernel error is not a verdict - the full environment re-checks and decides. The attempt runs under its
    -- OWN token `etk`, which the pool watchdog sets after the encapsulation budget (an attempt that needs a hidden body
    -- may search instead of failing) or when the worker is cancelled; an interrupted attempt is not a verdict
    -- either - the full check under the global token `tk` decides (and is `.cancelled` at once if the worker was).
    match ee.addDeclCore 0 0 j.decl (cancelTk? := some etk) with
    | .ok _ => .ok
    | .error _ => runJobFull tk j
"""),
("""/-- `n` dedicated worker threads applying `f` to every job of every batch received on two fresh channels: the""",
 """/-- Per-worker record for the pool watchdog (encapsulated replay): the running job's name, its start (monotonic ns) and the cancel
token of its encapsulated attempt. -/
structure LiveSlot where
  name : Name := .anonymous
  start : Nat := 0
  etk : IO.CancelToken

/-- `n` dedicated worker threads applying `f` to every job of every batch received on two fresh channels: the"""),
("""def startPools {α : Type} (n : Nat) (f : IO.CancelToken → Job → α) (skip : α) (stop : α → Bool)
    (logMinNs : Nat := 0) :
    IO (JobChan × JobChan × Array IO.CancelToken ×""",
 """def startPools {α : Type} (n : Nat) (f : IO.CancelToken → IO.CancelToken → Job → α) (skip : α) (stop : α → Bool)
    (logMinNs : Nat := 0) (budgetMs : Nat := 0) (liveMs : Nat := 0) :
    IO (JobChan × JobChan × Array IO.CancelToken ×"""),
("""  let mut slots : Array (IO.CancelToken × IO.Ref Nat) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)))
  let mut ts := #[]
  for (tk, cur) in slots do
""", """  let mut slots : Array (IO.CancelToken × IO.Ref Nat × IO.Ref LiveSlot) := #[]
  for _ in [0:nw] do
    slots := slots.push ((← IO.CancelToken.new), (← IO.mkRef (0 : Nat)), (← IO.mkRef ({ etk := ← IO.CancelToken.new } : LiveSlot)))
  -- encapsulated replay: pool watchdog (one thread). Every 200 ms: the encapsulated attempt of a job older than `budgetMs` (if > 0), or
  -- of a cancelled worker, gets its own token set, so that the kernel returns `.interrupted` there and `runJob` falls through
  -- to the full-environment check, which decides. Every `liveMs` (if > 0) the jobs running longer than `liveMs` are named on
  -- stderr. No result changes: tokens only stop kernel calls, and a stopped encapsulated attempt is never a verdict.
  let active ← IO.mkRef nw
  let _watch ← IO.asTask (prio := .dedicated) do
    let mut lastLive ← IO.monoNanosNow
    repeat
      IO.sleep 200
      if (← active.get) == 0 then break
      let now ← IO.monoNanosNow
      let live := liveMs > 0 && now - lastLive ≥ liveMs * 1000000
      let mut cnt := 0
      for (tk, cur, lv) in slots do
        let s ← lv.get
        if s.start > 0 then
          if budgetMs > 0 && now - s.start ≥ budgetMs * 1000000 then s.etk.set
          if ← tk.isSet then s.etk.set
          if live && now - s.start ≥ liveMs * 1000000 then
            cnt := cnt + 1
            IO.eprintln s!"[pchk-live] {s.name} (walk index {← cur.get}) running for {(now - s.start) / 1000000} ms"
      if live then
        IO.eprintln s!"[pchk-live] {cnt} job(s) over {liveMs} ms; {← active.get} worker(s) active"
        lastLive := now
  let mut ts := #[]
  for (tk, cur, lv) in slots do
"""),
("""              cur.set idx
              let a ← IO.monoNanosNow
              let r := f tk js[k]
              out := out.push (idx, r)
""", """              cur.set idx
              let a ← IO.monoNanosNow
              let etk ← IO.CancelToken.new
              lv.set { name := js[k].name, start := a, etk }
              let r := f tk etk js[k]
              lv.set { name := .anonymous, start := 0, etk }
              out := out.push (idx, r)
"""),
("""                for (tk', cur') in slots do
                  if (← cur'.get) > c then tk'.set
""", """                for (tk', cur', _) in slots do
                  if (← cur'.get) > c then tk'.set
"""),
("""        | none => break
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, pch, slots.map (·.1), ts)
""", """        | none => break
      active.modify (· - 1)
      return (out, { ws with finish := ← IO.monoNanosNow }))
  return (ch, pch, slots.map (·.1), ts)
"""),
("""  let (ch, pch, tks, ts) ← startPools n f skip stop
""", """  let (ch, pch, tks, ts) ← startPools n (fun tk _ j => f tk j) skip stop
"""),
("""    (verbose := false) (prio : NameSet := {}) (logMinMs : Nat := 0) (encapOn : Bool := false) (hide : NameSet := {}) :
    IO Kernel.Environment := do
""", """    (verbose := false) (prio : NameSet := {}) (logMinMs : Nat := 0) (encapOn : Bool := false) (hide : NameSet := {})
    (encapBudgetMs : Nat := 600000) (liveMs : Nat := 0) :
    IO Kernel.Environment := do
"""),
("""  if encapOn then log s!"encapsulated replay on: {hide.size} hidden definitions + theorems as axioms in the second chain"
""", """  if encapOn then log s!"encapsulated replay on: {hide.size} hidden definitions + theorems as axioms in the second chain; budget {encapBudgetMs} ms per attempt"
"""),
("""  let (ch, pch, tks, workers) ← startPools nw (fun tk j => runJob tk j) .cancelled decided (logMinMs * 1000000)
""", """  let (ch, pch, tks, workers) ← startPools nw (fun tk etk j => runJob tk etk j) .cancelled decided (logMinMs * 1000000)
    (if encapOn then encapBudgetMs else 0) liveMs
"""),
])
patch(os.path.join(d, "Main.lean"), [
("""          | none => pure (false, {})
""", """          | none => pure (false, {})
        -- D23-E r2: PCHK_ENCAP_BUDGET_MS = time budget of one encapsulated attempt (default 600000; 0 = none), after which
        -- the full-environment check decides; PCHK_LIVE_MS = name the jobs running longer than this on stderr (0 = off)
        let envNat (v : String) (dflt : Nat) : IO Nat := do
          pure (((← IO.getEnv v).bind String.toNat?).getD dflt)
        let encapBudgetMs ← envNat "PCHK_ENCAP_BUDGET_MS" 600000
        let liveMs ← envNat "PCHK_LIVE_MS" 0
"""),
("""        kernelEnv ← PChk.replayPar kernelConstMap kernelEnv nthreads verbose prio logMinMs encapOn hide
""", """        kernelEnv ← PChk.replayPar kernelConstMap kernelEnv nthreads verbose prio logMinMs encapOn hide encapBudgetMs liveMs
"""),
])
print("ok")
