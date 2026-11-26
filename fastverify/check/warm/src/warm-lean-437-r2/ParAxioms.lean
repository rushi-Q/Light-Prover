/-
Parallel drop-in for `Lake.Check.checkAxioms` (Lean 4.36 src/lake/Lake/Check/Axioms.lean).

Official algorithm: worklist BFS from the theorem/definition targets; for every popped constant `c`
(looked up in `solution.constMap`, error if missing) it calls `runForUsedConsts c validateConst`, where
`validateConst n` errors if `n` is not in `constMap` or is an axiom outside `legalAxioms`, and pushes
`n` if not yet checked. So it accepts iff every name in the closure R of the targets under the
`runForUsedConsts` edges is a key of `constMap` and no member of R is an illegal axiom.

This version: (1) the same target checks, in the same order, with the same messages;
(2) the `runForUsedConsts` name list of EVERY constant of `constMap`, computed in parallel tasks (pure);
(3) the same BFS over dense ids. It visits exactly R and applies exactly the same two predicates to
exactly the same names, so it errors iff the official one errors (only WHICH error is reported
first may differ when several exist). Verdict-identical; no kernel involvement.
-/
import Lake.Check.Util
import LeanExport.Parse

namespace ParAxioms
open Lean

/-- `runForUsedConsts` (official) collected into an array, in its call order. -/
def usedNames (info : ConstantInfo) : Array Name :=
  ((Lake.Check.runForUsedConsts (m := StateM (Array Name)) info fun n => modify (·.push n)).run #[]).2

/-- Used ids of `cis[lo:hi]`; a name that is not a key of `constMap` becomes `missing`. -/
def chunk (ids : Std.HashMap Name Nat) (cis : Array ConstantInfo) (missing lo hi : Nat) : Array (Array Nat) := Id.run do
  let mut out := Array.mkEmpty (hi - lo)
  for i in [lo:hi] do
    out := out.push <| (usedNames cis[i]!).map fun n => (ids[n]?).getD missing
  return out

def checkAxiomsPar (solution : LeanExport.ExportedEnv) (theoremTargets : Array Name)
    (definitionTargets : Array Name) (legalAxioms : Array Name) (nthreads : Nat := 16) :
    IO (Except String Unit) := do
  -- target checks: identical to the official function
  let mut worklist : Array Name := #[]
  for target in theoremTargets do
    let some solutionConst := solution.constMap[target]?
      | return .error s!"Const not found in solution: '{target}'"
    let .thmInfo solutionConst := solutionConst
      | return .error s!"Solution constant is not a theorem: '{target}'"
    worklist := worklist.push solutionConst.name
  for target in definitionTargets do
    let some solutionConst := solution.constMap[target]?
      | return .error s!"Const not found in solution: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | return .error s!"Solution constant is not a definition: '{target}'"
    worklist := worklist.push solutionConst.name
  let legal := Std.HashSet.ofArray legalAxioms
  -- dense ids
  let arr := solution.constMap.toArray
  let n := arr.size
  let cis := arr.map (·.2)
  let mut ids : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity n
  for h : i in [0:n] do
    ids := ids.insert arr[i].1 i
  -- used-name lists of all constants, in parallel
  let nt := max 1 nthreads
  let nchunks := max 1 (min (nt * 8) (n / 256 + 1))
  let csz := (n + nchunks - 1) / nchunks
  let mut tasks := #[]
  for c in [0:nchunks] do
    let lo := min n (c * csz)
    let hi := min n (lo + csz)
    tasks := tasks.push (Task.spawn (prio := .dedicated) fun _ => chunk ids cis n lo hi)
  let mut used : Array (Array Nat) := Array.mkEmpty n
  for t in tasks do
    used := used ++ t.get
  -- BFS over exactly the official closure
  let mut checked := ByteArray.mk (Array.replicate n 0)
  let mut stack : Array Nat := #[]
  for t in worklist do
    stack := stack.push ids[t]!   -- targets exist (checked above)
  while h : stack.size > 0 do
    let i := stack[stack.size - 1]
    stack := stack.pop
    if checked.get! i != 0 then continue
    for u in used[i]! do
      if u == n then
        -- recover the missing name for the official message
        let nm := (usedNames cis[i]!).find? (fun nm => !ids.contains nm) |>.getD .anonymous
        return .error s!"Constant not found in solution '{nm}'"
      if let .axiomInfo info := cis[u]! then
        if !legal.contains info.name then
          return .error s!"Illegal axiom detected: '{arr[u]!.1}'"
      if checked.get! u == 0 then stack := stack.push u
    checked := checked.set! i 1
  return .ok ()

end ParAxioms
