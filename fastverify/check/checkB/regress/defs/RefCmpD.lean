import Lake.Check.Compare
import Lake.Check.Axioms
import LeanExport.Parse

/-! Reference: exactly `verifyCompare` of Lake/CLI/Check.lean (4.36) incl. definition targets, without the kernel runs.
    (based on fuzz/ref/RefCmp.lean) -/
open Lake.Check

def primitives : Array Lean.Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble,
  ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
  ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam, ``semiOutParam,
  ``outParam]

def names (s : String) : Array Lean.Name :=
  ((s.splitOn ",").filter (fun x => x ≠ "" && x ≠ "-")).toArray.map String.toName

def runOne (chal sol : String) (theoremNames defNames legal : Array Lean.Name) : IO UInt32 := do
  try
    let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk chal .read)
    let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk sol .read)
    IO.ofExcept <| compareAt challenge solution (theoremNames ++ legal) defNames primitives
    IO.ofExcept <| checkAxioms solution theoremNames defNames legal
    IO.println "ref: ok"
    return 0
  catch e =>
    IO.println s!"ref: rejected: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [chal, thms, defs, axs, sol] =>
    runOne chal sol (names thms) (names defs) (names axs)
  | [chal, thms, defs, axs, "--list", listFile] =>
    for f in (← IO.FS.lines listFile) do
      let rc ← runOne chal f (names thms) (names defs) (names axs)
      IO.println s!"RESULT {rc} {f}"
    return 0
  | _ =>
    IO.eprintln "usage: refcmpd CHALLENGE THMS DEFS AXIOMS SOLUTION | refcmpd CHALLENGE THMS DEFS AXIOMS --list FILE  (lists: comma-separated, '-' or '' = none)"
    return 2
