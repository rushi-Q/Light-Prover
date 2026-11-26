import Lean
open Lean
/-- realized max DFS depth of Lean.Replay on a chain d0 <- d1 <- ... <- dN whose names are `pre ++ "d" ++ i`
(top-level iteration in NameSet = Name.quickCmp order; visiting d_k replays d_(k-1).. down to the visited prefix). -/
def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let pre : Name := if args.length > 1 then args[1]!.toName else .anonymous
  let mut arr : Array (UInt64 × Nat) := Array.mkEmpty (n+1)
  for i in [0:n+1] do
    arr := arr.push ((Name.str pre ("d" ++ toString i)).hash, i)
  let sorted := arr.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  let mut m : Int := -1
  let mut best : Nat := 0
  let mut bestAt : Nat := 0
  let mut first : Nat := 0
  let mut k := 0
  for (_, j) in sorted do
    if k == 0 then first := j
    k := k + 1
    if (j : Int) > m then
      let d := (j : Int) - m
      if d.toNat > best then best := d.toNat; bestAt := j
      m := j
  IO.println s!"N={n} pre={pre}: first visited d{first}, max DFS depth {best} (at d{bestAt})"
