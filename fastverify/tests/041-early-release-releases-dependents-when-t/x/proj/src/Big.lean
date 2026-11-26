module
public import Lean
open Lean Elab Command Meta

/-! A module-system file (Lean 4.33 `module`) whose private olean part is large: one theorem with a big proof term
(a balanced `Nat.add` tree over 1000000 distinct literals, built by a metaprogram). -/

meta def bigTree (lo hi : Nat) : Expr :=
  if hi - lo ≤ 1 then mkNatLit lo
  else
    let mid := (lo + hi) / 2
    mkApp2 (mkConst ``Nat.add) (bigTree lo mid) (bigTree mid hi)

run_cmd do
  let big := bigTree 0 1000000
  let value := mkApp (mkLambda `x .default (mkConst ``Nat) (mkConst ``True.intro)) big
  liftCoreM <| addDecl (.thmDecl { name := `bigThm, levelParams := [], type := mkConst ``True, value := value })

public theorem small : True := trivial
