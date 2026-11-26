import Lean
open Lean Meta Elab Command

/-- `e_{k}` = `Nat.add e_{k-1} e_{k-1}` with `e_0 = x` (the bound variable): DAG size k+1, tree size 2^(k+1)-1. -/
def bigShared (x : Expr) : Nat → Expr
  | 0 => x
  | k+1 => let e := bigShared x k; mkApp2 (mkConst ``Nat.add) e e

elab "mk_big_fn " n:ident k:num : command => liftTermElabM do
  let ty ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    let p ← mkEq (bigShared x k.getNat) (mkNatLit 0)
    withLocalDeclD `h p fun h => mkForallFVars #[x, h] (mkConst ``Nat)
  addDecl (.axiomDecl { name := n.getId, levelParams := [], type := ty, isUnsafe := false })

elab "fun_info " n:ident : command => liftTermElabM do
  let t0 ← IO.monoMsNow
  let info ← getFunInfo (mkConst n.getId)
  logInfo m!"getFunInfo {n.getId}: {info.paramInfo.size} params, deps of param 1 = {info.paramInfo[1]!.backDeps}, {(← IO.monoMsNow) - t0} ms"
