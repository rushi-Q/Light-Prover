import Lean
open Lean Elab Command Parser

/-- every token of the parser extension: the global token table plus all scoped `.token` / `.parser` entries -/
def dumpTokens : CommandElabM Unit := do
  let env ← getEnv
  let mut out : Std.HashSet String := {}
  for t in (getTokenTable env).findPrefix "" do out := out.insert t
  let st : ScopedEnvExtension.StateStack ParserExtension.OLeanEntry ParserExtension.Entry ParserExtension.State :=
    parserExtension.ext.getState env
  for (_, arr) in st.scopedEntries.map.toList do
    for e in arr.toList do
      match e with
      | .token tk => out := out.insert tk
      | .parser _ _ _ p _ => for tk in p.info.collectTokens [] do out := out.insert tk
      | _ => pure ()
  let toks := out.toArray.qsort (· < ·)
  IO.FS.writeFile (System.FilePath.mk (← IO.getEnv "TOKOUT").get!) (String.intercalate "\n" toks.toList ++ "\n")
  logInfo m!"{toks.size} tokens"

#eval! dumpTokens
