import FrontierJudge

/-!
`fvfrontier-judge CONFIG SOLUTION_EXPORT [--allowed FILE]`. See FrontierJudge.lean.
Exit 0 = frontier OK, 1 = frontier REJECT, 2 = could not run. Last stdout line = one JSON object.
-/
def main (args : List String) : IO UInt32 := do
  let usage := "usage: fvfrontier-judge CONFIG SOLUTION_EXPORT [--allowed FILE]"
  let rec go (pos : List String) (allowed : Option String) : List String → Except String (List String × Option String)
    | [] => .ok (pos.reverse, allowed)
    | "--allowed" :: f :: rest => go pos (some f) rest
    | a :: rest => if a.startsWith "--" then .error s!"unknown option {a}" else go (a :: pos) allowed rest
  match go [] none args with
  | .error e => IO.eprintln s!"{e}\n{usage}"; IO.println (Lean.Json.compress (FrontierJudge.fail2 e).json); return 2
  | .ok ([cfg, exp], allowed) =>
    try
      let o ← FrontierJudge.judge cfg exp (allowed.map System.FilePath.mk)
      IO.println (Lean.Json.compress o.json)
      return o.code
    catch e =>
      IO.println (Lean.Json.compress (FrontierJudge.fail2 s!"{e}").json)
      return 2
  | .ok _ => IO.eprintln usage; IO.println (Lean.Json.compress (FrontierJudge.fail2 "usage").json); return 2
