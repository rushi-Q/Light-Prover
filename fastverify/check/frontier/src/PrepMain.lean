import FrontierPrep

/-! `fvfrontier-prep` (UNTRUSTED helper of tools/frontier/frontier.py; see FrontierPrep.lean). Exit 0 = done (JSON on
stdout), 2 = failure (JSON with "error"). -/
def main (args : List String) : IO UInt32 := do
  let usage := "usage: fvfrontier-prep scan CONFIG EXPORT [--list FILE] [--axioms FILE] | mint CHALLENGE_EXPORT SOLUTION_PRIME_EXPORT FRONTIER_FILE OUT | prepare CONFIG EXPORT CHALLENGE_EXPORT OUTDIR [--list FILE] [--axioms FILE]"
  let err (m : String) : IO UInt32 := do
    IO.println (Lean.Json.compress (Lean.Json.mkObj [("error", Lean.Json.str m)])); return 2
  try
    match args with
    | "scan" :: cfg :: exp :: rest =>
      let rec opt (k : String) : List String → Option String
        | a :: b :: r => if a == k then some b else opt k (b :: r)
        | _ => none
      let j ← FrontierPrep.scan cfg exp ((opt "--list" rest).map System.FilePath.mk) ((opt "--axioms" rest).map System.FilePath.mk)
      IO.println j.compress; return 0
    | "prepare" :: cfg :: sol :: chal :: out :: rest =>
      let rec opt2 (k : String) : List String → Option String
        | a :: b :: r => if a == k then some b else opt2 k (b :: r)
        | _ => none
      let j ← FrontierPrep.prepare cfg sol chal out ((opt2 "--list" rest).map System.FilePath.mk) ((opt2 "--axioms" rest).map System.FilePath.mk)
        (redirect := !rest.contains "--in-place") (probe? := (opt2 "--probe" rest).map System.FilePath.mk)
      IO.println j.compress; return 0
    | ["mint", c, s, f, o] =>
      let j ← FrontierPrep.mint c s f o
      IO.println j.compress; return 0
    | _ => IO.eprintln usage; err "usage"
  catch e => err s!"{e}"
