How the "lean" answers in expected.json were obtained: `lean --run DeclaredTheorems.lean <case>` (a harness that runs
Elab.runFrontend with Elab.async=false, takes the module name from the file path relative to the run directory and lists
the thmInfo constants the module adds), inside bwrap without network, Lean 4.33.1 and 4.36.0; Mathlib / Batteries cases
with the verify/challenge workspace on 4.33.1 only. Generated auxiliary names can differ with the module name or
elaboration mode (t._proof_1_1 in one run, t._proof_1 in another): only the "want" field (the lexer's expected answer:
Lean's user-named theorems, null for a name the source cannot determine, or UNCLEAR) is asserted.
