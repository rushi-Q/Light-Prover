# Definition target not referenced by any theorem, body = sorry (a coverage gap of ParAxioms / checkAxioms)

The official `checkAxioms` seeds its worklist with the theorem targets AND the definition targets (`definition_names`), so
the body of every definition hole must be free of illegal axioms. Mutation testing: deleting the definition-target
seeding in ccmp's drop-in (ParAxioms-0006, ParAxioms.lean:49 `worklist := worklist.push solutionConst.name` -> `pure ()`)
SURVIVES every soundness-suite corpus (cmpx: definition_names = []; self-test: theorem only), and the existing package tests with a
`definition_names` hole (tests/cheat-bench CHT `hole`, tests/challenge-config `myDef`) cannot kill it either, because
there the hole occurs in a theorem statement and is reached through the theorem.

Here the hole is NOT mentioned by the theorem. All exports: official Lean 4.36.0 + its bundled leanexport 3.1.0, targets =
4.36 compareIt's export list (targets.txt). Results (check-sound.sh 0feac1c6 with the live pins / with ParAxioms-0006's ccmp):

| solution | live check-sound.sh | with mutant ParAxioms-0006 |
|---|---|---|
| Solution.export (`def hole : Nat := sorry`) | **REJECTED** `Illegal axiom detected: 'sorryAx'` | **ACCEPTED** (both kernels accept: sorryAx is just an axiom to them) |
| SolutionHonest.export (`def hole : Nat := 42`) | ACCEPTED | ACCEPTED |

Proposed suite case (cmpx-style, comparator-level): challenge = Challenge.export + comparator.json; Solution.export ->
REJECTED, SolutionHonest.export -> ACCEPTED.
