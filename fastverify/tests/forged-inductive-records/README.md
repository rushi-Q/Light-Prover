# Forged inductive records (a coverage gap of PChk/Par.lean `sameAdded` / `ciStrictEq`)

The official `Lean.Replay` adds an inductive block with the kernel's OWN generated `inductInfo` and compares only the
constructor and recursor records with the export (postponed checks); a differing exported `inductInfo` record is ignored.
`pleanchecker` (PChk/Par.lean) instead inserts the EXPORTED records speculatively and relies on `sameAdded`/`ciStrictEq`
(plus the phase-1 learning) to replace them by the kernel's records. That strict comparison is the only thing that keeps
the walk's environment equal to the official one. Mutation testing showed that weakening it
(e.g. `a.name == b.name && ...` -> `a.name == b.name || ...` in the `inductInfo` arm) survives every soundness-suite corpus
(arena, suitex, cmpx, the kernel-cves cases, selftest), because no suite export has an inductive record that differs from the kernel's in a
field the 4.36 type checker reads (`isRec`, `numIndices`, constructor count: is_non_rec_structure -> structure eta,
unit-like defeq, projections).

Source: T.lean (official Lean 4.36.0 + its bundled leanexport 3.1.0) -> T-honest.export; the other files are one-field edits.

| file | edit | official leanchecker 4.36 | pleanchecker (live walk) | gruszka | weakened mutant PChkPar-0094 |
|---|---|---|---|---|---|
| T-honest.export | none | 0 | 0 | 0 | 0 |
| T-isrec-forged.export | T's inductInfo `isRec` true -> false (unused) | 0 | 0 | 2 | 0 |
| T-numidx-forged.export | T's inductInfo `numIndices` 0 -> 1 (unused) | 0 | 0 | 2 | 0 |
| T-eta-honest-rec.export | `foo : forall x : T, x = T.mk x.1 := fun x => rfl` (needs structure eta) | 1 | 1 | 1 | 1 |
| T-eta-forged-isrec.export | the same theorem + forged `isRec = false` | **1** | **1** | 2 | **0 (accepts)** |

Proposed suite labels (kernel-only corpus, suitex-style): good = T-honest, T-isrec-forged, T-numidx-forged; bad =
T-eta-honest-rec, T-eta-forged-isrec. With them, the weakened comparison is caught as FAIL-CRITICAL (lean leg accepts a bad
test).

## Second family: every record of the block forged (kills the NEGATED comparison, PChkPar-0176/0177)

`if !ciStrictEq v c then return some ...` -> `if ciStrictEq v c then return some ...` reports a mismatch whenever a record
EQUALS the kernel's and accepts the block when ALL differ. Any honest block in the same export (e.g. `Eq`) triggers the
official fallback, so the killing test has a single, fully forged block:

| file | edit | official | pleanchecker | gruszka | mutant 0177 | mutant 0094 |
|---|---|---|---|---|---|---|
| Tonly-honest.export | first 47 lines of T-honest (T only) | 0 | 0 | 0 | 0 | 0 |
| Tonly-allforged.export | T: isRec false; T.mk: numFields 2; T.rec: k true | **1** (Invalid constructor T.mk) | **1** | 1 | **0 (accepts)** | 1 |
| T-allforged.export | the same with Eq + foo present | 1 | 1 | 1 | 1 (fallback via Eq) | 1 |
| T-ctor-forged.export | only T.mk numFields 2 | 1 | 1 | 1 | 1 | 1 |

Proposed labels: good = Tonly-honest; bad = Tonly-allforged, T-allforged, T-ctor-forged.

## Labels after the replay veto checks (the export-record check C2 ported to the 4.36 walk)
The veto checks' checkExportRecords requires every export record whose name is a kernel constant to equal that constant, so
the Lean leg with them (release-libs build 05b60b8e of check-sound-src) REJECTS T-isrec-forged and T-numidx-forged, which
the official 4.36 replay accepts (it ignores the exported inductInfo record). Stricter than official on records no genuine
export contains, intended. So: with the veto checks installed, label those two as bad (lean-leg rejection expected); without them,
good (official verdict). The killing cases (T-eta-forged-isrec, Tonly-allforged, T-allforged, T-ctor-forged) are bad either
way, and T-honest / Tonly-honest are good either way (the veto checks accept them).
