# bench/bigprojects — large public Lean projects through the fast presets and the official flow

The "other big projects" case of the generality study: real formalization projects pinned to the package's toolchain
(Lean 4.33.1, Mathlib `0df444a`), each against a challenge of its main theorems built by the official Lean, through
`--preset sound`, `fast-exact` and the official flow (`--preset reference` = official `lake build` -> official
`lean4export` -> unmodified `lake comparator` 4.36).

**Why these commits run on the trusted workspace.** Mathlib `db584cd6` (tag `v4.33.0`) and `0df444a` (`v4.33.1`) differ by
one commit that only bumps `lean-toolchain`; a project pinned at `db584cd6` is ported by changing its `lean-toolchain`
and the manifest's mathlib rev (no source change). PrimeNumberTheoremAnd and Foundation are natively on `0df444a`.

| file | what |
|---|---|
| `projects.tsv` | name, repository, commit, pin, port edits, solution module, challenge theorems, notes (10 rows, 8 projects) |
| `challenges/<name>/` | the clean challenge (statement(s) with `sorry`, `comparator.json`, lakefile, manifest; copies of the project's own statement definitions where the statement needs them: Carleson `Carleson/Defs.lean`, sphere-eversion `Immersion.lean`). No `challenge.export`: the package builds it with the official Lean (B0 + E0); pin it afterwards with `tools/pin.sh` |
| `tools/fetch.sh NAME [ROOT]` | clone (public git; no code is run), export the pinned commit to `ROOT/projects/NAME`, apply the documented port, copy the challenge |
| `tools/mkws.sh NAME [ROOT]` | the trusted dependency workspace `ROOT/ws/NAME`: packages shared with `TRUSTED_WS` (set it to the trusted Mathlib workspace, `$PACKAGES_WS`) are symlinked, other packages cloned at their manifest revisions into Lake's directory names, and the project's imports from them built OFFLINE in bwrap with the official lake (`tools/wsbuild.sh`) |
| `tools/run.sh NAME PRESET THREADS [ROOT] [args]` | one `bin/fastverify` run -> `ROOT/runs/NAME-PRESET[-TAG]` (`result.json`, `log/`; `TAG=x` suffixes the run name; `FV=` another package); sound runs use the pinned challenge if present |
| `tools/pin.sh NAME RUNDIR [ROOT]` | pin the official challenge export an earlier run built |
| `tools/collect.py RUNDIR...` | one TSV row per run: stage seconds, build attempts, modules, scheduler wall, sum of module walls / CPU, toolchain, zygote facts, export size, check legs |
| `tools/shape.py RUNDIR` | import-graph shape and schedule bounds of a B1-B3 build: modules, edges, depth, critical path from the measured walls, work, work/threads |
| `tools/exprdump.py EXPORT NAME` | canonical s-expression of a declaration's type in an NDJSON export (level params, binder info, constants with universes) - for diffing why `compareAt` rejects a restated statement |
| `tools/stmtdiff.py CHALLENGE.export SOLUTION.export NAME...` | explains a 'statement do not match': per name the universe parameter names and the FIRST differing subterm of the types (compareAt semantics: binder names/info ignored), e.g. `challenge: (InnerProductSpace.toNormedSpace ℝ ℝ Real.instRCLike)` vs `solution: NormedField.toNormedSpace` |
| `tools/r2real.sh NAME EXPORT CHALLENGE_DIR OUT` | kernel-level mutation classes (`tests/sound-gates/tools/mk_r2_specs.py` + `fvmut`) on a real project's honest export, each mutant labelled by the OFFICIAL comparator, then judged by `check/sound/check-sound.sh` (`tests/sound-gates/gates.py --gate mutants`) |
| `mutants/*.diff` | one-edit cheats inside real projects (PNT lemma by `sorry` / by a new `axiom`, Carleson statement definition weakened with all users re-proved) |

Example:
```
tools/fetch.sh pfr $SCRATCH/bp && tools/mkws.sh pfr $SCRATCH/bp
tools/run.sh pfr sound 48 $SCRATCH/bp            # builds the challenge officially; ACCEPTED
tools/pin.sh pfr $SCRATCH/bp/runs/pfr-sound $SCRATCH/bp
for p in sound fast-exact reference; do TAG=pinned tools/run.sh pfr $p 48 $SCRATCH/bp; done
tools/collect.py $SCRATCH/bp/runs/pfr-*/
```
Notes. (1) Writing a challenge for a real project: elaborate it under the same imports as the project file (or pin the
instances: `attribute [-instance] ...`), keep universe parameter names (declare the theorem in the same `variable` context
when the project does), and check equality with `exprdump.py` on both exports. (2) Foundation and PhysLean need the
package's unescaping of `«...»` package names (`lib/manifest.py`); pristine compfiles (lean_exe default targets) and
pristine PhysLean (Lake artifact cache) give no verdict. (3) On hosts with the official toolchain on NFS, official `lean`
processes pay extra latency; hosts with local disks (or a node-local install, `bench/shapes/mklocal.sh`) do not.
