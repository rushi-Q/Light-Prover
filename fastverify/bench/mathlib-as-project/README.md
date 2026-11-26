# bench/mathlib-as-project — Mathlib 0df444a itself as the (untrusted) project, plus Mathlib's Archive downstream

The other harnesses use Mathlib as a TRUSTED, pre-built dependency. These cases build
Mathlib (or a slice of it) from source as the project to be judged; the challenge imports the trusted cached Mathlib.

| file | what |
|---|---|
| `mkml.py SRC OUT` | generates `OUT/proj/<case>` (hard links of the Mathlib sources, no `.lake`/`.git`, Mathlib's `lakefile.lean` translated to `lakefile.toml` with the same `leanOptions`, a `Solution` module with `type_of% @Name := @Name` targets) and `OUT/chal/<case>` (challenge importing the trusted Mathlib). Cases: `prime` (328 modules), `sylow` (1,096), `qr` (2,568), `dirichlet` (3,417), `whole` (8,313, 10 targets), diagnostics `isd`, `withbot`, `dualmut` (the case behind `tests/confirm-reject`). `ONLY=a,b` restricts. `WS_MANIFEST` = the trusted workspace manifest. |
| `mkarc.py SRC OUT` | the `archive` case: Mathlib's `Archive` (85 modules, IMO / textbook proofs) + `Counterexamples` (30) as one downstream project on the cached Mathlib, roots renamed `Arc`/`Cex` (the mathlib package itself declares libraries `Archive`/`Counterexamples`; with the original names the official `lake build` resolves the modules to the read-only dependency and fails), 7 IMO targets with explicit challenge statements. |
| `runml3.sh CASE PRESET THREADS SUFFIX [args]` | one `bin/fastverify` run (env `FV`, `WS` = package / trusted workspace, `PIN` = taskset CPU list, `R` = root) -> `R/runs/CASE.PRESET<SUFFIX>`; appends to `R/runs/summary.tsv`. |
| `summ.py RUNDIR...` | one JSON line per run: verdict, build attempts, stage seconds, export size/sha, scheduler stats. |
| `cpath.py PLAN THREADS --sched sched.out | --lakelog build.log` | build shape: sum of module walls, work bound, critical path (walls along the longest import chain), import depth. |
| `closure.py ROOT MOD...` | import-closure size and depth from the sources. |
| `exportenv.sh PROJLIB OUT MODULE` | official lean4export of a module's whole environment from an untrusted build tree (bwrap) - e.g. to check whether a skip-kernel-tc build wrote kernel-invalid declarations. |
| `ablation_withbot.sh`, `dualmut.sh`, `exportin_mathlib.sh` | example job queues for a multi-core host (site-specific paths; adapt before use: point `T=` at this directory's `runml3.sh`) |
| `mktable.py SUMM.jsonl...`, `wallratio.py` | tables from the `summ.py` lines; per-module wall ratios fast vs official |
| `editcost.py SRC --sched sched.out [--threads T]` | model: re-verification cost after editing one library module (rebuild set = transitive importers; max(critical path, work/T) from measured walls) |

With skip-kernel-tc the build fails on Mathlib's `@[to_dual]` translation, which uses kernel errors as control flow
(-> B1 fallback); `--confirm-reject` covers the same root cause (regression test `tests/confirm-reject`).

## Reproduce

```
python3 mkml.py <copy of $PACKAGES_WS/.lake/packages/mathlib> $SCRATCH/ml          # cases (hard links)
python3 mkarc.py ... $SCRATCH/ml                                                     # archive case
R=$SCRATCH/ml FV=$FASTVERIFY/bin/fastverify WS=$PACKAGES_WS PIN=4-35,108-139 ./runml3.sh qr reference 64 -L
R=$SCRATCH/ml ... ./runml3.sh qr sound 64 -L-noktc --unsafe "toolchain-T1=lean4-7586a50cec-nopgo,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
python3 summ.py $SCRATCH/ml/runs/qr.* ; python3 cpath.py $SCRATCH/ml/runs/qr.sound-L-noktc/log/build-fast/plan.jsonl 64 --sched .../sched.out
```
Use node-local copies of the official toolchains and the workspace (`bench/shapes/mklocal.sh`): on NFS every
official `lean` pays a large per-import latency. Delete `log/build-fast/plan.jsonl` after a run (several GB for whole
Mathlib).
