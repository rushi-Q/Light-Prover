# Benchmark harnesses

The scripts and small input specifications behind the measurements in [docs/benchmarks.md](../../docs/benchmarks.md). Raw results of past runs are not shipped: every harness writes
its rows, logs and per-run outputs to a work directory that you pass on the command line (the few shipped data files
are listed under [Shipped data](#shipped-data)).

Nothing here is trusted. A harness only drives `bin/fastverify`, the official Lean tools or the package's services and
records what they report; every verdict comes from the official flow or from the trusted check (`check/sound/`).

## Before you run anything

| what | how |
|---|---|
| package | `FASTVERIFY` = the `fastverify/` directory, configured for the host with `tools/configure.py`. Most harnesses default to the package that contains them. |
| official toolchains | Lean 4.33.1 and 4.36.0 under `$ELAN_HOME/toolchains` and the official `lean4export` (as for the package itself). Other releases are added with `tools/addrelease.py`. |
| trusted workspace | `PACKAGES_WS` (or `--packages WS` / `--ws WS` / `WS=`): the built dependency workspace with Mathlib `0df444a` that challenges import. Needed by every Mathlib-based case. |
| scratch | a node-local `$SCRATCH` for work directories. Mathlib-scale runs start many `lean` processes; on a network file system use `shapes/mklocal.sh DEST` to make node-local copies of the toolchains, the workspace and the package. |
| sandbox and limits | `bwrap` (the package sandboxes every untrusted build). cgroup v2 plus a scope launcher for `budget/` and `lowmem/`. |
| external inputs | `$BENCH_INPUTS/<name>`: large inputs that are not redistributed here: `rh-miniF` and `rh-mid` (subsets of the published Lean proof of the Riemann hypothesis; see `tests/rh-minif-export/PROJ_NOT_INCLUDED.md` for how such a subset is made) and a whole-Mathlib export. The real-project harnesses clone public repositories at pinned commits (network). |

Some scripts still default to directories of the machines the benchmarks were first run on. Read a script's header
before running it and set its variables for your host. Each subdirectory's README documents its files and arguments.

## Overview

| directory | measures | used by |
|---|---|---|
| [smallproofs/](smallproofs/) | one-theorem projects (20 proof styles, core and Mathlib) through the official flow and the fast presets | `tests/smallproofs`, `tests/other-releases`, `tests/multi-claims` |
| [throughput/](throughput/) | many small proofs: cost per proof, batch verification, attempt streams | `tests/batchverify`, `tools/fvserve/test/`, `tools/guard/test/` |
| [shapes/](shapes/) | synthetic projects of controlled shape (wide / deep / layered, content kinds) | `tests/shapes`; `shapes/mklocal.sh` is used by `tools/fvserve/` |
| [bigprojects/](bigprojects/) | large public Mathlib projects through `--preset sound` and the official flow, plus mutants | - |
| [codeprojects/](codeprojects/) | formalizations of software through the same presets | - |
| [mathapps/](mathapps/) | mathematics projects on exactly the trusted Mathlib | - |
| [mathlib-as-project/](mathlib-as-project/) | Mathlib slices, whole Mathlib and Mathlib's Archive built from source as the untrusted project | - |
| [rhmid/](rhmid/) | rh-mid (11,371 modules on top of the cached Mathlib) from sources; makes the rh-mid export used by `lowmem/` | - |
| [budget/](budget/) | memory and CPU of every stage of `--preset sound` and of the trusted check under cgroup-v2 limits; behaviour at the limit; the memory model behind `lib/budget.py` | `tests/budget` (also reads `budget/results/`) |
| [lowmem/](lowmem/) | memory floors of the standard and the low-memory judges, and concurrent checks under a shared memory cap | - |

Files used by the tests and tools in the last column must not be renamed or moved without updating them.

## Running the harnesses

Commands are run from the `fastverify/` directory; `CASE`, `NAME`, `ROOT`, `OUT`, `WORK` are yours to choose.

### smallproofs

```
python3 -I bench/smallproofs/gen.py $SCRATCH/sp                          # corpus: one project + clean challenge per case
bench/smallproofs/run1.sh $SCRATCH/sp CASE reference $SCRATCH/sp 8 src    # official flow; the challenge is built in the run
bench/smallproofs/mkgiven.sh $SCRATCH/sp $SCRATCH/sp CASE                 # pin that run's official challenge export
bench/smallproofs/run1.sh $SCRATCH/sp CASE sound $SCRATCH/sp 8 given      # a fast preset against the pinned challenge
bench/smallproofs/test/sound-smallproofs.sh [WORK]                        # the regression subset run by tests/g05
```

### throughput

```
python3 -I bench/throughput/corpus/gen.py $SCRATCH/tp/corpus [--names a,b,...]
python3 -I bench/throughput/mkattempts.py $SCRATCH/tp/corpus $SCRATCH/tp/att mix     # pos | mix | neg attempt sets
R=$SCRATCH/tp CORPUS=$SCRATCH/tp/corpus FV_PKG=$FASTVERIFY WS=$PACKAGES_WS THREADS=8 \
  bench/throughput/runq.sh QUEUE LANES        # QUEUE lines: "CASE PRESET MODE [fastverify args]", MODE = src | pin
python3 -I bench/throughput/table.py RUNROOT...
bench/throughput/test/test-batchverify.sh [WORK]                                      # the regression run of tests/g06
```

### shapes

```
python3 -I bench/shapes/gen.py $SCRATCH/shp core-wide-8-tiny core-deep-32-tiny       # CASE = BASE-SHAPE-N-CONTENT[-sSEED]
python3 -I bench/shapes/run.py $SCRATCH/shp core-wide-8-tiny sound 8                  # appends one JSON line to ROOT/results.jsonl
bench/shapes/batch.sh ROOT THREADS "PRESETS" CASE...
bench/shapes/test/shapes-test.sh [WORK]                                               # the regression run of tests/g10
```

### bigprojects, codeprojects, mathapps

The three share one layout: `projects.tsv` (repository, pinned commit, targets), `challenges/<name>/` (challenge
sources and `comparator.json`) and `tools/`.
```
bench/bigprojects/tools/fetch.sh NAME ROOT                       # clone at the pinned commit, port the toolchain pin
TRUSTED_WS=$PACKAGES_WS bench/bigprojects/tools/mkws.sh NAME ROOT
bench/bigprojects/tools/run.sh NAME reference 32 ROOT            # -> ROOT/runs/NAME-reference
bench/bigprojects/tools/pin.sh NAME ROOT/runs/NAME-reference ROOT  # pin the official challenge export
bench/bigprojects/tools/run.sh NAME sound 32 ROOT
python3 -I bench/bigprojects/tools/collect.py ROOT/runs/*
```
`codeprojects/tools/` and `mathapps/tools/` follow the same pattern. Pass `ROOT` explicitly.

### mathlib-as-project

```
python3 -I bench/mathlib-as-project/mkml.py MATHLIB_SRC $SCRATCH/ml      # ONLY=prime,sylow restricts the cases
R=$SCRATCH/ml FV=$FASTVERIFY WS=$PACKAGES_WS bench/mathlib-as-project/runml3.sh CASE PRESET THREADS [SUFFIX] [args]
python3 -I bench/mathlib-as-project/summ.py RUNDIR...
```

### rhmid

```
RHMID=$BENCH_INPUTS/rh-mid WS=$PACKAGES_WS bench/rhmid/run-dev.sh OUT PRESET [fastverify args]
```
The run uses `rhmid/lakefile.toml` in place of the input's own lakefile.

### budget

```
CGRUN_TOOL=/path/to/scope-launcher bench/budget/cgrun.sh --name NAME --mem 8G --cpus 0-15 --json OUT.json -- CMD...
bench/budget/run_fv.sh OUT TAG CPUS MEM THREADS PROJECT CHALLENGE [fastverify args]
bench/budget/sweep_check.sh OUT LABEL INDIR CPUBASE "THREADS..." [MEM...]
python3 -I bench/budget/fit.py bench/budget/sizes.json bench/budget/results/sweep1 bench/budget/results/legs1
python3 -I bench/budget/mkreport.py bench/budget/results
```

### lowmem

```
python3 -I bench/lowmem/run_c5_benchmarks.py FV BENCH_INPUTS OUT_DIR    # single-check memory floors
python3 -I bench/lowmem/run_c5_cliff.py FV BENCH_INPUTS OUT_DIR         # concurrent checks under a shared cap
```
Inputs: `$BENCH_INPUTS/{rh-miniF,rh-mid}/{ref/solution.export,challenge/}` and a whole-Mathlib export. The scope
launcher path is the `CGRUN` constant at the top of `run_c5_benchmarks.py`.

## Shipped data

* `budget/results/{sweep1,legs1,limits1}/`: the cgroup-v2 measurement rows (JSON plus sibling `.out`) that
  `tests/budget/run.sh` checks and from which the memory model of `lib/budget.py` is fitted (`budget/fit.py`).
  Command lines inside them show the directories of the hosts they were recorded on; they are records, not
  instructions.
* Input specifications: `projects.tsv` and `challenges/` of `bigprojects/`, `codeprojects/` and `mathapps/`
  (`mathapps/repos.txt`, `bigprojects/mutants/`), `shapes/challenge/`, `throughput/corpus/`, `smallproofs/problems.py`, `budget/sizes.json`, `rhmid/lakefile.toml`.
