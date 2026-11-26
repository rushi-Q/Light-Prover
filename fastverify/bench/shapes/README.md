# bench/shapes — synthetic projects of controlled shape

Generality benchmark: which project features make the fast presets fast, and when the speed-up shrinks or inverts.

| file | what |
|---|---|
| `gen.py OUTROOT CASE...` | generates `OUTROOT/challenge/` (shared: `theorem Shp.main : True := sorry`) and `OUTROOT/CASE/project/`; CASE = `BASE-SHAPE-N-CONTENT[-sSEED]` (see the docstring: base `core`/`mathlib`, shape `wide`/`deep`/`layered` (N = LxW), content `tiny`/`tactic`/`kernel`/`many`/`inductive`/`typeclass`/`universe`/`automation`) |
| `run.py ROOT CASE PRESET THREADS [--tag T] [-- extra fastverify args]` | one `bin/fastverify` run (env `FASTVERIFY` = package, `PACKAGES_WS` = trusted workspace); appends one JSON line to `ROOT/results.jsonl` (verdict, stage seconds, build attempts, export size/sha256, scheduler statistics from `sched.out`); deletes the export afterwards; pins the challenge with `--challenge-sha256` for sound presets when `ROOT/challenge/challenge.export.sha256` exists |
| `batch.sh ROOT THREADS "PRESETS" CASE...` | generate missing cases, run every case x preset sequentially |
| `threads.py LABEL=RESULTS.jsonl... [--md]` | thread-scaling table (one column per machine label and thread count) |
| `table.py RESULTS.jsonl... [--md] [--detail] [--presets LIST]` | per-case table (stage times per preset, speed-ups) / per-run breakdown (build fixed part, scheduler wall, lean processes, wall and CPU per process, toolchain) |
| `mklocal.sh DEST` | (run ON the host that runs the benchmarks; reads the toolchains from `~/.elan` and the trusted workspace / exporter from the site's install layout - adapt before use) node-local installation: copies of both official toolchains, the official exporter and the trusted workspace + a copy of the package configured by its own `tools/configure.py` (code and pins unchanged); use `DEST/fv/bin/fastverify ... --packages DEST/ws` |
| `model.py RESULTS.jsonl...` | splits every run into the fixed part F (= the 1-module case of the same base, median of repeats) and the scaling part S; prints S_ref/S_sound and the break-even scale factor |
| `styles.py RESULTS.jsonl...` | per-module cost of each content kind (build CPU, export bytes, official vs sound check) |
| `advise.py PROJECT [--threads P] [--json]` | reads only the project's sources and reports the shape features that decide the speed-up (modules, longest chain, library importers, single-importer chains, module-system files, `decide +kernel` markers, `@[to_dual]`, declarations per module), which `--preset sound` levers apply, which items to drop, and whether the official flow is expected to be faster; advice only |
| `fuzz.py ROOT N SEED THREADS [PRESET]` | random property test: random shapes x contents x a random defect (`sorry` / false `decide +kernel`) with the expected verdict known by construction; FAIL CRITICAL iff a defect is accepted |
| `test/shapes-test.sh` | the regression test behind `tests/shapes` |
| `challenge/` | the shared challenge (sources + sha256 of its official export; the export itself is rebuilt by the first `reference` run: copy `OUT/challenge.export` here) |

Reproduce (node-local installation; on hosts where `/home` is NFS every official `lean` pays extra latency):
```
./mklocal.sh $SCRATCH/local      # node-local official toolchains + exporter + trusted workspace + configured package copy
export FASTVERIFY=$SCRATCH/local/fv PACKAGES_WS=$SCRATCH/local/ws
python3 -I gen.py $SCRATCH/shapes core-wide-1-tiny
python3 -I run.py $SCRATCH/shapes core-wide-1-tiny reference 32
cp $SCRATCH/shapes/runs/core-wide-1-tiny-reference-*/challenge.export $SCRATCH/shapes/challenge/
sha256sum $SCRATCH/shapes/challenge/challenge.export | cut -d' ' -f1 > $SCRATCH/shapes/challenge/challenge.export.sha256
./batch.sh $SCRATCH/shapes 32 "reference fast-exact sound" core-deep-512-tiny mathlib-wide-128-tiny ...
python3 -I table.py $SCRATCH/shapes/results.jsonl --md
```
All projects are generated locally (no fetched code); every build runs inside the package's bwrap sandbox.
