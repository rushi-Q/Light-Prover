# bench/codeprojects — code and software formalizations through the fast presets and the official flow

The "code formalizations" case of the generality study: Lean formalizations of software (an authorization language,
differential-privacy samplers, ZK circuits and proof systems, cryptographic games, a distributed-computing impossibility
result, a Datalog certificate checker) at the commit of each project that pins the package's trusted toolchain (Lean 4.33.1 + Mathlib `0df444a`, or v4.33.0 = Mathlib `db584cd6`, ported by the one-commit
toolchain bump), each against a challenge of its main theorems built by the official Lean, through `--preset sound`,
`fast-exact`, `sound --build B0` and the official flow (`--preset reference` = sandboxed official `lake build` -> official
`lean4export` -> unmodified Lean 4.36 `lake comparator`). One project (`cedar436`) is Cedar's current HEAD on Lean 4.36.0
(the other-release path).

| file | what |
|---|---|
| `projects.tsv` | name, repository, commit, subdirectory, Lean, dependencies, port edits, solution module, challenge theorems, notes. `<name>toml` rows = the same commit with the root `lakefile.lean` replaced by an equivalent `lakefile.toml` |
| `challenges/<name>/` | the challenge: `Challenge.lean` (statements with `sorry`) or `prefix.txt` (`FILE THEOREM[,THEOREM...]`), `comparator.json`, `lakefile.toml`, `lean-toolchain` (+ manifest if it differs from the project's) |
| `tools/fetch.sh NAME [ROOT]` | blobless clone (public git, NO code run), export of the pinned commit's subdirectory to `ROOT/projects/NAME`, port edits, the challenge = the challenge files + the project's module trees (third-party sources are never stored here); `prefix.txt`: the challenge's copy of FILE (same path = same module name) is cut at the last listed theorem, whose proof becomes `sorry` (`tools/mkprefix.py`); missing challenge manifest = the project's, renamed |
| `tools/mkws.sh NAME [ROOT]` | trusted dependency workspace `ROOT/ws/NAME`: packages present at the same revision in `TRUSTED_WS` (default `ROOT/../local/ws` = node-local copy of the RH challenge workspace, `bench/shapes/mklocal.sh`) are symlinked, others cloned at their manifest revision; the workspace is loaded once and the project's imports from cloned packages are built OFFLINE in bwrap with the official lake of the project's release (`bench/bigprojects/tools/wsbuild.sh`) |
| `tools/run.sh NAME PRESET THREADS [ROOT] [args]` | one `bin/fastverify` run -> `ROOT/runs/NAME-PRESET[-TAG]` (`result.json`, `log/`); `FV=` package (default: `ROOT/../local/fv`), `WS=` workspace; sound runs pass `--challenge-sha256` once `tools/pin.sh` pinned the official challenge export |
| `tools/pin.sh NAME RUNDIR [ROOT]` | pin the challenge export an official run built |

Example (tables with `bench/bigprojects/tools/collect.py` / `shape.py`):
```
T=bench/codeprojects/tools; R=$SCRATCH/codeprojects          # R/../local = bench/shapes/mklocal.sh output
$T/fetch.sh cedartoml $R
$T/run.sh cedartoml reference 32 $R && $T/pin.sh cedartoml $R/runs/cedartoml-reference $R
for p in sound fast-exact; do $T/run.sh cedartoml $p 32 $R; done; TAG=b0 $T/run.sh cedartoml sound 32 $R --build B0
python3 -I bench/bigprojects/tools/collect.py $R/runs/cedartoml-*/
```
Projects with extra packages first need `tools/mkws.sh NAME $R` (arklib: VCVio/CompPoly/cslib/PolyFun/loom2 built offline;
sampcert: doc-gen4 + deps cloned; vcvio: the arklib workspace; cedar436: batteries v4.36.0).

Notes. (1) Writing the challenge for a code formalization: the statements mention the project's own definitions, so the
challenge must contain the project's definition modules and compareAt compares those definitions constant by constant;
restate the theorems in their own elaboration context (exact imports, opens, variables) or use `prefix.txt`, which keeps
the module name (private, hygienic and auxiliary names then match); a challenge that restates theorems under other imports or
inside another module name can be rejected by the official comparator itself. (2) `cedarsym` is a deliberate negative:
Cedar's symbolic-compiler theorems use `native_decide` -> REJECTED by every flow. (3) On shared hosts timings are noisy:
compare runs of the same period.
