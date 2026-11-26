# bench/rhmid — rh-mid (11,371 RH modules on top of the cached Mathlib) as a large real case

Input: `$BENCH_INPUTS/rh-mid/pristine` with `lakefile.toml` replaced by the one here: the shipped lakefile names five
library globs whose directories are absent (BuildAid, PositivityTheory, Supplements, GroundTheory.IdeleRoots,
GroundTheory.PAdicHodge) - with them the official `lake build` fails and every preset reports REJECTED (correctly).
Challenge: `$BENCH_INPUTS/rh-mid/challenge` (pinned challenge.export sha256
851372abb99f64bc445e99148506af98db19df4d15f3fac888937c6a383505b9; 5 trivial targets whose proofs pull in a
112,954-constant closure).

* `run-dev.sh OUT PRESET [ARGS]` — one run on this host into `OUT` (env `RHMID` = `$BENCH_INPUTS/rh-mid`, `WS` = the
  trusted workspace, `FASTVERIFY_BIN`, `THREADS`, `TMPSRC` = where the project copy goes; node-local install
  recommended: `bench/shapes/mklocal.sh`).
