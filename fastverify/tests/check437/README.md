# tests/check437 — the trusted check built from the official Lean 4.37.0-rc1 sources

`run.sh [PKG]`: regression test of `check-sound.sh --pins check/sound/pins-437.env`: preflight, the self-test pair, the
10 crafted kernel/replay cases of `tests/kernel-cves`, the 4.37 toy fixtures if installed (directory
`$FIXTURES_437`), the encapsulated-replay `--hide` cases (hide list recorded, bad export still rejected, Lean
#15100-class attack rejected with the list), and the unchanged default path.

The other files are the tools behind the 4.37 evidence described in `check/sound/README.md`; the regression test does
not call them:

* derivation of the judge sources: `mk_ccmp437.py` (`check/sound/src-437/CCmp.lean` from the official 4.37
  `Lake/CLI/Check.lean`), `mk_checksound_v3.py`, `mk_pchk_budget.py`, `mk_pchk_live.py`;
* official 4.37 labels and differentials: `relabel_kernel.py`, `relabel_cmpx.py`, `run_plc.py`, `gate_cmpx437.py`,
  `gate437_big.py` (Mathlib differential, mutants, thread matrix);
* RH-scale checks and diagnostics: `mk_rh437_specs.py`, `rhgate437.sh` (honest export and mutants M1-M4),
  `tgt437-export.sh`, `tgt437-time2.sh`, `tgt437-time3.sh`, `kernelon-rebuild.sh`, `axiomize.py`, `exprefs.py`,
  `pchk-live-run.sh`, `closures-hide-test.sh`, `threekernel437.sh`, and launch wrappers (`*-launch*.sh`). Their inputs
  are read from `$FV_RH437_DIR` (default `$FV_BENCH_INPUTS/rh437`, i.e. `/scratch/bench-inputs/rh437`); the launch
  wrappers SKIP when their inputs are absent.
