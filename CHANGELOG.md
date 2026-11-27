# Changelog

## Unreleased

- macOS on Apple silicon: the build stage (B0 to B3), the export stage (E0, E1) and the low-memory and
  ultra-low-memory judges run natively, as separate stage scripts ([docs/macos.md](docs/macos.md)). A sandbox profile
  that denies by default (`lib/macos/sandbox-run.py`) and a macOS backend of the resource guard stand in for
  bubblewrap, cgroups and `timeout`. The judge's four programs are built on the Mac by
  `check/sound/macos/build-judge-macos.sh` from the sources the Linux recipes use, and run only with the bytes the
  tree pins. Not on macOS: the orchestrator and the services, the standard sound judge `check-sound.sh`, the
  notary and frontier judges, `toolchain-T1`, the zygote items, `native-pkg`, the low-memory exporter.

## v0.1.0 (first release)

Light-Prover checks a Lean 4 project against a pinned challenge with the official comparator's statement and axiom
checks, the unmodified official Lean kernel sources and an independent second kernel; the build and the export are
untrusted. Measured results: [docs/benchmarks.md](docs/benchmarks.md).

### Stable

- Sound judge with the presets `sound-auto` and `sound`. Only an ACCEPTED with trust `sound`, `sound-conditional` or
  `notary` counts; DECLINED, NO-VERDICT and ERROR are no verdict.
- Both pins are required: `--comparator-sha256` wherever `--challenge-sha256` is given.
- Low-memory judge (the Riemann Hypothesis export in a 128 GB limit) and ultra-low-memory judge (64 GB, pin
  `pleanchecker_lowmem` d27c3bdd).
- Lean 4.37.0-rc1 judge, selected by `--preset sound` and `sound-auto` for 4.37.0-rc1 challenges; Lean releases
  v4.26.0-rc1 to v4.37.0-rc1 admitted by the cross-version gate (14 with shipped toolchain manifests).
- Fast build for project shapes whose module set equals Lake's; every other project gets the official `lake build` of the
  configured module ([which build runs](docs/reference/options.md#which-build-runs)). The build planner runs no project
  code, and no sandbox that runs project code can write the build logs.
- `fv verify`, `fv check`, conditional verdicts (`--modulo-frontier`, frontier run / verify), the MCP verify tools,
  `fvserve`, `batchverify` and the HTTP API with an explicit `theorem`.
- Opt-in veto kernels `con-leche` and `nanoda`; opt-in `--require-sorried-holes`.

### Experimental (may change; opt-in flags in the user guide)

- `--preset notary`; `fv watch`, `fv triage`, `fv ci` and the GitHub action; sub-challenges (`tools/subcontract/`).
- The incremental machinery (`--experimental-incremental`); without it the incremental entry points run cold. `fvwork
  init` also accepts a project that uses the official build; that state serves the cold sound path only.
- Theorem inference of the HTTP API.

### Known limitations

- The second kernel gives no verdict on some very large computations and is slower than the official kernel on large
  `BitVec` terms.
- The ultra-low-memory judge gives no verdict when the closure of the failing declarations exceeds its budget; the 4.37 judge rejects some valid structure-eta
  proofs, and its ACCEPTED rests on an argument that a Lean kernel maintainer has not yet confirmed.
- Small proofs take longer than with the official flow (about 20 s fixed cost per run); projects outside the fast-build
  shapes gain only in the export and the judge.
- Lean releases up to v4.25 are not supported.

All limitations, one paragraph each: [docs/limitations.md](docs/limitations.md).

Not in v0.1: the warm delta judge. fvwork, fvserve and incr-reverify refuse it; the standalone
`check/warm/fvcheckd.py` is research code, is not sound in its current form, and is not used by any entry point. The
legacy judge check A and the presets `fast-exact` and `default` are retired and refused.
