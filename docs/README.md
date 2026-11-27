# Light-Prover documentation

Light-Prover (the `fastverify/` package) verifies the configured targets of Lean 4 projects against a pinned challenge:
a counted ACCEPTED certifies them, and a run can also reject or give no verdict. The build and the export run outside
the trusted judge, so they can be optimized for time and memory.

## Guides

- [Getting started](getting-started.md) - prerequisites, building the pinned components, configuration, a first
  verification, running the tests.
- [User guide](user-guide.md) - verify a project, judge an export, conditional verdicts while proving, the
  per-repository daemon, the prover and RL attempt service with HTTP and MCP, the CI gate, choosing a configuration for
  your hardware, Lean versions.
- [Large runs](large-runs.md) - verifications of the size of the Riemann Hypothesis proof on one machine.
- [macOS](macos.md) - the build, export and check stages natively on Apple silicon: setup, what is missing, what
  differs from Linux.

## Concepts

- [Soundness model](concepts/soundness.md) - what ACCEPTED means, what is trusted and what is not, the rules every
  trusted change follows.
- [Architecture](concepts/architecture.md) - the build, export and check pipeline, how the fast path stays outside the
  trust boundary, the judge and its variants.

## Reference

- [Command line](reference/cli.md) - `bin/fastverify`, the `fv` subcommands, services, standalone judges and tools.
- [Presets and options](reference/options.md) - every preset and stage option with its trust assumption.
- [Output formats](reference/result-json.md) - `result.json`, the API envelope, SARIF and LSP diagnostics.

## Results and scope

- [Benchmarks](benchmarks.md) - headline measurements with methodology and caveats, and how to reproduce them.
- [Limitations and non-goals](limitations.md).
- [Changelog](../CHANGELOG.md).

## Package documents

- [`fastverify/PROVENANCE.md`](../fastverify/PROVENANCE.md) - origin, pinned hash and build of every component.
- [`fastverify/README.md`](../fastverify/README.md) - the package manual.
- [`fastverify/tests/README.md`](../fastverify/tests/README.md) - the regression suite.
