---
name: Bug report
about: A wrong REJECTED, a run without a verdict, a crash or another malfunction
title: "[bug] "
labels: bug
---

<!--
STOP if the bug is a false ACCEPTED (or a false CONDITIONAL) in sound or notary mode, a sandbox escape of untrusted
project code, or a way to tamper with a verdict. Do not file it here: report it privately as described in SECURITY.md.
-->

## What happened

<!-- What you ran, what you got, and what you expected instead. -->

## Command and options

```
<!-- e.g. fastverify/bin/fastverify PROJECT CHALLENGE OUT --preset sound-auto --challenge-sha256 ... --comparator-sha256 ... -->
```

## Result

- verdict and exit code:
- `result.json` fields `trust`, `verdict_basis`, `warnings` (and `autotune` for `sound-auto`):
- what the official flow (`--preset reference`) answers on the same input, if known:

<details><summary>Relevant log excerpts (OUT/log/)</summary>

```
```

</details>

## Environment

- Light-Prover commit or release:
- Lean toolchain of the project (`lean-toolchain`) and of the challenge:
- Linux distribution and glibc version:
- CPU threads and memory (and cgroup limits, if any):
- bubblewrap and Python versions:
- output of `fastverify/bin/fv doctor --project PROJECT`, if relevant:

## Reproduction

<!-- A minimal project / export and challenge, or the steps to obtain them. Remove anything you may not share. -->
