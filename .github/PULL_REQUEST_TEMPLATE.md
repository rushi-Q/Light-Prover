## Summary

<!-- What this change does and why. Link related issues (e.g. "Fixes #123"). -->

## Type of change

- [ ] bug fix
- [ ] new feature or option
- [ ] performance (untrusted producer: build, export, scheduling, services)
- [ ] documentation
- [ ] tests or CI only

## Tests

<!-- Commands you ran and their results (PASS/FAIL rows, RESULT lines). -->

- [ ] CI checks pass (Python byte-compile, `bash -n`, unit tests without Lean)
- [ ] the suites of the components I changed pass (e.g. `fastverify/tests/run_all.sh IDS`, component `run.sh` / `test.sh`)
- [ ] a regression test is added for a fixed bug

## Trusted components

Does this change touch a trusted component? That is anything that can turn a run into ACCEPTED or CONDITIONAL:
the trusted check and its wiring (`fastverify/check/sound/`, the judge variants in `check/lowmem/`, `check/notary/`,
`check/frontier/`), the release gate `check/xversion/`, the incremental kernel leg in `fastverify/overlap/`,
the judge sources in `sources/pchk/` (`CCmp.lean`, `ParAxioms.lean`, `FastParse.lean`, `PChk/`), the second kernel
(`sources/gruszka/` and its copies), the verdict and pin logic in `fastverify/lib/` (`decide_sound`, `decide_notary`,
toolchain and integrity verification), or any pins file (`pins*.env`, `components.template.json`, `toolchains/*.json`).

- [ ] **No**: this change only affects untrusted producers, interfaces, tools or documentation, and can at most cause
  REJECTED or no verdict.
- [ ] **Yes**: then all of the following are required before merge:
  - [ ] an independent check by a second person who is not the author
  - [ ] a written soundness argument (a new or updated soundness section in the component's README)
  - [ ] the soundness gates were run on a frozen copy of the package and their results are attached or linked:
    lean-kernel-arena, the adversarial suites (`suitex`, `cmpx`), the Mathlib differential, the RH mutants, the thread
    matrix (and the kernel-level mutation classes for kernel-level changes)
  - [ ] the official kernel sources are unchanged in every deciding leg (only compiler and link options may differ)
  - [ ] rebuilt binaries are pinned by sha256 and their provenance is recorded (`fastverify/PROVENANCE.md`)

## Checklist

- [ ] documentation and `CHANGELOG.md` updated where behaviour changes
- [ ] no secrets, personal data, host names or machine-specific paths added
- [ ] third-party code keeps its license; `NOTICE` updated if third-party code is added
