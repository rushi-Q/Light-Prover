# Security and soundness policy

Light-Prover exists to give verdicts that can be trusted. A bug that makes it accept something it must reject is
treated as a security vulnerability, even if no system is "compromised" in the usual sense.

## Reporting a vulnerability

**Do not open a public issue, pull request or discussion for a vulnerability.** Report it privately through GitHub:

1. Use GitHub's private vulnerability reporting for this repository (the **Security** tab, **Report a
   vulnerability**). This creates a private security advisory that only you and the maintainers can see.
2. If private vulnerability reporting is unavailable, use a maintainer contact listed in the repository and ask for a
   private channel, without including technical details in the first message.

Please include as much of the following as you can:

- the Light-Prover commit or release, and the command line (preset, options, pins files);
- the `result.json` of the run (at least `verdict`, `trust`, `verdict_basis`, `soundness`, `warnings`);
- a minimal reproduction: the project or the solution export, the challenge directory (`comparator.json`,
  `challenge.export` and its sha256) and, where relevant, what the official `lake comparator` answers on the same input;
- the host (Linux distribution, glibc, CPU threads, memory, bubblewrap and Python versions) if the issue depends on it;
- for a sandbox escape, which component ran the untrusted code and what it could read, write or execute.

Large inputs can be shared after the first contact. Exploit details stay in the private advisory until a fix is
published.

## What counts as a security or soundness bug

The soundness standard, the trusted base and the trust labels are described in [docs/concepts/soundness.md](docs/concepts/soundness.md)
and in section 3 of [fastverify/README.md](fastverify/README.md). Within that model, the following are vulnerabilities:

- **A false ACCEPTED**: a run with trust `sound` (`--preset sound`, `--preset sound-auto`, `--check CS`, export-in
  checks with `check/sound/check-sound.sh`), `notary`, or one of the documented judge variants (low-memory,
  ultra-low-memory, the Lean 4.37 judge) reports ACCEPTED although a target statement differs from the
  pinned challenge, a non-permitted axiom (including `sorryAx`) occurs in the closure of the targets, or a declaration
  of the export is not type-correct. This includes false accepts that need a bug in the official Lean kernel, the
  second kernel or the comparator judge code, if the combination used by Light-Prover accepts.
- **A false CONDITIONAL**: a `sound-conditional` verdict whose targets do not follow from the permitted axioms plus the
  listed open lemmas, or that omits an open lemma the targets depend on.
- **A sandbox escape of untrusted project code**: code elaborated or executed from a project, an attempt or a
  submitted export (for example in the build sandbox, the fork server of `fvserve`, or `fvwork`) that reaches the
  network, writes outside its private directories, reads hidden files, survives its run, or influences a later run.
- **Verdict tampering**: any way for untrusted input or an untrusted component to change a verdict, an exit status or
  `result.json` without the trusted check deciding it. Examples: rewriting an export after the check started reading
  it, poisoning a cache, integrity record or daemon state, bypassing the challenge pin, the pins of the trusted
  binaries or the toolchain verification, or passing a trust parameter (challenge, comparator configuration, permitted
  axioms, frontier allow-list, target theorem) through a request to `fvserve`, `fvwork`, the HTTP API, the MCP server
  or the CI action.

The following are **not** vulnerabilities; please report them as regular issues:

- false REJECTED verdicts and runs that end without a verdict (DECLINED / ERROR), including those caused by resource
  limits; these are availability bugs (a hostile project can always steer a run to no verdict);
- accepts by checks or presets that are documented as not sound: results with trust `UNSAFE` (for example
  `--preset fastest`, `--unsafe` options, or a single independent kernel deciding) and results with trust
  `exact-by-design (unofficial)` (the label of the research presets `fast-exact` and `default` when the official check
  did not decide; both presets were retired before the first release and are refused);
- a challenge that does not state the intended mathematics (statement fidelity is the challenge author's
  responsibility) and differences in code outside the closure of the targets, which the official comparator also
  ignores;
- differences between a sound-mode verdict and the official toolchain where the official toolchain fails for its own
  reasons and the proof is valid.

A false ACCEPTED with trust `official` (the unmodified official `lake comparator`, e.g. `--preset reference`) is a bug of
the official Lean toolchain: report it to the Lean developers, and tell us privately as well if you suspect that the
sound mode is affected.

If you are unsure, report privately; we will reclassify the report if needed.

## Supported versions

Light-Prover is a pre-1.0 research release. Fixes are made on the default branch and in the latest release.

| version | supported |
|---|---|
| 0.1.x (latest release and the default branch) | yes |
| earlier snapshots | no |

## Disclosure policy

- We aim to acknowledge a report within 7 days and to give a first assessment within 14 days.
- We fix the issue in private where possible, add a regression test, and publish a GitHub security advisory that names
  the affected versions, presets and options, together with the fix. Fixes to trusted components follow the independent
  checks and soundness gates in [CONTRIBUTING.md](CONTRIBUTING.md).
- We agree a disclosure date with the reporter. Unless agreed otherwise, we ask reporters to keep details private for
  up to 90 days after the report, or until a fix is released, whichever comes first.
- Issues in upstream components (the Lean 4 kernel, the official comparator, `gruszka` or other third-party software
  listed in [NOTICE](NOTICE)) are also reported to their maintainers, in coordination with the reporter.
- Reporters are credited in the advisory unless they prefer to stay anonymous.
