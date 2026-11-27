# Limitations and non-goals

This page lists what Light-Prover does not do, what its verdicts do not say, and where it is slow or fragile. The trust
argument is in the [soundness model](concepts/soundness.md); measured costs are in [benchmarks.md](benchmarks.md).

## Non-goals

- **Checking that statements mean what was intended.** A sound verdict certifies proofs, not statements. In one real
  history a theorem stated with an inequality the wrong way round was "proved" by a trivial witness; the official
  comparator and Light-Prover both accepted it, correctly, because the statement was true as written. The open-lemma
  ledger (an ACCEPTED target that uses no project lemma) and `fv audit --solution-mode` can flag such cases; they cannot
  rule them out.
- **Reproducing the official toolchain's verdict in every case.** Equivalence with the official `lake comparator` is a
  test oracle. Where the official build rejects a valid proof for its own reasons (a resource limit, an official-tool
  bug), sound mode may accept it; a sound run does not run the official pipeline as well, so such a disagreement shows
  only next to a separate official run (`--preset reference`).
- **Judging anything outside the closure of the targets.** As with the official comparator, modules outside the closure,
  binder names and the bodies of the definitions listed in `definition_names` are not checked.
- **Helping to write proofs.** The tools judge proofs; interactive Lean tools (goals, hover, tactics) help write them.
- **Redistributing the Riemann Hypothesis proof.** Its author published it without a license; the benchmarks describe
  how to obtain it.

## What a verdict does not tell you

- **CONDITIONAL is not a proof.** It reduces the targets to an explicit list of open lemmas; those lemmas may be false or
  vacuous (an open lemma `False` implies every target). An open lemma inside a target statement's closure cannot be
  judged conditionally; the answer is REJECTED with the path named.
- **A verdict is about the export that was judged, not automatically about a source tree.** ACCEPTED means that export
  proves the challenge's statements with the permitted axioms; it does not say which sources produced the export. When
  you supply an export (export-in), the verdict is about that file. When Light-Prover builds the project (sources-in),
  the export comes from that build; if the build reuses an untrusted cache, a stale or substituted cache entry can make
  the export differ from the sources (it must still be a valid proof to be ACCEPTED). For a verdict about exactly this
  source tree, build from pristine sources without a cache, or check that the export is byte-identical to the one the
  official toolchain produces from the same sources.
- **Definition holes before Lean 4.37.** By default a definition listed in `definition_names` is a hole even if the
  challenge gives it a body, as in the official 4.36 comparator; pass `--require-sorried-holes` to refuse such
  challenges. With the 4.37 judge selected explicitly, the 4.37 rule applies to such a challenge as well (REJECTED where
  the official 4.36 comparator accepts); judge challenges before 4.37 with the default pins
  ([options](reference/options.md#sorried-definition-holes-cs-cn)).
- **An old-format challenge export can give REJECTED instead of no verdict.** A challenge export made with the target
  list of comparators before 4.36 (theorems, axioms and a few `Nat` / `String` constants only) lacks kernel primitives the
  4.36 judge needs; Light-Prover then answers REJECTED ("Const not found in challenge") where no verdict would be
  correct. Seen on Equational Theories; with a challenge export carrying the 4.36 target list the same proof is ACCEPTED.
- **No verdict is a failure.** DECLINED and ERROR must count as failures in rewards and CI gates: hostile code can steer a
  run to no verdict, and every resource limit ends in no verdict.
- **Advisors are advisory.** The statement audit is measured only on a small held-out set (0 of 23 false alarms, 17 of
  22 flawed statements caught, but only 3 of 8 real historical statement bugs before a proof existed; experimental).
  Duplicate lookup finds identical kernel statements only, not generalizations or instances.

## Assurance

- **Not externally audited.** Every trusted component is reviewed, gated and argued in writing, but no external expert
  review has taken place yet.
- **Known kernel defects of v4.36.0, also caught by the official-kernel leg.** The default judge's Lean leg runs the
  official v4.36.0 kernel, which lacks the upstream fixes for Lean issues #16489 (loose bound variables in inductive types,
  fixed in the 4.37 kernel), #15100 and #15101. The replay driver adds two veto checks in front of and
  after the kernel (`fastverify/check/sound/README.md`): crafted exports of these kinds are rejected by the
  official-kernel leg alone in the default, incremental, notary, warm and ultra-low-memory judges, and still by the
  mandatory second kernel.
- **The second kernel affects availability.** `gruszka` declines a few valid corner cases, which gives a false reject or
  no verdict; it can never cause an acceptance. Known case: the packed export format `gruszka` reads does not carry a
  `let`'s non-dependent flag (`nondep`), so when a nested inductive occurrence equals an earlier one, its parameters
  contain a `let`, and the export has at least one `"nondep": true` let, `gruszka` declines (no verdict) instead of
  risking a merge Lean does not make. The official exporters write `false` everywhere, so their output is not affected;
  carrying the flag through the packed format is planned for the next rebuild.
- **Known open: the 4.37 judge rejects a valid official 4.37 eta proof.** A valid Lean 4.37.0-rc1 proof that relies on
  4.37's structure eta for partially applied constructors (Lean #15373; also the iota / structure-eta cases of #15371),
  accepted by the official 4.37 comparator, is REJECTED (exit 1) by the 4.37 judge (`check/sound/pins-437.env`): its
  second kernel `gruszka` follows Lean 4.36's eta rules. This is a false reject (availability), never an acceptance.
- **The opt-in extra veto kernels affect availability.** `con-leche` treats theorem bodies as opaque, so it rejects valid
  proofs whose kernel check unfolds a theorem body - also output of the official toolchain: a six-line file (a
  `decide +kernel` that reduces `Acc.rec` on a theorem proof; kernel evaluation of well-founded recursion has the same
  shape) is accepted by the official kernel, `gruszka` and `nanoda` and rejected by `con-leche`. It also rejects exports
  whose declarations are out of dependency order, and declines custom axioms ("not decided", no effect). Measured: 2 of
  the 237 valid tests of the adversarial corpus, none of the arena suite, the Mathlib differential or the two Riemann
  Hypothesis exports. This is why it is off by default; the REJECTED reason names the remedy (`--skip-kernel con-leche` on `check-sound.sh`,
  `--skip-extra-kernel con-leche` on `bin/fastverify`).
  With several workers `con-leche` can also keep running without end after it found an invalid declaration (a later
  declaration that uses it loops; seen on a crafted ill-typed test: 4 of 60 runs at 4 jobs, every run at 64 jobs). That is
  "not decided", never an acceptance, but an optional `con-leche` named with `--kernel` / `--extra-kernel` is waited for
  without a time limit unless check-sound.sh gets `--kernel-grace S` (or `--timeout`): pass a grace when enabling it
  there. bin/fastverify passes neither, so `--extra-kernel con-leche` is unbounded.
  `nanoda` reads fewer export variants (duplicate entries, non-continuous back-references: "not decided") and takes
  36-38 minutes and 70 GiB at 64 threads on the Riemann Hypothesis exports. An enabled extra kernel shares the CPUs with
  the judge (+10 to +16 % wall on the Riemann Hypothesis exports at 216 threads). A declaration name with embedded
  newlines could forge a line in an extra kernel's log; the effect is a lost veto or a false reject, never an acceptance.
- **Not covered by the evidence:** a mechanized proof of the replay driver, mutants at the scale of the Riemann
  Hypothesis proof beyond four classes, the official-kernel leg on non-x86 hosts, and hostile challenges or comparator
  configurations (those are trusted inputs).
- **Open availability issues.** A declaration name with two embedded newlines can turn one export's REJECTED into
  DECLINED. A name component with thousands of digits (for example 5,000) gives no verdict (DECLINED, with an internal
  error message) instead of the official outcome. The notary judge declines exports whose hint field exceeds 2^32.
- **The second kernel alone misses some ill-formed nested inductive types.** `gruszka` by itself accepts some ill-formed
  nested inductives; the official-kernel leg rejects them, so the judge's verdict is not affected, but `gruszka` is not a
  complete check on its own.
- **The ultra-low-memory judge gives no verdict above its closure budget.** v0.1 ships `pleanchecker_lowmem` d27c3bdd. When
  its targeted retry does not converge, one pass over the complete reachable-theorem closure of the failing declarations
  decides; a closure above `PCHK_LOWMEM_CLOSURE_MAX` theorems (default 400,000) gives no verdict (DECLINED), and a run over
  the memory cap is killed (no verdict). The variable is parsed leniently: a non-numeric, signed or empty value means
  400,000 and a very large value switches the budget off (the judge runs under `env -i`, so it is not set in normal runs).
- **The second kernel gives no verdict on some very large computations.** `gruszka` declines when one of its worker
  tables is full or runs out of memory (it reached 639 GB and 811 GB resident on two openai/math challenges with 46
  workers). Seen on the openai/math challenges NearSquareRootMultiplication (also with one worker), ExactFourier and
  Sunflower, and on SHA-256 gadget theorems of the clean (zk circuits) project; the official comparator accepts them.
  The judges retry once with one worker after a worker-table decline; a manual rerun with fewer threads can also help
  (MultitapeWeakETH was ACCEPTED in a rerun with `--threads 2`).
- **The second kernel is slower than the official kernel on large `BitVec` terms.** On LNSym the judge takes 51.5 s
  against 7.8 s for the official comparator: `gruszka` spends about 40 s on one declaration, while the Lean kernel leg needs 1.4 s for all
  declarations.

## Platform

- Linux x86-64 with glibc only (no musl, as for the official Lean releases); bubblewrap 0.5 or later.
- macOS on Apple silicon: the build, export and check stage scripts only, without the orchestrator and the services,
  tested on macOS 27.2 only. What is missing there and what differs from Linux: [macos.md](macos.md).
- Large Lean 4.37 module-system projects need a high `vm.max_map_count`: importing the main module of a large one can
  create several hundred thousand memory mappings, against a Linux default of 65,530; set at least 524,288.
- The repository ships sources and recipes, no binaries and no build environment; rebuilds need the compilers, sysroots,
  images and other inputs named in each component's provenance recipe. Byte-identical rebuilds of the judge's
  PGO kernel legs (`pleanchecker`, `pleanchecker_incr`) need a 4.1 GB build bundle (conda clang 18.1.8, dependency
  headers, the v4.36.0 sources at a canonical path, the PGO profile) that is NOT shipped; the PGO profile of the
  experimental 4.37 toolchain `lean4-v4.37.0-rc1-pgo-portable` (2d9ed39c…) was lost, so that toolchain cannot be rebuilt
  byte-for-byte. `gruszka` (`portable-v3`), the notary's `gruszka-r7` and `gruszka-lowmem` DO rebuild byte-for-byte
  (`fastverify/tools/reproduce/portable-gruszka.sh`: digest-pinned manylinux2014 image, offline Rust 1.97.1, canonical
  paths), as do the release-library Lean legs (`ccmp`, the notary's `ccmp-notary` / `pleanchecker-notary`). Some build
  recipes assume the original build environment and need adapting
  ([getting-started.md](getting-started.md#4-build-the-pinned-fast-components)).
- The patched Lean 4.33.1 build toolchains of `--preset sound` (`toolchain-T1`: `7586a50cec` = v4.33.1 plus 36
  performance patches, its PGO build `d5e35ef223`, and the zygote toolchain on top of it) are pinned by whole-tree
  manifests in `fastverify/toolchains/unofficial/`, but their patch series is not published; only the zygote diff
  relative to the patched base (`fastverify/toolchains/s01zy-recipe/s01zy.patch`) is. The headline build time of
  `--preset sound` on the Riemann Hypothesis proof therefore cannot be reproduced from this repository alone. Verdicts
  do not depend on these toolchains: they are untrusted producers, and without them the fast build uses the official
  toolchain or falls back to the exact build.
- Lean releases up to v4.25 are not supported (refused). The full fast path exists for 4.33.1; 4.36.0 and 4.37.0-rc1 have the transformed fast build B3 of the sound presets
  and a native exporter but no zygote; other admitted releases use the official build and exporter.

## Performance

- **Small proofs can be slower than the official flow.** Every run pays fixed costs (preflight, sandboxes, integrity
  checks) of about 20 s on single-file challenges that import Mathlib, so one small proof or a failed attempt can take
  longer than the official flow. `sound-auto` uses the official build for very small
  projects; for many attempts use `fvserve`.
- **Speed-ups are not uniform.** Projects outside the fast-build shapes (a `lakefile.lean` anywhere, a non-ASCII character anywhere in
  `lakefile.toml`, comments included, Lake plugins, a module claimed by several libraries and the other cases of
  [which build runs](reference/options.md#which-build-runs)) or on a Lean release other than 4.33.1, 4.36.0 and
  4.37.0-rc1 use the official build stage, and the build of many real projects is bound by its critical path; the gain then comes from the export and the judge only, and some projects are slower end to end
  (LNSym 0.6x-0.7x, Aeneas 1.0x; [benchmarks](benchmarks.md#other-projects)). Full overlap of check and build gives no gain outside the Riemann Hypothesis proof, and more
  threads are slower for small exports.
- **`--preset sound` needs a large node for Mathlib projects.** Its zygote holds Mathlib in memory: large Mathlib
  workloads give no verdict under 16 GB (small projects can), and its zygote items are dropped below a 96 GB budget.
- **Large proofs need CPU time even when memory fits.** The Riemann Hypothesis proof needs about 92,000-125,000 CPU-s of
  kernel replay: about 1.6 to 2.2 hours on 16 threads at full use, more in practice.
- **The guarantees cost time.** A conditional check of a nonempty frontier is two judge runs (one when the first is
  cached; an empty frontier is one ordinary check); the low-memory judges are slower when
  memory is not the constraint; the notary judge took 556.6 s against 503.9 s for the sound judge on the Riemann Hypothesis export (192 threads, one
  run each; the notary run alongside another run on the server, the sound run alone).
- **The low-memory comparison reads name indices more strictly than the official reader.** An export that refers to one
  constant through two different name indices (the official exporters never write such files) is rejected by the
  low-memory judges with `Constant not found`. A constant declared twice under two name indices can pass their
  comparison (it keeps the last record) and is then rejected by their two kernel legs, where the official reader rejects
  it at once (`Duplicate declaration`). Neither case can produce an ACCEPTED; the duplicate case has a regression test.
- **Lean 4.37 at very large scale** depends on the second kernel staying mandatory (the hide list: see the 4.37.0-rc1 kernel
  replay item below); the official build of a very large 4.37 project can need several hundred GB of disk.

## Official tools this depends on

Observations with the official Lean 4.37.0-rc1 binaries on large module-system projects; they matter when you compare
with the official flow.

- **The Lean 4.37.0-rc1 kernel replay of a module-system export can be extremely slow.** An export carries the bodies of
  Mathlib definitions marked `@[no_expose]` (for example `Complex.exp` and the real and complex arithmetic instances),
  which the build-time kernel never unfolds, so the official `leanchecker` and the Lean kernel leg of the unmodified
  `lake comparator` can spend a very long time on single declarations. Light-Prover's 4.37 judge replays in an
  encapsulated environment driven by an untrusted hide list (a wrong list costs time, not soundness) and keeps the second
  kernel mandatory.
- **`nanoda` can reject a valid proof by stack overflow.** The bundled `nanoda` 0.4.31 gives each worker a 32 MiB stack and
  `lake comparator` does not set a larger one, so a valid proof with a long kernel computation can be reported as
  rejected. When the sound judge runs `nanoda` as an extra kernel it uses 1 GiB stacks, and a stack overflow counts as
  "not decided".
- **`lake comparator` reports a sandbox failure as a rejection.** On a host without `/run/user` every kernel's bubblewrap
  sandbox fails to start and the comparator prints "kernel rejected the solution" for each of them. Light-Prover's C0
  supplies an empty `/run/user` in an outer sandbox, and a sandbox start-up failure or an exit 1 without a report is
  ERROR there, never REJECTED.
- **The official exporter needs much more memory than the export size on very large module-system projects**, because it
  maps the `.olean` pages of the whole environment; Light-Prover's native exporter writes the same bytes in parallel.

## Services

- `schemas/fv_schema.py` `validate_v1` is a structural check: it does not refuse every malformed v1 envelope (for example
  a non-number or negative timing, an extra top-level key, a non-string `verdict_basis`); verdicts are not affected.
- The HTTP API has no per-user client field: under `fvserve --fair` all its users count as one client.
- `batchverify` and `fvserve` give no verdict (not REJECTED) when the ownership export of an attempt that does not declare
  the requested theorem ends in an exporter panic; the official comparator rejects such an attempt. No verdict counts as
  not accepted.
- The CI gate is experimental: a `--frontier` check that declines leaves the sound report (which may say REJECTED) in
  place; an unreadable or truncated previous report silently disables the comparison with the previous run; its separate frontier command takes the judge release from the challenge's `lean-toolchain` (the judge's own
  gate refuses a mismatch); with the standalone `tools/ci-action/fv-ci.sh`, the frontier report's verdict is not
  cross-checked against the process status beyond its exit field, and an input refusal removes earlier reports but
  publishes no fresh error envelope.
- The notary preset is experimental: in v0.1 it supports exactly one challenge-configured kernel and refuses other
  configurations (use `--preset reference` for those).
  Every kernel the challenge's comparator config declares is mandatory, so the notary gives no verdict (DECLINED) when such
  a kernel crashes on the export; for example the bundled nanoda panics on one valid control export of the kernel-defect tests.
- In v0.1 `fvwork` and the incremental entry points take the cold sound path: each request costs about a cold run of the
  project. The incremental machinery (`--experimental-incremental`) is experimental, not claimed sound and never counted.
- A reconnecting slow HTTP client still competes for slots.
- Not in v0.1: the warm delta judge. fvwork, fvserve and incr-reverify refuse it;
  the standalone `check/warm/fvcheckd.py` is research code, is not sound in its current form, and is not used by any entry point.
- Theorem inference of the HTTP API (`--experimental-theorem-inference`) is EXPERIMENTAL: it is not reward-safe against
  adversarial multi-theorem submissions, and Mathlib-style notation, attributes outside a short allow-list, an
  `instance` next to the theorem and namespaced or private theorems give NO-VERDICT. Send an explicit `theorem`.
- A running service keeps the code it started with; check `fvserve.py stats` for `stale` and restart after an update.
- Fork-server children may write only to their own output directory, so an honest attempt that writes elsewhere during
  elaboration is REJECTED there although the official `lean` path would accept it.
