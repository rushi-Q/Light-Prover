# Soundness model

This page defines what an ACCEPTED verdict means, which components have to be trusted for it, and why everything else
can be optimized freely. The pipeline and the judge variants are described in [architecture.md](architecture.md); the
evidence is summarized in [benchmarks.md](../benchmarks.md#correctness-evidence).

## What is claimed

Light-Prover separates three properties:

- **Soundness** is the guarantee. If a sound-family judge reports ACCEPTED (trust `sound`, `sound-conditional` or
  `notary`, the only ACCEPTED that `fv`, the services and the CI gate count), the target statements of the pinned
  challenge are derivable from the permitted axioms. A raw `bin/fastverify` run can also print ACCEPTED with trust
  `official` (`--preset reference`) or `UNSAFE`; those carry no such guarantee.
- **Availability** (valid proofs are not rejected) is a measured rate, not a guarantee. A bug in an untrusted component
  can cost a verdict.
- **Equivalence** with the official toolchain is a test oracle. It is measured on large corpora, not claimed. Where the
  official build rejects a valid proof for its own reasons (a resource limit, a bug of an official tool), sound mode may
  accept; a sound run does not also run the official pipeline, so establishing such a disagreement needs a separate
  official run (`--preset reference`).

## What ACCEPTED means

An ACCEPTED verdict requires that trusted components establish all four conditions:

1. **Challenge.** The challenge is the official export of the clean challenge file, pinned by the verifier with
   `--challenge-sha256`, and the comparator configuration with `--comparator-sha256` (required together). Both hashes are
   checked by the judge scripts on their own private copies. The two hashes
   together are the *challenge identity*. The challenge is never elaborated or exported by anything the untrusted build
   produces. If no `challenge.export` is given, it is built and exported by the official `lake build` and the official
   exporter.
2. **Statements.** Every target statement, and every definition it mentions, is equal in solution and challenge (the
   official comparator's `compareAt`: Lean 4.36's, or 4.37.0-rc1's in the 4.37 judge), except the bodies of the
   definitions listed as holes in `definition_names`, under the hole rules of the selected comparator and the
   cross-version gate.
3. **Axioms.** Only the permitted axioms occur in the dependency closure of the targets (the official `checkAxioms`). The permitted
   axioms are at most `propext`, `Quot.sound` and `Classical.choice`: every judge script refuses (DECLINED) a
   configuration that permits anything else, and a definition hole that names a kernel primitive, a theorem target or a
   permitted axiom, comparing names in Lean's canonical form, so a configuration cannot weaken the check. Only the
   internal runs of the frontier and conditional-mode machinery pass an exact extra list (`sorryAx` or the frontier
   lemmas), and their callers report at most CONDITIONAL.
   A challenge exported by Lean 4.37.0-rc1 is held to that release's own comparator rule (a definition hole must be
   sorried) by the cross-version gate inside every judge script.
4. **Kernel.** Every safe, non-partial declaration of the solution export is accepted by the official Lean kernel (4.36;
   4.37.0-rc1 in the 4.37 judge, see the basis below) in a dependency-correct replay, as the official `Lean.Replay`
   does, **and** every declaration is accepted by an independent second kernel, which can only veto. `unsafe` and
   `partial` records are skipped by that replay, as by `Lean.Replay` and by the official `lake comparator`'s default
   kernel; an ill-typed one is caught by the second kernel (`gruszka`). In addition, every export record whose name
   occurs in the final kernel environment must equal the kernel's constant (the record checks of the replay driver, `fastverify/check/sound/README.md`).

The judge reads exactly two inputs: the pinned challenge identity and a private, immutable copy of the solution export.
How the export was produced does not matter.

### Verdicts

For the sound-family judges and `bin/fastverify` with CS or CN:

| verdict | exit | meaning |
|---|---:|---|
| `ACCEPTED` | 0 | all four conditions hold |
| `REJECTED` | 1 | a build or export failure, a statement mismatch, an illegal axiom (`sorryAx`, the compiler-trust axioms of `native_decide`, a custom axiom), or a kernel rejection |
| `NO-VERDICT` (`DECLINED` / `ERROR`) | 2 | the package refused to decide: timeout, resource limit, OOM kill, unsupported input, pin mismatch, interrupted run |
| `CONDITIONAL` | 3 | the targets follow from the permitted axioms plus an explicit list of open `sorry` lemmas (opt-in `--modulo-frontier`); never exit 0 |

Only a counted exit 0 means proved. Rewards and merge gates must count NO-VERDICT as a failure: hostile project code can
steer a run to no verdict.

`result.json` records the basis of a verdict in `trust`: `sound` (the sound judge decided), `sound-conditional` (a
CONDITIONAL of the frontier check; a closed frontier is the plain sound check), `notary` (the notary judge), `official`
(the unmodified `lake comparator` decided), and `UNSAFE` (legacy research checks, or C0 on a caller-given export or a B3
build); `exact-by-design (unofficial)` appears only in results of the retired check A. Only `sound`,
`sound-conditional` and `notary` count: the `fv` envelope gives any other ACCEPTED `accepted: false`, reward 0 and exit 2
([trust rule](../reference/result-json.md#api-envelope-result-v1)).

## The trusted base

Only components that can cause a false ACCEPTED have to be trusted.

| component | what it is | assurance |
|---|---|---|
| challenge identity | sha256 of the official `challenge.export` and of `comparator.json`, configured by the verifier | input of the argument |
| `FastParse` | the export reader of the judge (`fastverify/check/sound/src/FastParse.lean`, about 1,080 lines; `sources/pchk/` holds the earlier Check A v3 tree `d876802`) | code review, soundness gates, differential agreement with the official reader |
| `ccmp` | the official Lean 4.36 `lake comparator` judge code (`compareAt`, `checkAxioms`, in `fastverify/check/sound/src/`; 4.37 in `src-437/`) with reviewed drop-ins: concurrent parse, early stop on a rejection, axiom check on all threads | independent code review, soundness gates |
| `pleanchecker` | the `Lean.Replay` walk with every declaration checked on a worker thread (`fastverify/check/sound/src/PChk/Par.lean`; 4.37 in `src-437/PChk/Par.lean`), linked against the **unmodified official v4.36.0 kernel sources** rebuilt with PGO and ThinLTO; a priority channel for known long jobs changes the order only | independent code review, soundness gates; byte-identical rebuilds |
| `pleanchecker_incr` | the targeted overlap (opt-in `--overlap-targets FILE`; not a default): the longest kernel jobs are checked while the build runs; the final replay skips a declaration only if it and its whole closure equal what was checked | two independent reviews, soundness gates including adversarial schedules |
| `gruszka` | an independent Rust kernel (`sources/gruszka` + `fastverify/check/checkB/patches/gruszka-combined.diff`), attached through the official comparator's `external_kernels` mechanism; mandatory, veto only | conformance patches with regression tests; soundness gates; the default, low-memory and notary builds (`gruszka` v3, `gruszka-lowmem` v3, `gruszka-r7` v3) rebuild byte-for-byte with the patches (note: the pinned `gruszka-warm` of the experimental warm judge was built from unpatched `sources/gruszka`) |
| `check-sound.sh` and `decide_sound()` | the wiring: pins, private input copies, one log and exit status per leg, end-of-run re-hash, exit mapping | code reviews, unit suite (`fastverify/check/sound/test/`) |
| `check/xversion` | the Lean release admission gate; can only turn a verdict into REJECTED or no verdict | mechanical checks of each release's kernel primitives from the sources |
| extra veto kernels `con-leche`, `nanoda` | the checkers bundled with the official Lean v4.37.0-rc1 release (`con-leche --verified`, `nanoda_bin` 0.4.31), pinned by sha256 in both pins files and run by `check-sound.sh` next to the judge, each in its own sandbox; both are opt-in (`--kernel NAME`; con-leche because it rejects some valid proofs, nanoda for its cost). **Not needed for ACCEPTED**: they are consulted only after the official kernel and `gruszka` accepted, and can only turn that ACCEPTED into REJECTED (their own rejection of a declaration) or, when made mandatory with `--require-kernel`, into no verdict | the classification table in `check-sound.sh` (`--xk-classify`) with a unit suite on recorded logs (`check/sound/test/xk.sh`), soundness gates with the extra legs on, `check/sound/README.md` |

**Why the second kernel is mandatory.** Known kernel defects fixed upstream after v4.36.0 (Lean issues #16489, #15100 and
#15101) can be exploited by crafted exports. On such exports the unmodified official `lake comparator` accepts 6, and
the official-kernel leg alone accepted 7 before the replay driver's veto checks were added; these checks reject all of
them in that leg too, and the second kernel still rejects all of them, so no judge variant accepts any. The replay also
skips `unsafe` and `partial` records, as `Lean.Replay` does; an ill-typed one is rejected only by the second kernel. An
official-comparator acceptance is therefore no evidence against these classes of input.

**Basis of an ACCEPTED of the Lean 4.37 judge (encapsulated replay).** The 4.37 judge's official-kernel leg first checks
each definition, theorem, opaque or axiom in an environment in which earlier theorems and the definitions of an
untrusted hide list are axioms of the same type; if the unmodified kernel accepts there, the declaration counts as
accepted, and only a kernel error (or the per-attempt time budget) leads to the check in the full environment. Such an
ACCEPTED therefore means that the official kernel code accepted every declaration in an environment with fewer unfolding
(delta) rules than the one the official replay builds, together with an argument: typing is monotone in the set of delta
rules, so acceptance there implies validity in the full environment. The argument was checked by reading the kernel's
rule classes (proof irrelevance, eta, projections, recursor and quotient reduction, lazy delta unfolding, literal
evaluation) and not by test; a confirmation by a Lean kernel maintainer is pending. Every ACCEPTED of the 4.37 judge rests on it. The comparison leg and
the mandatory second kernel are unchanged.

**Extra veto kernels.** `check-sound.sh` computes the two-kernel verdict exactly as before. Only if it is ACCEPTED does it
consult the extra kernels it was asked to start (`--kernel NAME`; both are off by default): a kernel's own rejection of a declaration makes the
verdict REJECTED; an acceptance is recorded; everything else - an unsupported construct (`con-leche` declines custom
axioms), a format or version mismatch, a resource limit, an out-of-memory kill, a stack overflow, a signal, a timeout, a
missing binary or a failed per-run self-test - is recorded in the judge's JSON and in `result.json` as
`<kernel>: not decided (<reason>)` and leaves the verdict ACCEPTED. `--require-kernel NAME` makes a kernel mandatory:
then "not decided" means no verdict. Because ACCEPTED still needs the official kernel and `gruszka`, an extra kernel can
never cause a false ACCEPTED and never lowers an existing requirement; at worst it costs a verdict (a false REJECTED, or
no verdict when required). `con-leche` treats theorem bodies as opaque and so rejects some valid proofs, including
official-toolchain output (see limitations); that is why it is opt-in. `nanoda`'s configuration is written by the judge
with 1 GiB worker stacks: its default 32 MiB reports a valid deep proof as a stack overflow, which the judge classifies as
"not decided", never as a rejection.

### Integrity records of `sound-auto`

`sound-auto` avoids re-hashing unchanged pinned files and toolchain trees on repeated runs: after one full verification it
records a stamp of each tree (sha256 over path, device, inode, mode, size, mtime, ctime, link count and symlink target of
every entry) in a directory owned by the user with mode 0700, and later runs compare the stamp instead of re-hashing. Changing
a file through the file system changes its ctime and replacing it gives a new inode, and unprivileged code cannot set ctime
back, so an unchanged stamp means unchanged entries. Untrusted code runs in a sandbox that can neither write the records nor
change a tree. Every failure (a missing, unreadable, foreign or symlinked record, a stamp error or mismatch) falls back to the
full verification, and stamps are re-checked at the end of the run. `--no-integrity-cache` turns the records off.

## Untrusted producers

Everything outside the judge is an untrusted producer: the builds (official or fast) and every build transform, the
exporters (official, native, low-memory, delta), the frontier preparer, sub-challenge minting, the compression tools and
prover models. A fault in any of them can cause REJECTED or no verdict, never ACCEPTED, because the judge checks the
export from scratch against the pinned official challenge:

- a declaration missing from the export ends in "unknown constant" and is rejected;
- an altered statement fails `compareAt`;
- a `sorry` or an extra axiom reachable from a target fails `checkAxioms`;
- an ill-typed proof fails both kernels.

**Orchestrators and services** (`bin/fastverify`, `bin/fv`, `fvwork`, `fvserve`, the HTTP and MCP servers, the CI action,
the sub-challenge tools, the resource guard) are untrusted and bound by a request boundary. In the fixed-challenge
deployment a request carries a *solution* (source code, a patch or an export), never a *trust parameter*: the challenge,
the comparator configuration, the permitted axioms and the allowed frontier are configured on the server side and pinned.
An HTTP client selects a theorem of a problem set registered on the server (explicitly, by default); the MCP server can
also be configured to take caller-supplied challenge directories, and then requires their challenge and comparator pins.
Every failure maps to NO-VERDICT.

**Advisors** (`fv audit`, `fv triage`, `fv lookup`, `fv diff`) never
affect a verdict or an exit code.

**Sandboxing.** Project code is elaborated only inside bubblewrap, without network, with home directories hidden, an
empty environment and only a private copy of the project writable. Exporters and kernels run sandboxed as well. The
orchestrator never loads an `.olean` file produced from project code, and `bin/fastverify` runs under `env -i`, so no
environment variable of the caller can influence a verdict.

## Rules for trusted changes

- The official kernel sources are never changed in a deciding leg. Only compiler and link options may differ (PGO,
  ThinLTO, a static runtime for portability).
- Every change to a trusted component needs an independent code review, the soundness gates
  ([`fastverify/tests/sound-gates/`](../../fastverify/tests/sound-gates/)) and a written soundness argument, kept next to
  the component (the `SOUNDNESS*.md` files under [`fastverify/check/`](../../fastverify/check/) and
  [`fastverify/overlap/`](../../fastverify/overlap/)).
- The second kernel stays mandatory in every judge variant.
- Untrusted producers may be optimized freely; their only obligation is to fail closed.
- Equivalence with the official `lake comparator` is measured as a test oracle, not claimed.

## Evidence

Every change to the trusted check must pass the soundness gate set: the lean-kernel-arena suite, an adversarial kernel
corpus, comparator-level cases in two configurations, a Mathlib differential (export-in and end to end), the
Riemann Hypothesis export with four mutant classes, a thread matrix from 1 to 384 threads, kernel-level mutation classes,
adversarial schedules of the targeted overlap and a protocol attack on the incremental server. Each run of the gates names the binaries it ran on;
run records are not part of the repository (the ultra-low-memory judge ships `pleanchecker_lowmem` d27c3bdd, whose Riemann Hypothesis gate passed within 64 GB:
the honest export ACCEPTED, mutants M1-M4 REJECTED); the headline numbers,
including differential fuzzing against the official comparator, are in
[benchmarks.md](../benchmarks.md#correctness-evidence).

## What is not claimed

- That the challenge states the intended mathematics. Statement fidelity is the challenge author's responsibility;
  `fv audit` can help.
- Anything about code outside the closure of the targets. As in the official comparator, binder names and the bodies of
  the definitions listed in `definition_names` are free.
- That the second kernel is sound in general. It can only veto. The same holds for the extra veto kernels `con-leche` and
  `nanoda`: they are evidence that can remove an acceptance, not part of what an ACCEPTED rests on.
- That a CONDITIONAL verdict is a proof. Open lemmas may be false or vacuous.
- Equivalence with the official verdict, or export identity for the sound presets. Module merging changes module names,
  and its plan depends on the host, so merged exports are not comparable across machines.
- An external audit. The trusted components are reviewed and gated, but not yet externally audited.
- A confirmation of the encapsulated replay's monotonicity argument by a Lean kernel maintainer (pending; it underlies
  every ACCEPTED of the 4.37 judge).
