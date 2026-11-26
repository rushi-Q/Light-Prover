<p align="center">
  <img src="logo.svg" alt="" width="96">
</p>

<h1 align="center">Gruszka</h1>

<p align="center">
  A Lean 4 kernel in Rust: normalization by evaluation, fed on Susz.
</p>

<p align="center">
  <a href="#try-it">Try it</a> ·
  <a href="#checking-part-of-a-file">Part of a file</a> ·
  <a href="#what-it-checks">What it checks</a> ·
  <a href="#a-few-things-inside">A few things inside</a> ·
  <a href="#how-fast">How fast</a> ·
  <a href="docs/architecture.md">Inside the kernel</a>
</p>

---

Gruszka checks Lean proofs with its own implementation of Lean's type
theory. Given an export of a Lean environment, it checks every declaration,
including universe levels, reduction and recursors, without involving Lean
itself in the check.

Its only input format is [Susz](https://github.com/jasisz/susz), a binary
form of [lean4export](https://github.com/leanprover/lean4export) files. The
`susz` tool converts an export in a couple of seconds, so the kernel never
needs to parse text.

Like the fastest kernels, Gruszka decides definitional equality by
**normalization by evaluation (NbE)**. Its knowledge of which work to skip
comes from [Pestka](https://github.com/jasisz/pestka), a substitution-based
kernel that paid for that knowledge first: Pestka's knowledge, NbE's speed,
and Susz for food.

It checks **all of mathlib** (702,040 declarations) in under nine seconds on
eight cores, in under 3 GB. [How fast →](#how-fast)

*Gruszka* is Polish for a pear. Dried pears are a classic *susz*, a pear has
*pestki* (pips) inside, and pear trees get rust. The Polish phrase *gruszki
na wierzbie*, pears on a willow, means a promise of the impossible, which is
what checking all of mathlib in ten seconds once sounded like.

## Try it

You need a Rust toolchain. From a checkout of this repository:

```sh
cargo build --release
cargo install susz
susz pack --no-index MyModule.ndjson MyModule.susz
target/release/gruszka MyModule.susz
```

The last line contains the verdict, for example:

```text
accepted
```

Gruszka uses all cores by default, but you can pass a worker count as the
second argument, for example `MyModule.susz 1`. The verdict is the same for
any number of workers: each declaration sees only the environment before it
in the file, and Gruszka reports the first failure in file order.

If you need an export first, Lean and `lean4export` produce the file;
neither is needed when checking it.

`--progress` (or `--progress=SECS`) prints a line on stderr every 10 (or
SECS) seconds: declarations checked out of those to check, the process's
memory, and the three longest-running declarations in flight with their
elapsed time. It is off by default.

```text
progress: 30 s, 605928/1710994 declarations (35.4%), 4 workers busy, 8.93 GB; longest: WeierstrassCurve.ellipticNet_four (3.7 s), ...
```

## Checking part of a file

`--only` checks named declarations in a Susz file rather than the whole
file, exactly as Pestka's `--only` does. It requires the INDEX section,
which `susz pack` writes unless given `--no-index`; Gruszka declines a file
without it, or an ndjson file, with a message explaining why.

```sh
gruszka --only Nat.add_comm mathlib.susz                # one declaration
gruszka --only Nat.add_comm,List.map_id mathlib.susz    # several
gruszka --only 'Finset.*' mathlib.susz                  # every name under Finset
```

Names use dots, as Lean prints them, and a component that contains only
digits is numeric. `Foo.*` asks for every name under `Foo`, but not `Foo`
itself, while a constructor or recursor name asks for its inductive block.

After finding each name in INDEX, Gruszka reads MAIN from the beginning
through the record of the last requested declaration, then stops. It
decodes proof blocks only for the targets and for theorems unfolded by a
target.

A subset check has a narrower trust boundary. As in a full check, each
target is checked against the environment of everything before it in the
file, but the earlier declarations are handled differently:

- Inductive blocks and the quotient package before the last target are
  derived and compared with the file, as in a full check, because reduction
  relies on the recursor and quotient rules they add.
- Names must be new and universe parameters distinct, as always.
- Every other declaration before the last target, an axiom, definition,
  theorem or opaque constant that was not requested, is admitted as the file
  states it: its type and value are not checked, and a theorem's proof is
  not examined.
- Unsafe and partial declarations are skipped. A target that is unsafe or
  partial is declined.

So a subset verdict holds only if the declarations admitted
unchecked are well typed. An ill-typed definition unfolded by a target
could make it pass or make a reduction run forever; only a full check can
vouch for the whole file.

| Last line | Exit code | Meaning |
| :--- | :---: | :--- |
| `checked: NAME (subset; N earlier declarations admitted unchecked)` | `0` | The targets check, given the declarations before them as stated. |
| `rejected: <declaration>: <why>` | `1` | A target fails, an inductive block or quotient before the last target fails, or the part read is malformed. |
| `declined: <why>` | `2` | A name is not found, the file has no INDEX, or Gruszka cannot judge. |
| `index invalid: <why>` | `2` | INDEX disagrees with the records; this says nothing about the file. |

With several targets, the output reads `checked: a,b (2 declarations;
subset; ...)`. A subset check never prints `accepted`.

Nothing in INDEX is trusted. Gruszka decodes the whole section with the
`susz` crate's checked reader, which checks sizes, front coding, strictly
increasing keys and that every declaration index is in range. As it reads
MAIN, Gruszka verifies for each target that the record is at the offset
given by INDEX, has the stated kind and proof block, and declares the name
that led to it. Any disagreement is `index invalid`. A name absent from
INDEX is `not found`: without reading all of MAIN, an INDEX that omits a
name is indistinguishable from a file that does not contain it.

All of mathlib, four workers, Gruszka and Pestka on the same file:

| Target | Gruszka | Pestka |
| :--- | ---: | ---: |
| `Int.neg_ediv` (early) | 0.09 s, 0.2 GB, 1.0 G | 0.27 s, 0.1 GB, 3.3 G |
| `CategoryTheory.FintypeCat.Action.isConnected_of_transitive` (middle) | 1.5 s, 1.2 GB, 16 G | 6.1 s, 2.0 GB, 51 G |
| `HenselianLocalRing.TFAE` (late) | 2.6 s, 1.8 GB, 24 G | 10.3 s, 3.3 GB, 76 G |

The figures show time, peak memory and instructions. Reading MAIN record by
record costs about twice as much per record as loading it for a full check:
for the late target, this accounts for 2.3 s of the 2.6, compared with
1.24 s to load all of MAIN in a full check.

<!-- milestone 26, data/m26 -->

## What it checks

Gruszka implements Lean's type theory, including:

- Universe polymorphism and definitional equality.
- Mutual and nested inductive types, with recursors built by Gruszka and
  compared with the export.
- Quotients, proof irrelevance, and the Nat and String literal extensions.

The last output line and the exit code give the result:

| Output | Exit code | Meaning |
| :--- | :---: | :--- |
| `accepted` | `0` | The check passed. |
| `rejected: <declaration>: <why>` | `1` | The input failed a check. |
| `declined: <why>` | `2` | The input needs something Gruszka does not support. |

Axioms remain assumptions: Gruszka checks their types, but not proofs of
them. Unsafe and partial declarations stay outside the logical environment.

**The whole file is untrusted, including the prelude.** A file can define
its own `Quot`, `Nat` or `Eq`, or state its own recursor rules. Gruszka
builds the quotient package and every recursor itself and compares
them with the file, checks the shape of the declarations used by the
built-in rules, and bounds-checks every reference it reads. Every kernel
change passes a gate of adversarial files, and Gruszka is run through a
differential fuzzer against the reference kernel: it accepts nothing the
reference kernel rejects.

## A few things inside

**Terms are never built.** Every expression is a Susz id. Environment terms
remain in columns throughout the run, while proof terms are decoded from
the file when their theorem is checked. Everything the checker creates is a
*value*: a weak-head form with closures over environments of values. There
is no term substitution, no universe instantiation into terms and no
reference counting.

**The same computation is one value.** Values, environments and spines are
hash-consed, so reaching the same computation twice yields the same id.
Equality is then often identity, and every route to a value shares its
attached caches, including its weak-head form and type.

**Values live for a session.** Until its arena fills, a worker keeps values
across many declarations so that later declarations can reuse earlier work.
It keeps only facts that hold in any later environment, stamping each one
with the declaration that produced it so that nothing travels backward in
file order. Inside one heavy declaration, a `whnf` call whose result
reaches few of the values it made gives the rest back (a *region*), so a
long kernel computation runs in bounded memory.

**What not to compute comes from Pestka.** A call walks through its
function's lambdas without creating values for them, while a `casesOn`
reduces only its major premise. Arguments in proof positions are not
compared once the preceding arguments agree, and an argument is never
evaluated if its binder body does not read it.

**Workers keep related declarations together.** Declarations are grouped by
namespace, and each worker takes a contiguous part of that order so that
related proofs meet the same session. A worker that runs out takes half of
the largest remaining part.

[Inside the kernel](docs/architecture.md) describes the data, values,
checking process and every soundness measure.

## How fast

All of mathlib (702,040 declarations), on an M2 Pro, from the Susz file,
with the PGO build:

| Workers | Time | Peak memory | Instructions |
| ---: | ---: | ---: | ---: |
| 1 | 44 s | 2.0 GB | 369 G |
| 4 | 13.6 s | 2.4 GB | 372 G |
| 8 | 8.4 s | 2.8 GB | 375 G |

The full Fermat's Last Theorem environment (1.71 M declarations), four
workers: 3 min 55 s (229 and 240 s in two runs), 11 to 12 GB, 6600 G
instructions. This is the whole FLT project with its dependencies, every
declaration in the build, not just the cone of the two final theorems.

<!-- milestone 32, PGO build (scripts/build-pgo.sh, Init at 1 worker), M2 Pro. -->

Converting the ndjson export to Susz with `susz pack` adds 1.9 s and 35 G
instructions on all twelve cores for mathlib, and 37 s for the FLT export.

On the [Lean Kernel Arena](https://arena.lean-lang.org)'s x86 runner, with
the conversion included and four workers, mathlib takes 25.7 s, 2.47 GB
and 445 G instructions.

## Working on Gruszka

```sh
cargo build --release
scripts/gates_all.sh     # small tests, adversarial vectors, --only, poisoned corpora, parity
tests/only.sh            # --only alone (packs with susz 0.1.2: SUSZ=path)
scripts/build-pgo.sh init.susz   # the PGO build: trained on Init at 1 worker
```

The numbers in [How fast](#how-fast) come from the PGO build.
`scripts/build-pgo.sh` builds an instrumented binary, checks the given file
with it, merges the profile with `llvm-profdata` and builds
`target/release/gruszka` with that profile. It needs rustup's `llvm-tools`
component, or `LLVM_PROFDATA` pointing at a matching `llvm-profdata`.

- `src/env.rs`: loading Susz, constants, known names.
- `src/level.rs`: universe levels.
- `src/tc.rs`: values, evaluation, weak-head reduction, definitional
  equality, inference, declarations.
- `src/induct.rs`: inductive groups, nested inductives, recursors.
- `src/quot.rs`: the quotient package.
- `src/main.rs`: command line (`--only` included) and the parallel driver.

## Thanks

Gruszka builds on [Pestka](https://github.com/jasisz/pestka), whose
measurements determined most of what it skips, and on Lean's reference
kernel, which it follows rule by rule. It also draws on the kernels of the
Lean Kernel Arena, including nano-lean, whose sessions and unread-argument
rule it adopted, and logos, whose value engine it was measured against.
