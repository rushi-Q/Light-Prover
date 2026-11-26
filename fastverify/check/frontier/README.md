# Conditional verdicts (`check/frontier/`)

While a proof still contains `sorry`, the conditional check answers CONDITIONAL: every target has exactly the official
statement and follows from the permitted axioms plus an explicit list of open lemmas, and from nothing else. It runs the
[sound judge](../sound/README.md) twice and adds no trusted kernel code of its own. Used by `fv verify --modulo-frontier`,
`--preset sound --modulo-frontier` and `tools/frontier/frontier.py`.

```
check/frontier/check-frontier.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--allowed FILE] [--axioms FILE] [--pins FILE]
                                 [--hide FILE] [--threads N] [--json FILE] ...
```

Exit 0 ACCEPTED (no open lemma), 3 CONDITIONAL, 1 REJECTED, 2 no verdict. CONDITIONAL is never mapped to ACCEPTED and
its verdict string does not start with "ACCEPTED"; for rewards and merge gates it counts as "not proved".

## What it runs

Notation: C = the official challenge export, A = its permitted axioms, S = the solution export.

1. **Preparation (untrusted)**, `tools/frontier/frontier.py prepare` with the pinned fast preparer `fvfrontier-prep`
   (or its Python implementation): F = the non-target theorems of the targets' closure whose value uses `sorry` (with
   `--allowed FILE`, only listed names, matched exactly on canonical Lean names). In S' each open lemma L stays a theorem
   whose value is a fresh axiom of the same type; a `sorry` inside a target or definition becomes a fresh open lemma over
   its context. C' = C verbatim plus the statements of the frontier axioms.
2. **Check A** = the sound judge on C' against C with permitted axioms A: the minted statements leave the official
   statements unchanged.
3. **Check B** = the sound judge on S' against C' with permitted axioms A + F.
4. CONDITIONAL iff F is non-empty and both checks are ACCEPTED; ACCEPTED iff F is empty and the sound judge accepts S
   against C; a rejection of check B is REJECTED.

The script builds both configurations from the challenge's own configuration, validates F (no target, definition target,
permitted axiom or `sorryAx`; well-formed names), and passes `--pins` and `--hide` to both checks.

## Pinned binaries

<!-- PINS:BEGIN check/frontier/pins.env -->
| pin | sha256 | what it is | sources | rebuild | byte-identical rebuild |
|---|---|---|---|---|---|
| `fvfrontier_prep` | `62c43393ddb8700036fc6bb13f1c32217ca551833cb1b30d195ff737ea05e920` | untrusted frontier preparer (never decides a verdict) | `check/frontier/src` | `lake build` (official 4.36 toolchain), see below | yes |
<!-- PINS:END -->

The judge legs are those of the sound judge (`check/sound/pins.env`, or the file given with `--pins`).

Rebuild of the preparer (static, byte-identical in two directories), from the repository root:

```bash
B=$(mktemp -d); cp fastverify/check/frontier/src/*.lean fastverify/check/frontier/src/{lakefile.toml,lean-toolchain} $B/
cd $B && TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0 && env -i HOME=/tmp PATH=$TC/bin:/usr/bin:/bin lake build
sha256sum .lake/build/bin/fvfrontier-prep      # = the pin above
```

`src/FastParse.lean` is a verbatim copy of `sources/pchk/FastParse.lean` (the reader of the pinned `ccmp`).

## Why CONDITIONAL implies the claim

1. Check A runs the official `compareAt` on C' against C, so the fragment of C' reached from the targets is exactly the
   fragment of C. A forged or wrong C' is rejected there, whoever produced it.
2. Check B shows that every target and every frontier axiom of S' matches its record in C', that the targets' closure in
   S' uses only A + F, and that both kernels accept every declaration of S'.
3. `compareAt` is a structural equality that walks the challenge side, so (1) and (2) give: the targets of S' state
   exactly the official statements.
4. S' is a kernel-valid environment whose targets' closure uses only the axioms A + F. A kernel-valid environment is a
   derivation, so every official target statement is derivable from A plus the frontier statements, whose types are the
   records of C'.

How S, F, S' and C' were produced does not enter the argument; they are inputs of two unchanged trusted checks. A lemma
missing from F leaves `sorryAx` in S', and check B rejects; an unused extra name only weakens the claim. Not claimed: that
the frontier statements are true, consistent or non-vacuous, or that the frontier is minimal.

## Known limitations

A conditional check of a non-empty frontier costs two judge runs; an open lemma inside a target statement's closure
cannot be judged conditionally (REJECTED, with the path named). See
[docs/limitations.md](../../../docs/limitations.md#what-a-verdict-does-not-tell-you).

## Tests

`tools/frontier/test/run.sh` and the directories of `tests/` whose names contain `frontier`.
