# On Lean 4.37 the untrusted B3 item `linter-off` changes auxiliary-lemma numbering (repro, heavy)

Not a soundness issue (the trusted check replays whatever is exported); it matters for EXPORT IDENTITY with the official
build and for statement-drift tools that diff exports of differently configured builds.

`repro.sh [MODULE]` recompiles one module of a complete, built tree of the community RH main (Lean 4.37.0-rc1;
`FV_RHC_TREE` = the tree, e.g. a cache-restored tree, used read-only; `FV_RHC_WS` = the Mathlib 31ce06e workspace) with
the official 4.37 `lean` in bwrap, in four variants, and lists the `_simp_1_N` / `_proof_N` names of the private olean
part. Measured twice (on a copy of a cache-restored tree, then on that tree directly) for
`Formalism/.../InertiaGaloisSymmetry/KcDiffSmulMem` (one of the 4 modules that differ between the cache-built and the
from-sources export):

| variant | aux names |
|---|---|
| no options (= the official/cache build) | `_simp_1_1 _simp_1_3 _simp_1_4` |
| `-Ddebug.skipKernelTC=true` | `_simp_1_1 _simp_1_3 _simp_1_4` |
| `-Dlinter.all=false` | `_simp_1_1 _simp_1_2 _simp_1_3` |
| both | `_simp_1_1 _simp_1_2 _simp_1_3` |

Mechanism (from the module's warnings): linters such as `linter.unnecessarySimpa` ("`simp` already closes the goal") and
`linter.unusedSimpArgs` elaborate `simp` calls again; those runs allocate `_simp_1_N` numbers that the final proof does not use,
so with linters off the proof's own auxiliary lemma gets a lower number. Consequence: compare exports of the SAME build
configuration for drift, or treat private auxiliary renumbering as noise; drop `linter-off` when an official-identical export
is required.
