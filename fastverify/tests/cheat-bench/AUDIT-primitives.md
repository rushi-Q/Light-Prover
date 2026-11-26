### Audit: every constant the Lean 4.36 kernel treats specially is inside the comparator's compared closure

Why it matters: a solution may contain its OWN declarations under any name it likes (a `prelude` module does not even
import `Init`). If the kernel gave special meaning to a name that the comparison never looks at, a solution could redefine
that constant and obtain a kernel-valid "proof" of a false statement (e.g. a `Nat.add` that ignores its second argument,
while the kernel's GMP acceleration still computes `2 + 2 = 4`). The official comparator guards against this with the
primitive list of `Lake/CLI/Check.lean` (`primitiveTargets`, "List from `git grep new_persistent_expr_const
src/kernel/`") plus the target statements and the permitted axioms' statements, whose constants are all compared
transitively (`Lake/Check/Compare.lean`: `runForUsedConsts`, inductives with their constructors). Our trusted `ccmp` is that
judge code. The audit checks the list against the kernel sources the sound mode actually runs (v4.36.0, tag 611c117b).

Method: `git grep` of `src/kernel/` at v4.36.0 for every hard-coded constant name (`name{...}`, `mk_constant(...)`,
`new_persistent_expr_const(...)`):

| kernel name (v4.36.0 `src/kernel`) | kernel use | compared by the comparator because |
|---|---|---|
| `Nat.add` `Nat.sub` `Nat.mul` `Nat.pow` `Nat.gcd` `Nat.div` `Nat.mod` `Nat.beq` `Nat.ble` `Nat.land` `Nat.lor` `Nat.xor` `Nat.shiftLeft` `Nat.shiftRight` | GMP literal reduction (`type_checker.cpp`) | each is in `primitiveTargets` |
| `Nat.zero`, `Nat.succ` | literal <-> constructor conversion | constructors of `Nat` (primitive; `runForUsedConsts` adds `ctors`) |
| `Bool.true` (and `Bool.false` via `mk_bool_false`) | results of `Nat.beq`/`Nat.ble` reduction; eager `decide` path | `Bool` occurs in the type of the primitive `Nat.beq`; its constructors follow |
| `String.ofList`, `Char`, `Char.ofNat`, `List.nil`, `List.cons` | string literal expansion (`inductive.cpp`) | `String.ofList`, `Char`, `Char.ofNat`, `List` are primitives (`List` brings `nil`/`cons`) |
| `eagerReduce` | eager reduction mode | primitive |
| `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` | built-in quotient (types created by the kernel itself in `add_quot`, not taken from the export) | compared when `Quot.sound` is permitted (`builtinTargets`); otherwise the kernel's own fixed types apply |
| `Eq` | `add_quot` checks its shape (1 universe, 1 constructor, exact types of `Eq` and `Eq.refl`) | in the statement of `propext` / `Quot.sound` when permitted; the shape check pins it otherwise |

Result: **no gap** — every specially treated name of the 4.36 kernel is compared (or, for the quotient, defined by the
kernel itself). `optParam`, `autoParam`, `outParam`, `semiOutParam`, `String`, `String.mk` are compared too (elaborator
annotations / literal types). Source-level attempts that rely on redefining core constants are also blocked one step
earlier in practice: the export targets include every primitive, and `Nat.gcd` / `Nat.land` / ... live outside
`Init.Prelude`, so a `prelude` solution that does not import `Init.Core` cannot even be exported against the official
target list (case F22 of the cheat benchmark: export fails on the missing primitives; a solution that does import them
gets the real `Iff`, `Nonempty`, `Eq`). Residual: this is an audit of names, not a proof; a future kernel version that adds
a special constant must add it to the list (the Lake comment says so).
