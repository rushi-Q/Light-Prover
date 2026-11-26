kcompare — the statement/axiom half of Lean 4.36 `lake comparator`, for use beside an external kernel
=====================================================================================================
(std-only Rust, one file src/main.rs)

WHAT IT DOES
  kcompare [-j THREADS] [-v] --challenge CHALLENGE.export --theorems A,B,.. [--axioms X,Y,..] SOLUTION.export
  exactly reproduces `verifyCompare` of Lean v4.36.0 lake/Lake/CLI/Check.lean:
    compareAt   challenge solution (theorems ++ permitted axioms) [] primitiveTargets(26 names)
    checkAxioms solution theorems [] permitted axioms          (default axioms: propext,Quot.sound,Classical.choice)
  on NDJSON exports read as LeanExport.parseStream reads them:
    * constant equality = derived BEq ConstantInfo; Expr == is Expr.eqv (structural, binder names/infos ignored,
      letE nondep compared, mdata payload dropped by the parser); levels/names structural;
    * used constants = Lake.Check.runForUsedConsts / 4.36 Expr.getUsedConstants (.const names AND .proj type names).
  It does NOT type-check: pair it with a kernel that checks every declaration of the same file (with-kernel.sh).

EXIT STATUS
  0 = the comparison passes (the official comparator's compare/axiom part would pass)
  1 = definite failure (the official comparator would reject), with the official error message
  2 = declined: the input is outside the strictly supported subset (or an internal error) — says nothing about
      the input; use the official tool. Supported subset = what lean4export writes: dense increasing indices per
      kind (names/levels from 1, expressions from 0), plain decimal integers, no unknown/duplicate/escaped keys,
      valid UTF-8, no lone surrogate escapes, natVal without leading zeros/underscores.

WRAPPER
  with-kernel.sh KCOMPARE CHALLENGE EXPORT KC_THREADS -- KERNEL_CMD...   runs both concurrently;
  exit 0 iff both accept, 1 if either rejects, else 2. Empty CHALLENGE or a corpus file (*/arena/suite/*,
  */inputs/suitex/*) -> the kernel alone (those files are kernel tests without a challenge).

VERIFICATION
  * differential fuzzing against the OFFICIAL Lake.Check.compareAt/checkAxioms (a reference harness compiled with
    the 4.36 toolchain): 6,000 structured mutants of a mini solution + 480 line-local mutants of rh-miniF: 0
    disagreements; declines are (almost all) official rejects;
  * harness cmpx corpus (14 comparator-level cases): 14/14; end-to-end cheats from Lean sources: 9/9;
  * parser: 64 parser-fidelity tests: never accepts an officially malformed file,
    never rejects an officially valid one (declines non-canonical forms);
  * --digest: structural digest of the parsed environment; equal to the digest of `susz unpack (susz pack X)` on
    whole mathlib, rh-mid, rh-miniF and 332 corpus files (the kernel's input pipeline preserves what is compared).

SPEED
  rh-mid (1.1 GB): 0.31 s on 16 threads (~2.2 CPU-s); real RH challenge closure (53,008 constants): compare 0.37 s;
  whole-mathlib parse + validation 1.7 s on 16 threads. check-mid with gruszka: 1.3 s total.

OTHER FLAGS (test aids)
  --parse-only FILE   parse/validate only;  --digest FILE   print the structural digest;
  KCOMPARE_DUMP_CLOSURE=1   list the constants compareAt compared (the constants the comparator pins).
