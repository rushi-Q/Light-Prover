# Inside Gruszka

This document describes how the kernel is built, from its data and values
through checking, inductive groups and the soundness measures. For an
overview of Gruszka and instructions for running it, see the
[README](../README.md).

Gruszka reads [Susz](https://github.com/jasisz/susz). Mathlib's 38 million
environment terms are loaded into memory in about a second, at 13 bytes
each, while the 67 million terms inside proofs remain as bytes until their
theorem is checked.

Declarations are arranged in namespace order: they are grouped by the first
two components of their namespace, groups follow their order of first
appearance, and declarations within a group remain in file order.
`SK_ORDER=file` keeps file order throughout. Each worker starts with a
contiguous part of the chosen order and takes chunks from the front; when it
runs out, it takes the back half of the largest remaining part. The verdict
does not depend on this order (see Soundness measures).

## The idea

Terms are never built. Every expression examined by the kernel is a Susz
id: either a MAIN expression held in columns for the whole run, or an
expression from a proof block, decoded into the worker's arena at ids above
MAIN when a declaration needs it. Everything the checker creates is a
*value* in the worker's arena, represented by
weak-head forms with closures over environments of values (normalization by
evaluation). Type inference returns values as well. There is no term
substitution, no instantiation of universe parameters into terms, and no
reference counting. A worker keeps its arena for a *session* of
declarations and clears it when the session ends (see Sessions).

The ids below 2^31 past MAIN hold two overflow arenas, then two arenas per
worker (session and scratch). A declaration whose blocks do not fit its
worker's arena runs again from a new session in the overflow arenas, which
one worker holds at a time. Their size (a quarter of the ids left each, at
most 2^28) does not depend on the number of workers, so neither does the
verdict; when the workers' arenas would be smaller than 2^20 ids, fewer
workers run.

## Data

**Environment (shared, read-only).** MAIN expressions are stored in columns:
a kind byte with binder information folded in, three u32 fields (`a`, `b`,
`p`), and the exact loose-bound-variable range (u32). This range allows
closed terms to drop their environment and answers both "closed" and "uses
variable i". Names remain Susz name ids, with equality determined by value
through the reader's canonical names, so two records with the same name
denote the same constant. A u32 column maps every name id to its constant
row. Levels are interned once in a global table with canonical parameter
names, and terms store global level ids. Literals are copied out of the file
(big Nat as `BigUint`). Each declaration row contains its name, universe
parameters, type, declaring index and the kind-specific facts stated by the
file. Those facts remain untrusted until the declaration has been checked,
while proof blocks stay as `BlockRef`s.

**Worker (one per thread).** Its persistent state consists of a level
interner layered on the global table (Lean's simplifying `max`/`imax`,
normalization, equivalence, `is_geq`), interned level lists and level
substitutions, and memos keyed by level ids. These ids stay valid until the
level tables pass their bound (`SK_LVL_FLUSH`). Then the tables, every memo
keyed by them and the current session are dropped together. The block
arena, values, linked-list environments, spines, free-variable types, and
every cache keyed by value or arena ids are session state. They are cleared
together when a session ends, so a stale id cannot survive.

**Memory per worker (milestone 37).** On AWS, FLT's peak grew from 28.7 GB
at 16 workers to 73.8 GB at 192, and CFSG's from there to 190 GB at 64.
A worker's report (`SK_MEM_REPORT=1`, knobs: bytes held by group at the
worker's end) on FLT at 4 workers showed what each worker kept:

- facts about MAIN terms' variables (`uses_main`): 1.5 GB per worker, never
  bounded; now dropped past `WIDE_CAP` = 2^20 entries, as `wide_main`
  already was;
- per-constant arrays of facts about the file (unused argument positions,
  explicit binders, abbreviation and casesOn/matcher shapes): 26 bytes per
  constant and worker, one array written in full at start; now one shared
  array each (atomics; any worker that asks first computes the same
  value);
- the room each session table keeps for the next session: 16 MiB per table
  (about 35 tables, twice with the scratch arena's); now `KEEP_BYTES` =
  4 MiB (half of `SESSION_MIB`). mathlib w4 (knobs): 16 / 4 / 1 / 0.25 MiB
  give 419.5 / 419.4 / 421.5 / 434.0 G, memory equal;
- the tables kept across declarations (names, levels, closed equalities,
  the memos of MAIN terms and level substitutions): their caps were set at
  4 workers (`CAP_WORKERS`); with more workers each cap is divided by
  `workers / CAP_WORKERS` (at most 64), so all workers together keep about
  what 4 kept. Room (`KEEP_BYTES`) is not divided: re-growing tables every
  session cost +3.5% where the kept facts cost +1.4%. Simulated on mathlib
  w4 (knobs, SK_CAP_DIV): divisor 1 / 4 / 16 / 48: 419.5 / 421.3 / 427.0 /
  ~433 G; FLT w4 divisor 48: +2.7% instructions, peak 9.7 against 10.3 GB.

## Values

- `Clo { term, env, ls }`: a lambda or Pi term with its environment and its
  universe substitution `ls` (the constant whose body it came from and the
  levels it was used at). A `Clo` marked `infer` stands for *the type of*
  a lambda: a Pi whose codomain is the inferred type of the body.
- `Thunk { term, env, ls }`: an argument, evaluated on demand and memoized.
- `Neu { head, spine }`: a free variable, a constant (with its level list)
  or a stuck value, applied to a spine of arguments and projections.
- `Sort`, `Lit`.

All values are hash-consed by structure: the same term, environment and
substitution, or the same head and spine, produce the same value.
Environments and spine nodes are hash-consed as well, so reaching the same
computation twice yields the same id. Definitional equality then gets an
O(1) identity test, and per-value memos (forced thunk, `whnf`,
`whnf_core`, type) are shared. Without this sharing, two unfoldings of the
same definition produce equal but separate graphs, and comparing them can
take as long as running the definition. In Init, that was the difference
between seconds and divergence.

## Sessions

A worker keeps its arena, and every table keyed by arena ids, from one
declaration to the next for a *session* (milestone 10). Within a session a
value id always means the same computation. Its memos and every cache keyed
by ids remain facts about that value when a later declaration of the
session meets it again. A session ends, and all of this is emptied at once,
in these cases:

- its tables pass `SESSION_MIB`, 8 MiB;
- the next declaration is not strictly later in file order than the last
  one checked in the session (`d <= sess_last`), for example when namespace
  order goes back or a worker takes part of another worker's range;
- the level tables pass their bound, because values hold level ids;
- the previous declaration failed (reject, decline, cancellation or panic)
  or met a Bool or Nat constructor that was not declared yet.

A session only moves forward, so every fact used in a declaration D' was
found in D' or in an earlier declaration D of the same session. Every
constant a value of D mentions was declared before D, the environment only
grows, and a definition's value never changes, so evaluation and reduction
give the same results in D'. Check-mode inference results carry the
declaration's interned list of universe parameters in their key. Free
variables belong to the session: a binder takes the first variable of its
type that is not in scope, so two binders in scope at once never share one.

## Regions

A session's values were kept until the session ended, so a declaration
that computes a lot (a `decide` by `Eq.refl` over big tables, as in the
CFSG certificates) needed memory in proportion to its computation:
286 GB for one of them, then "a worker table is full". Milestone 36
reclaims values inside a declaration. Once the session's arena holds
2^22 values (or its big literals 64 MiB), every `whnf` that misses its
memo opens a *region*: the
lengths of the value, environment, spine and literal tables are noted,
and every write that could keep an id made inside the region past the
call is logged: a memo of an older value, an entry of a session map
(equalities, inference, used-entry ids, variable slots, names of values
and terms, ...), a slot of the spine or frame table. When the call
returns, has made at least 256 values, and its result reaches at most a
quarter of them (or it made 1 MiB of big literals), the region is rolled
back:

- the values, environments, spines and literals the result reaches are
  copied out and made again through the hash-consing tables after the
  cut; so is everything the logged memos of older values name (the
  forced value of an older thunk stays found, which keeps the sharing
  between sibling calls: a region that would lose one is kept), and,
  within a small budget, closed thunks forced in the region with their
  forced values. Past 512 MiB of big literals in the
  session, a memo naming a literal over 16 KiB is not kept (it is made
  again if asked again: CFSG's gf3 test holds 609961-bit intermediates),
  until a literal of the same content is made again after such a drop
  (milestone 43): the drop then cost the work again, and memos naming
  that content are kept from then on (CFSG's LyOm.neg_a3 forces each
  18 KB table entry about 100 times; with every force after a rollback
  multiplied again it ran past 80 minutes, now 8.5 s);
- the result, memos and thunks together may reach at most a quarter of
  what the region made, or the region is kept. The threshold of 2^22
  values is a guard against thrashing: at 2^20, Arena's reachability
  tests (BFS over lazily built lists, working sets of 1-3 M values)
  rolled back and recomputed shared work without end (123 M values
  dropped in 40 s for a declaration that makes 1.9 M);
- a logged map entry that names a dead id (one past a mark) is removed;
  one that does not stays (a fact about live values) and is logged again
  for the enclosing region;
- a logged memo field that names a dead id takes the copy of that value,
  or else what it held before the write (the log, latest first); the
  enclosing region learns the memo as it was before this one;
- `vmap` forgets the dead values by their keys, the spine and frame
  tables undo their slots in reverse order (or are rebuilt after a
  growth), the tables are cut to their marks, and the direct-mapped tables
  stamped with the generation are dropped (`cgen_bump`; sorts are now
  also interned in `vmap`, so they keep their ids).

Nothing else can name a dead id. A value, environment or spine only
points to older ids, so the only pointers from before the region into it
are the logged writes and the call's result; the callers of `whnf` hold
ids made before the call. Worker fields that hold ids across a call are
stacks balanced inside it (open binders, `let_vals`), or `kb_env`, which
keeps the region. Free variables are never cut: their indices stay
unique, so a key or name that mentions one cannot meet another variable.
Used-entry ids are counted rather than taken from the map's length, and
opaque name leaves (`infer` closures) carry a rollback epoch. A region
whose call fails is kept, and scratch declarations never open regions.

The constants (data/m36/sweep-table.txt: thresholds at x1/4, x1, x4 and
regions off, instructions and peak memory on the gate corpora, mathlib
and the CFSG slices):

- 2^22 values / 64 MiB of big literals before regions open: guards
  against thrashing a working set that fits (reachability, 1-3 M values,
  is killed at x1/4) while keeping heavy computations bounded; x1 and x4
  agree within 3% instructions everywhere (x4 costs 3x the memory on the
  probes and kSol), x1/4 is 2-3x slower on the probes and kSol. Gate
  corpora and mathlib are flat (<= 0.3%) across all four settings.
- 256 values made before a region may roll back: the bookkeeping of a
  rollback costs about as much as a few hundred values; probe300 w1:
  min 64 +56% instructions, min 1024 +27% memory, 4096 2.4x memory.
- a quarter of the made values as the most a rollback copies out: the
  copy costs about what the cut saves past that (lyLet before
  args_refuted: half and three quarters copied more than they dropped).
- 1 MiB of big literals makes a small region worth rolling back; 16 KiB
  and 512 MiB for big-literal memos (past 512 MiB of them in a session,
  a memo naming a literal over 16 KiB is not kept): gf3 at 0 / 256 / 512
  / 1024 MiB: 835 / 1005 / 1232 / 1684 MiB, 31.9 / 31.3 / 30.4 / 28.6 G
  (regions off: 4117 MiB, 18.3 G); the probes' tables (<= 2 KiB literals)
  are never affected.
- 256 objects for closed thunks kept by a rollback, 256 ticks per
  argument pair for `args_refuted` (64 also cures lyLet, 16 does not;
  the cost of the pre-pass, +0.8% on con-leche, does not depend on it).

A self-limiting threshold (raise it when rolled-back work is redone) was
tried and is not in: key-bucket stamps marked nearly every bucket
(probe300 counted 98% of dropped values as made again, as did the
thrashing reachability), and exact identities of forced thunks over older
environments matched nothing (the redone work sits under environments
made in the region). See data/m36/README.txt.

**Work done again (milestone 37).** On AWS, CFSG's slowest declarations
took 8 to 28 minutes each (p6 1660 s, hD 1187 s, rowOK49 617 s, m6c
522 s, ggA4 460 s); with regions off they take 2 to 63 seconds. The
rollbacks dropped work that later calls asked for again, or cost more
than they gave back:

- *A copy keeps its forced value.* A value the result reaches is copied
  out with its whnf memo (a thunk's forced value), following the memo
  when it names a value of the region; a region whose copies would lose
  one is kept. Before, a lazy structure handed out by a region came back
  unforced, and every later force did its work again at every
  enclosing level.
- *Redone work is pinned.* When a rollback drops the root of a closed
  region that cost at least 256 ticks (`GHOST_TICKS`, about a rollback's
  own bookkeeping), the root's content key (`mkey`: term, levels and the
  keys of its environment or spine, computed from the ids of older
  values, so a value made the same way from the same older values gets
  the same key) goes to a ghost table. A region opened later on a value
  with that key is the same work done again: its key is pinned, and a
  pinned region's root and result must survive every enclosing
  rollback (or that region is kept). p6 checks a BFS closure for each
  of 64 elements; each check's region made the BFS thunk and returned a
  Bool, so the BFS ran 64 times. The key is approximate (collisions,
  `KEY_FUEL` = 4096 nodes, then by id): it only decides what is kept.
  The ghost table holds at most 2^20 keys (`GHOST_CAP`, 16 MiB), then
  starts over; a value's shape (term or head) is checked first, so most
  region openings compute no key.
  Milestone 46: pinned at the first redo when redone work tends to be
  redone again, else at the second. A pin lives for the session, so
  pinning work asked for twice only holds memory: MatCert_J4Fix's row5
  made 2.9 M first redos and 0.6 M second ones (4.7 GB), LyOm 1.1 M and
  0.04 M (6.9 GB at w4). An eighth of the keys (by key bits) is always
  pinned at its second redo and counts both; the others are pinned at the
  first while second redos are at least half the first ones in that
  sample (`REDO_CUT` = 2, after 64 first redos; the worker's run, not
  the session). Ratios measured: AlphaMc_Fi23Data 0.50, p6 0.60, CosetW
  0.43, row5 0.21, LyOm 0.06. Sweep of the cut (data/m46/redo-cut-sweep.txt,
  w4): x1/2 .. x2 keep row5 at 1.6-1.8 GB; x4 (8) pins row5 at the first
  redo again (4.6 GB) and gives Fi23Data 647 G instead of 702 G. Against
  milestone 45 (every key at its first redo): row5 4.3 -> 1.6 GB and
  570 -> 406 G, LyOm w4 7.6 -> 4.1 GB, MatCert_J4Fix past 12 GB ->
  6.3 GB; Fi23Data +21% instructions, CosetW +10%, m6c +7% (and
  1.7 -> 1.3 GB), kSol +2.5%.
- *A rollback must give something back* (milestone 46). The entry
  bounds (256 values made, or 1 MiB of big literals) are applied again
  to what the rollback frees: values and literal bytes the copies do not
  reach. McertP_Ly's ly31_K proof rolled back 98 K regions that copied
  out 1109 M of the 1111 M values they made (10.29 of 10.30 TB of literal
  bytes): a chain of Nat operations, each whnf a region whose result is
  the next big literal, each level copying it again. 314 s / 2929 G ->
  9.3 s / 94 G (Pestka 7.2 s / 69 G).
- *Attempts grow geometrically.* An attempt reads the region's log and
  walks what its result reaches; a region kept after an attempt is read
  again by every enclosing attempt (quadratic in deep recursions). An
  enclosing region attempts only once it has made `REGION_GROW` = 2
  times the values of the largest region kept inside it, so each value
  is read by a logarithmic number of attempts.
- *Deletion by key.* After a growth of the spine or frame table inside a
  region, the logged slots are stale; the rollback rebuilt the whole
  table, once per open region (hD rebuilt a 130 MB spine table at each
  of thousands of rollbacks). Dead entries now leave the tables one by
  one (backward-shift deletion, which also marks slots stale for the
  open regions). Log entries whose map entry is already gone are
  dropped rather than passed up.
- *Checkpoints.* whnf's loop keeps only its current term from one step
  to the next, so once the loop has made half of what opens regions
  (2^21 values or 32 MiB of big literals) since its region opened, the
  region closes with that term as its result and opens again. A long
  tail loop (rowOK's continuation-passing code over 120100-bit numbers)
  gave nothing back before.
- *Big literals by content.* A big Nat result equal to one already in
  the session is that value (a hash of its length and a few digits,
  confirmed by comparing contents): shared thunks and memos, one copy.
  Nat operations read their operands in place instead of cloning them,
  and a long-by-short product skips zero digits.

The constants (data/m37/sweep.txt: knobs build, w1, the CFSG slices p6,
hD, m6c, rowOK49, gf3, probe300, c0f and lyLet; instructions and peak):

- `GHOST_TICKS` 64 / 256 / 1024: within 6% everywhere (m6c 87.7 / 95.5 /
  100.4 G, peak 1.98 / 1.74 / 1.64 GB); 65536 doubles p6.
- `REGION_GROW` 1 / 2 / 8 (0: off): p6 27.5 / 15.4 / 14.8 G (off 87.0),
  m6c 185 / 95.5 / 90.4 G (off 267), rowOK49 112 / 22.8 / 22.7 G (off 147);
  2 keeps rowOK49's peak 0.1 GB lower than 8.
- checkpoints after `reg_at / 8`, `/ 2`, `/ 1` values: equal within 0.5%
  (rowOK49 peak 4.27 / 4.30 / 4.36 GB); without checkpoints rowOK49 passes
  6 GB.
- `KEY_FUEL` 1024 / 4096 / 16384: equal within 0.5%.
- each mechanism off: pinning off p6 517 G (on 15.4); copies without their
  forced values p6 82.9 G, rowOK49 37.8 G; big literals unshared rowOK49
  passes 6 GB (gf3 1.22 instead of 1.56 GB, c0f -5%); the table rebuild
  instead of deletion: hD past 300 s.

Results: data/m37/README.txt.

**Loops that give back (milestone 38).** CFSG's Fi24P7.MS.a0 multiplies
42 bit-sliced 781x781 matrices over GF(3) (609961-bit numbers) and held
11.4 GB of big literals on AWS; on the laptop it passed 6 GB in a minute.
Nothing kept it on purpose: the loops ran where no region could give
anything back.

- *Late regions.* A whnf opens a region only when the session already
  wants them at its call; the 42 nested products were all entered before
  the session passed 64 MiB of literals, so every one of their loops ran
  region-less to the end. Now whnf's loop, whnf_core's loop inside it
  (recursors over a literal reduce with no delta step) and lazy delta
  open a region at their next step once the session wants regions. Each
  keeps only its current term (lazy delta: the pair; it checkpoints when
  one side is older than the region), so a region opened there is as
  sound as one opened at the call.
- *Checkpoints at their marks.* A checkpoint closed the region with the
  loop's current term as its result and opened the next one after the
  copies, so the copies lived in the enclosing context: one loop state per
  checkpoint, for good when nothing encloses the loop. The next region now
  opens at the closed one's marks, before the copies (`reg_cut` logs the
  restored memos of older values for it), so a state dies at the next
  checkpoint unless reached again. The next checkpoint waits until the
  loop made at least as many values as the copies took (big-literal bytes
  keep their plain bound: copying them is a memcpy, and waiting would hold
  twice a loop's big live state). Fi24P7-a0: 763 MB, 361 G -> 0.18 GB,
  216 G (the old copies also kept redone work out of reach).

**Deep whnfs handed up.** A lazy accumulator (`go n (xor b true)`, a fold
or a `for` loop whose state no step looks at) is a chain of thunks as long
as the loop, each one's whnf inside the next one's: a million steps
declined at the 1 GiB stack, and past ~50 K levels nested regions cost
more than linear (acc300000 and goS1-200000 past 300 s). Pestka's
DeepMajorsResumed, ported: a whnf miss nested `DEEP_WHNF` = 8192 whnfs deep
(or past half the stack, `DEEP_DIV`) returns `Stop::Deep` with the value;
the outermost whnf (`whnf_outer`) works that value out from its own
shallow stack (its deep misses handed up the same way, deepest first),
which sets its memo, then tries its own call again, which now finds it.
The frames between are unwound by `?`; the outermost puts the argument
stack, `let_vals` and the open binders back. A failed attempt's region is
rolled back with the handed-up value as its result, so what the attempt
made does not pile up (acc1000000: 4.6 -> 2.8 GB). Handing up costs a
retry of up to `DEEP_WHNF` levels; where levels are costly (CFSG's hD, a
deep tree of levels of ~84 ticks, 3.7x its work at a fixed bound) the
bound doubles, per declaration, after an attempt whose deeper half cost
`DEEP_TICKS` = 64 ticks a level (a quarter of `GHOST_TICKS`); a lazy
accumulator's levels take ~8 and keep it. Half the stack (`DEEP_DIV` =
2) is a backstop for chains whose levels are very wide; the depth bound
acts first everywhere measured.

**Deep inferences and comparisons handed up (milestone 45).** CFSG's
`CertificateChecks.KernelMisc.RuFive.RG.chars` is a `List Char` literal of
913 500 conses, and `RG.eq` states that a string literal of as many
characters is `String.ofList chars` by `Eq.refl`. Inferring the list's type
infers each tail inside its cons (infer, infer_core: ~500 B of stack a
level on arm64), and comparing the two lists compares each tail inside its
cons (defeq_app, spines: ~630 B a level): on AWS (x86, PGO, 1 GiB) the
inference passed the stack limit, the declaration was declined and the
rest of the file skipped. The same hand-up as for whnf, by stack only
(past `deep_at`, half the stack): an inference of a closed term that
misses `infer_cache` returns `Stop::DeepInfer`, a comparison of two
values without free variables that misses `eq_cache` (both outcomes are
kept) returns `Stop::DeepDefeq`, outside probes; the declaration
(`check_decl_deep`) works it out from its own shallow stack, deepest
first, and checks the declaration again, which finds it cached. Both
look at the stack only once `tick_slow` (every `TICK_STACK` ticks) found
it past `deep_at` (`deep_zone`): an outermost inference and comparison
catching them, as `whnf_outer` does, cost +1.7% / +0.5% instructions on
Init (every call went through them); the declaration-level catch +0.25%.
Scratch declarations (inductive groups, the quotient, unsafe ones) do not
hand up.
Two walks that never tick went with them: `canon_app` makes each argument
canonical inside its own call (past half the stack a closed term is left
the lazy thunk, past the limit a decline; leaving open terms lazy too
turned the deep vector lets_bad into 7 GB of thunks over environments),
and names (`nv`) walked the 913 K-element list to the budget or to half
the stack once per element compared: a value without a name is now
remembered as such (`of_val` NONE), as the field's comment always said.
RuFive (6342 declarations) is accepted at 16 MiB of stack and at the
default; m43 declined RG.chars at 256 MiB, and with only the inference
handed up `canon_app` aborted the run with a stack overflow at 64 MiB. tests/deep.sh: list_good / list_bad (1 M conses) at 4-64 MiB.

The constants and switches (data/m38/sweep.txt: knobs build, w1, CFSG
slices, the deep tests, Init and con-leche; G, s, peak MiB):

- `DEEP_WHNF` 2048 / 8192 / 32768: acc1000000 76.9 / 81.2 / 121.8 G (deep
  nesting of regions turns superlinear past ~16 K levels: 65536 took
  711 G), rowOK49 163 / 25.6 / 25.1 G (its levels hand up at 2048), hD
  24.9 / 24.4 / 22.4 G; the rest within 1%. Without hand-ups acc1000000
  declines at the stack and goS1-200000 passes 300 s.
- `DEEP_TICKS` 16 / 64 / 256: hD 24.2 / 24.4 / 72.2 G (at 256 the bound
  never doubles); the rest within 1%. Without hand-ups hD takes 19.6 G.
- `DEEP_DIV` 8 / 2: equal within 1% (the depth bound acts first).
- failed attempts kept instead of rolled back (SK_DEEP_ROLL=0): acc1000000
  64.1 G 4.62 GB (rolled back 81.2 G 2.79 GB), hD 1.15 GB (0.86).
- checkpoints opened after the copies, as in milestone 37
  (SK_REGION_CKSAME=0): Fi24P7-a0 346 G 692 MiB (216 G 189 MiB), gf3
  301 MiB (163); rowOK49 23.3 G (25.6 G: its large live state is copied
  again at each checkpoint).
- late regions off (SK_REGION_LATE=0): Fi24P7-a0 passes 6 GB, gf3 27.2 G
  1.56 GB (16.7 G 0.16 GB); only at whnf's delta steps (=1): rowOK49
  4.59 GB (4.21), the rest equal.
- Init and con-leche: equal within 0.2% across all of them.

Under the region gate (`SK_REGION_AT=1`, `SK_REGION_POISON=2`) late
regions in lazy delta checkpoint every 16 values and each rollback checks
every table: tests/adv/bad_m34_let_fold_wrong takes 47 s there (milestone
37: 1.3 s), so the region gates give vectors 300 s (`ADV_SECS`); release
builds are not affected (equal instructions).

Results: data/m38/README.txt.

**The ground machine (milestone 39).** Regions give back what a
computation made, but only at whnf calls, and only what the result does
not reach. CFSG's invol_eq, totalC and inv_get compute with arrays,
which the kernel sees as lists (`Array.push` is `List.concat`): a lazy
push chain of n elements, forced, is n^2/2 cells, and a hash-consed thunk
keeps its environment and its forced value for good, so every
intermediate list stayed reachable (20 GB at 4 workers, and on). Once the
session holds `GROUND_AT` = 2^26 values (16 times what opens regions:
regions did not keep the declaration small), closed computations go to a
call-by-need machine of its own (`src/tc/ground.rs`):

- *Where.* A whnf miss of a closed value, and a comparison of a closed
  computation headed by a constant with data (a literal or a
  constructor application) in `defeq_core` and after each step of lazy
  delta. Lazy delta would unfold the computing side until its head is a
  constructor too: the same weak head normal form.
- *What it is.* The kernel's terms (Susz ids, the session's level
  substitutions) evaluated by an environment machine with an explicit
  frame stack: no hash-consing, objects reference counted (freed without
  recursion), thunks updated in place (the environment goes once the
  value is known), environments cut to what a delayed term reads (the
  classic space leak: `f i` in `Array.ofFn`'s loop kept the accumulator,
  so every intermediate list stayed alive), and a constructor's parameters
  that were delayed terms over an environment dropped (their types,
  `PProd (motive x) ...`, kept the list a structural recursion walked).
- *Rules.* Beta, zeta, delta of visible definitions and theorems with as
  many levels as parameters, iota with the recursors' own rules (Nat and
  String literals as constructors, `Nat.zero` as 0), casesOn read
  directly (`cases_direct`), structure eta before the major is reduced
  (fields as projections, as `rec_rule`), projections of constructor
  applications, the kernel's Nat operations on literals (a Nat operation
  short of its operands is kept whole until applied). K-like recursors,
  quotients, structure eta on a stuck major and anything else the machine
  does not take apart go to the kernel (`iota`, `quot_reduce`, `whnf` on
  exported values), one step at a time.
- *Answers.* A comparison answers `true` by itself only when both sides
  reach the same constructor at equivalent levels with equal arguments
  (positions whose declared type is a proposition skipped, as in
  `spines_defeq_skip`), or equal literals; everything else (a mismatch, a
  function, a sort) goes to the kernel's `defeq` on the two weak head
  normal forms. A whnf result is exported to the kernel's values.
  Anything the machine cannot do (an erased parameter needed, an unused
  entry read, a value that asks for itself) gives the whole run back
  (`Stop::Ground`, caught where the run began): the kernel then works as
  before.
- *Budget.* Past `GROUND_AT` a run has no budget. The gate mode
  (`SK_GROUND=2`, knobs) sends every closed comparison and whnf to the
  machine; below `GROUND_AT` a run there has `GROUND_FUEL` = 2^20 steps,
  one that runs out doubles it, and the next run waits until the kernel
  has worked as many ticks (the machine has no hash-consing:
  `bad_m34_let_fold_wrong` repeats one computation exponentially often).
- *What it costs.* The machine shares a value only through the object
  that holds it; the kernel's hash-consing also shares equal work reached
  twice. Where a declaration repeats work (CFSG's Fi23Data w_wNodup:
  555 G in the kernel, past 300 s in the machine at 2^22 values) the
  kernel is faster, hence the high threshold: SuzData, whose session
reaches about 2^25.4 values, took 677 G in the machine at 2^25 against
68 G in the kernel; Fi23Data stays near 2^24.
  `SK_GROUND=0` turns the machine off.

**The ground machine, milestone 40.** What the kernel drives run by run
now shares, and three faults that gave whole runs back are gone:

- *One heap per declaration.* The machine keeps its objects from one run
  to the next (`Worker::gm`): the constants it forced, the literals, and
  every value of the kernel that a later run imports again (`pin`: a value
  imported by two runs is kept; one imported by one run only is not, so a
  push chain the kernel built is not held). CFSG's Fi23Data asked for
  `(foldl … (range (length L))) % 3` once per element, each run 24 M steps
  recomputing `L`; now 30 K. The heap names kernel ids, so it goes when a
  rollback since the last run cut the arena below the lengths at that
  run's end (`ground_cut`, noted by `reg_cut`; cuts inside a run are past
  what the run holds), when the declaration or session ends, and when it
  holds more objects than the kernel's arena has values.
- *Runs given back keep the heap.* A run that stops (`Stop::Ground`) puts
  back what every thunk being forced held (`Orig` in the update frame; the
  environment weakly: holding it during the forcing would keep what the
  evaluation lets go of). Only if an environment is already gone does the
  heap go.
- *Erased parameters.* A constructor's delayed parameters are dropped
  (M39); exporting such a value gave the run back, after all its work
  (totalC: every other run, 10-17 M steps each). The root's weak head
  normal form is now exported with the parameters of its type
  (`g_export_typed`: a well-typed `C ps fs : I qs is` has ps = qs; each
  field's type follows from the constructor's type at qs and the fields
  before it, so nested ones are rebuilt the same way). Environment entries
  `g_trim` cut (never read) export as the kernel's HOLE.
- *Indices.* A recursor's rule takes parameters, motives and minor
  premises, not the indices; M39 applied indexed families' rules to their
  indices too (`good_m40_ground_rec_indexed_closed` was rejected under
  `SK_GROUND=2`).
- *Memo of delayed terms.* A delayed term is looked up by its key when its
  forcings so far, on average, times the share of its lookups that hit
  (one hit and one miss assumed) save more than a lookup costs
  (`MEMO_COST` = 4 steps, plus one per part of the key). The key is the
  term, the level substitution and each entry the term reads: a forced
  thunk by its value, a small literal by value, a value of the kernel by
  id, an unforced delayed term by its own key while the parts last, else
  the object's address (a weak reference keeps the address taken). Equal
  keys are the same term over the same values, so the same weak head
  normal form; a hash alone never decides. The memo starts over whenever
  the machine holds more objects than the kernel's arena has values.
  totalC's loop body: 19.5 M steps a run without it, 12.6 M with it.

Tried and dropped: hash-consing every machine object while it lives
(weak tables, forced thunks keyed by their term and environment): it
found what the M39 census called repeats with the earlier copy alive, but
the walls' repeats are of copies already dead, and the lookups made the
machine 3 times slower per step; keeping dear thunks alive for it did not
help either. Structural keys for constructor applications in the memo
(lists by content) passed 5 GB in two minutes.

Regions, milestone 40: a rollback copied every big literal its result
reaches (`reach_root` cloned it, `reg_cut` made it again). A literal of the
region is now moved out of its dead slot at the cut (`Rcp::LitAt`). In
McertP_Ly's register file of 150 000-bit numbers this copying was 57% of
the time: the slice now checks in 568 s at 4.4 GB (M39: past 900 s).

`SK_REGION_POISON=1` (knobs) marks the dead ids instead of reusing them;
release-da asserts on every read of a marked value, environment or
literal, and `=2` also checks after every rollback that no table names a
dead id. The region gate (`data/m36/rgate.sh`) runs the small tests,
vectors, Init and con-leche with regions everywhere (`SK_REGION_AT=1
SK_REGION_MIN=16`) that way.

Quotient records, inductive groups, and unsafe or partial axioms,
definitions and opaque constants run in a *scratch arena*. The session's
tables are set aside, the declaration starts from empty tables, and
afterwards its tables are emptied and the session's tables come back. A
scratch declaration adds nothing to the session or to the facts kept across
declarations. An inductive check sees its own constants in stages, so a
stuck reduction found there may not hold once all of them are visible.
Unsafe and partial declarations may use constants that safe ones may not.

## Checking

**Inference** is `infer(term, env, ls, check) -> value`. A bound variable's
type is the type of its environment value. Under a binder, the checker
pushes a fresh free variable whose type is the domain (itself a value). For
an application, it whnf's the function's type to a Pi and continues with
the codomain at the argument's thunk; in check mode, it first compares the
argument's type with the domain. A lambda is checked under a fresh variable,
and its type is the lazy `infer` closure. For constants, inference checks
visibility (the declaring index must precede the current declaration, or be
part of it for inductive groups and unsafe recursion), safety and the number
of levels; in check mode, it also verifies that every universe parameter is
declared. Projections follow Lean's `infer_proj`, including the rule about
data out of propositions. They also treat a structure as a proposition when
its inductive type lives in Prop at generic parameters (Arena test
`proj-of-subst-prop`, where the instance is a Prop only through equalities
that are not transitive).

**Definitional equality** follows Lean's `is_def_eq_core`, operating on
values:

- identity, including `(term, env, ls)` identity for unforced thunks and
  closures, with both outcomes cached for the session;
- congruence of closures and thunks: the same term and substitution, with
  equal environment entries wherever the term uses them;
- quick checks: sorts by level equivalence, literals, binders (domains, then
  bodies under a shared fresh variable);
- `whnf_core` with *cheap projections* (the structure of a projection is
  only `whnf_core`'d), then proof irrelevance;
- lazy delta by definitional height: unfold the higher one, and with the
  same head and regular hints compare arguments first (failures cached).
  Milestone 36: before that left-to-right comparison, each argument pair
  is tried under a budget of 256 ticks (last argument first); one found
  different ends the shortcut, so `List.getD l 2 d =?= List.getD l' 0 d'`
  fails on the indices before `l` (a list of 111x111 matrices in CFSG's
  lyLet_mem) is evaluated. A difference found there only skips the
  shortcut: both sides are unfolded, as after any failed comparison of
  arguments;
  Nat offsets (`succ`) and literal folding run only when neither side has
  free variables, as in Lean. The free-variable test is exact, so it only
  counts environment entries the term uses;
- projections of the same field: first the structures by lazy delta, then
  their fields (Lean's lazy_delta_proj_reduction); congruence of other
  neutral terms; then full projection reduction and a retry, lambda eta,
  structure eta, string literal expansion (whnf'd, as Pestka does), and
  unit-like types.

**Conversion order, milestone 41.** CFSG's three walls (totalC, inv_get,
invol_eq) were not computations the proofs need but the reference
kernel's order of steps: each `rfl` holds after a few unfoldings of one
side, while lazy delta took the other side down to data. The official
kernel fails on the same three (totalC past 100 GB, inv_get "deep
recursion", invol_eq past 24 GB). A conversion-stack dump (knobs
`SK_DSTACK=1` with `SK_DIAG_SECS`: every defeq and whnf in progress, its
sides and age) found the first expensive pair of each:

- totalC: `List.sum [x, y] =?= x + (y + 0)` with `x` a closed count over a
  whole enumeration. `HAdd.hAdd` (an abbreviation) unfolds first to
  `Nat.add x (y + 0)`, and literal folding brings `x` to whnf; unfolding
  `List.sum` reaches `Nat.add x …` with the same `x`.
- inv_get: `co1GenInv[0]! =?= invCand 1365 twoBStrong[0]!`. `invCand` is
  higher, so it unfolds and runs its loop over `twoBStrong[0]!`; the left
  side, an entry of the array literal `#[invCand 1365 twoBStrong[0]!, …]`,
  reaches the right side's very term in a few steps.
- invol_eq: `Equiv.toFun (levT … (c / 8)) =?= Equiv.toFun (gC c)`: `levT`
  is higher and unfolds to `permOfArr` and a `decide` over all 4060
  points; `gC c` unfolds to the same `levT` application.

Three rules change the order, never the steps. Each answer `true` comes
from delta, `whnf_core`, congruence or proof irrelevance, as before; none
is refused, only delayed, so lazy delta's answers stay the reference's.

- *ProofsComparedBeforeReduced* (Pestka round 8). A side that is a
  recursor applied at least up to its major premise (no projection in its
  spine, as many levels as the recursor has parameters), whose motive ends
  in a sort that is zero at the recursor's levels, is a proof: its type is
  the motive applied, a proposition. Such a pair is compared by its two
  types (`proof_by_rec`, read from the recursor's declared type, cached
  per recursor; the level substituted per use) before `whnf_core`, whose
  K-like iota would compare the major's type with the constructor's and so
  compute it (Pestka's lev_size: a whole Schreier-Sims run). Soundness:
  proof irrelevance says two proofs of definitionally equal propositions
  are equal, and `whnf_core` keeps a value's type up to definitional
  equality, so the reference asks the same question after `whnf_core`.
  Gruszka skips proof positions of a constant's spine, so the trap shows
  only where proofs are compared position by position (a primitive
  projection's spine): `good_m41_pfirst_k` is 0.11 G without the rule,
  0.03 G with it. knobs `SK_KTRAP=1` counts K checks on a closed major
  whose type is not the constructor's syntactically, `=2` aborts at the
  first: none in invol_eq.
- *NatFoldWaits.* In lazy delta, a side `Nat.op x y` (an operation the
  kernel folds on literals) whose operands are not literals yet (neither
  the value nor its known whnf; nothing is evaluated to find out) waits:
  if the other side is the same operation, the operands are compared first
  (congruence, under CommonHeadFirst's budget) and the fold runs only if
  they are not shown equal within it; if the
  other side is a definition or a projection application that reduces, it
  takes one step (`proj_app_step`, else delta and cheap `whnf_core`) and
  the loop goes on; otherwise (a literal, a constructor, a stuck or opaque
  term, another operation) the fold runs as before. Soundness: congruence
  (`f a ≡ f b` from `a ≡ b`) and reducing a side both preserve
  definitional equality; completeness: the fold is only postponed while
  the other side unfolds, and runs once it cannot. totalC: 0.53 G, 0.05 s.
  The budget on the congruence matters: two runs of one computation on
  different inputs agree in shape down to where the inputs differ, and an
  unbounded congruence first walked the whole recursion nested (the
  coordinator's synthetic trap s2bad, `#[f 0, f 1][0]! = f 1` with
  `f i = g 19 i`: 21 G in milestone 40, 785 G with an unbounded
  congruence, declined at the stack limit without CommonHeadFirst; 21.7 G
  with the budget).
- *CommonHeadFirst.* The outermost lazy delta runs under a budget of
  `HEAD_PROBE` = 4096 ticks (the argument probes' machinery: `probe_on`,
  `Stop::Budget`). Past it, each side in turn is unfolded a step at a time
  (`head_lookahead`: a projection application reduced, else delta and cheap
  `whnf_core`) until its head is the other side's constant, and the two are
  compared by their arguments (`spines_defeq_skip`), each try under the
  same budget; if neither finds a common head with equal arguments, lazy
  delta runs again without a budget (what the first try computed stays in
  the caches). Soundness: unfolding a side and congruence; a `false` from
  the lookahead decides nothing. Cost: a declaration pays at most two
  budgets more per lazy delta that already took one. Sweep (con-leche /
  Init w1, G): off 45.72 / 22.49, 256 50.59 / 24.93, 1024 46.47 / 22.57,
  4096 45.40 / 22.47, 16384 45.47 / 22.48; the three walls pass at each.
  inv_get 0.43 G, invol_eq 2.5 G (most of it reading the slice).

Vectors (`tests/adv-base/m41.lean`, Lean 4.35 + olean-export):
good/bad_m41_natwait_sum (`[w, 1].sum = w + (1 + 0)` and `+ (2 + 0)`),
good/bad_m41_natwait_congr, good/bad_m41_headfirst (an array literal's
entry against an expensive application, the same and another argument),
good_m41_pfirst_k, good_m41_pfirst_lvl, bad_m41_pfirst_type and
bad_m41_pfirst_stuck (`Bool.rec` into `Type` with 1 and 2: not proofs);
and the coordinator's synthetic traps as {good,bad}_m41_trap_*
(`tests/adv-base/traps/`): good ones go from 7 G to 0.03 G, bad ones are
rejected at milestone 40's cost.
Mutants (data/m41/mut-*.py): every recursor a proof, the motive's sort
read without the levels, the same Nat operation equal without its
operands or by its first operand, the common head equal without its
arguments, a side that stops unfolding taken as equal: each is caught by
a bad vector (data/m41/mutants.txt).

**Reduction.** `eval` performs beta and zeta reduction and builds thunks,
looping rather than recursing in tail positions. `whnf_core` handles
projections, iota and quotients, again looping over consecutive head steps,
while `whnf` adds Nat operations on literals (GMP via `num-bigint`) and
delta. Delta unfolds definitions and theorems. Another theorem's proof block
is decoded on demand at the current end of the arena. Iota handles recursor
rules, K-like recursors (the major is replaced by the nullary constructor
when the types agree), structure eta of the major (not for propositions),
and Nat and String literal majors.

**What is not computed** follows Pestka. A call walks its function's lambdas
as (term, environment) pairs and creates a value only for the result. For a
casesOn recognized by its value, only the major premise is reduced before
the selected minor premise is applied to the fields; similarly, a
matcher-like definition over a casesOn evaluates only the major premise and
the chosen alternative. Arguments in proof positions are not compared once
the preceding arguments are equal. Before unfolding, the same applies to
arguments that the definition's body never reads. Binders take the first
variable of their type that is not in scope, allowing a binder opened again
to find its caches. Literal Nat arithmetic in whnf ignores free variables
elsewhere in the value, as Lean's whnf does.

**Names in heavy declarations.** After a declaration has created 1 M values
or performed 10 K unfoldings, inference and definitional equality are also
remembered under *names*. A name represents the substituted, unreduced term
denoted by a value or (term, environment), using an id from a hash-consed
table. The worker keeps that table across declarations until it holds 2 M
names or the level tables are dropped, while the memos keyed by names are
cleared for every declaration. Environment entries unused by the term do
not participate, and closed MAIN terms are leaves. Two values with one name
stand for the same term, so a type or equality established for one also
holds for the other. This is Pestka's identity "value = substituted term",
paid for only where it saves work.

**Declarations.** The checker handles axioms, definitions, theorems (which
require a Prop type), opaques, the quotient package (with each type compared
structurally with the one Lean builds after Eq's shape is checked), and
inductive groups.

**Inductive groups** are checked as Lean's `inductive.cpp` checks them, with
nothing in the record trusted. Gruszka first checks the parameters and
universe of every type, then its nested occurrences. Lean replaces each
`J Ds` (J an earlier inductive, Ds mentioning the group) with an auxiliary
type that copies the constructors of J's mutual group, repeating the process
until no new type appears. Gruszka never builds this auxiliary type: it *is*
the triple (J, levels, Ds), its constructors are J's at those parameters,
and every later check runs on the enlarged group in the restored form used
by the file. Constructor checks then cover the parameters, the universe of
every field, strict positivity and the return type. The resulting facts are
compared with the record's: isRec, isReflexive, numNested, the K flag, large
elimination and the recursor's universe parameters. Finally, the type of
each recursor (`I.rec`, and `I.rec_k` for the auxiliary types) is walked as a
value against the expected telescope (parameters, motives, minor premises
with fields and induction hypotheses, indices, major premise, result) and
compared structurally with the one generated by Lean's kernel (binder names
and infos aside, as `Expr.eqv`; outParam-style annotations consumed, and the
motive universe named as Lean names it). Structurally, each rule must be the
canonical one: lambdas over parameters, motives, minor premises and fields,
followed by the minor premise applied to those fields and to one recursor
call per recursive field. Nested occurrences are merged and matched as
terms, as Lean does, rather than up to definitional equality. Iota only ever
uses a fully applied rule.

**The quotient package.** The names `Quot`, `Quot.mk`, `Quot.lift` and
`Quot.ind` are reserved for the package. A constant with one of those names
that is not the corresponding quotient record causes the file to be
rejected, and each record's type is compared with the one Lean builds after
Eq's shape has been checked. The whole file, including the prelude, is
treated as hostile.

## Checking part of a file

`--only NAMES` (milestone 26) follows Pestka's subset check (Pestka's
`docs/susz.md`, decision `SubsetAdmitsUnchecked`) and produces the same
output. `main.rs` decodes all of INDEX with the susz crate's checked reader
(`susz::index::parse`), scans the name table once for the requested keys
(`Foo.*` means a longer key beginning with Foo's), and declines names that
have no matching key. The declarations belonging to those keys become the
targets. `env::load_part` then uses the reader's iterator to read MAIN one
record at a time, rather than `decode`'s visitor, which cannot stop while
retaining its state. Reading ends at the last target's record. As each
target is encountered, its INDEX entry is matched to its record: the offset
from the start of MAIN, its kind, its proof block (offset from the start of
PROOFS and length), and every requested key naming a name declared by that
record (`canon_decl`). A disagreement is `index invalid`, while a structural
error in the portion read rejects as it would in a full check. Nothing after
that portion is read, so nothing there (the trailer's counts and
the PROOFS fill included) is checked. The iterator path costs about twice as much per
record as the visitor's fast path (late mathlib target: 2.3 s to read 99% of
MAIN, against 1.24 s for a full load). A visitor that read all of MAIN and
dropped everything after the last target would be faster beyond about half
of the file, but it would also encounter and reject errors past that point,
which Pestka does not.

The driver checks only the targets and, before the last target, every safe
inductive block and quotient record. As usual, workers process them in
namespace order. Every other declaration read receives a verdict without a
check: axioms, definitions, theorems and opaque constants are admitted as
stated and counted in the `checked:` line, while unsafe and partial
declarations are skipped and not counted (an unsafe or partial target is
declined). Declarations in both groups still reject when their universe
parameters are named twice. As in a full check, the verdict is the first
failure in file order, so a bad inductive block before a target takes
precedence over the target.
An admitted theorem's block is decoded only if a target unfolds it. Facts
kept across declarations come from checked declarations and, as always, are
stamped and weakening-safe (see Soundness measures).

`tests/only.sh` (in `gates.sh`) runs Pestka's fixtures and a collection of
INDEX lies: Pestka's `indexbad.py` modes, a name sent to a later declaration,
a wrong proof block, unsorted keys, a declaration out of range, a wrong
declaration count, and front coding off by one. It also sweeps over the bad
adversarial vectors. A declaration rejected by a full check is rejected
when requested, and the file's last declaration is never `checked` past an
inductive block, quotient record or duplicate universe parameter that a
full check rejects.

## Soundness measures

- *Declared before* is enforced at every constant lookup and delta step
  (row index against the current declaration), not only for blocks (rule
  P). A forward reference in MAIN is unknown.
- Milestone 36's regions cut the arena inside a declaration only where
  no table or memo can name a cut id (see Regions); the region gate
  checks every table after every rollback.
- Caches keyed by arena ids live for one session and only move forward in
  file order (see Sessions). Caches keyed by level ids, level lists and
  level substitutions do not depend on any declaration and last until the
  level tables are dropped. A few facts keyed only by MAIN ids or by closed
  names are kept across sessions. The shared table `Shared.checked`, read
  by every worker, holds closed terms checked at ls = 0 in a safe
  declaration, kept with that declaration's level parameters and reused
  only by a declaration whose parameters include them. It also holds the
  lambda body and type codomain of each checked safe definition (milestone
  29), reused only where the declaration's type opens the same domains.
  Each worker also keeps the definitional equalities it found true between
  closed MAIN thunks or closures, and the outcomes of equalities between
  closed names. All of these
  remain valid as the environment grows (weakening). Each is stamped with
  the declaration that produced it and used only when that declaration is
  earlier than the current one (`d < cur_decl`). No fact travels backward
  in file order, whatever order a worker checks declarations in. Unknown
  constants and errors are never cached. A value lives only as long as its
  session or scratch declaration: every value and anything at an id at or
  above MAIN dies with it. `SK_POISON=1` shifts those id spaces at every
  new session and scratch declaration, so a stale id points elsewhere and
  is caught.
- Closedness is checked for every type, value, recursor type and rule. A
  loose bound variable met during evaluation is an error, not a crash.
- Reduction is total on garbage: lookups are bounds checked; a failed
  foreign block or unknown constant only stops that reduction (or declines);
  deep recursion declines at a stack budget; and panics are caught and
  declined. Once a declaration fails, workers on later declarations are
  cancelled. Regardless of the number of workers, the verdict is the
  earliest non-accepted declaration in file order.
- Where the kernel deliberately reduces less than Lean (big literals inside
  open Nat operations), it can only reject, never accept.

## Layout

- `src/env.rs`: loading Susz into columns, constants, known names.
- `src/level.rs`: universe levels.
- `src/tc.rs`: values, eval, whnf, definitional equality, inference,
  declarations.
- `src/induct.rs`: inductive groups, nested inductives, recursors.
- `src/quot.rs`: quotient package.
- `src/show.rs`: printing, for messages and traces.
- `src/main.rs`: CLI (`--only`: INDEX lookup, targets), parallel driver,
  diagnostics.
- `scripts/`: soundness gates (`gates.sh`: small tests, adversarial vectors
  at 1 and 4 workers in file and namespace order; `gates_all.sh`: every
  gate, poisoned corpora and Pestka parity in both orders), test runner, perf
  runner, measurement under the shared lock (`measure.sh`, `withlock.sh`),
  the PGO build (`build-pgo.sh`), adversarial vectors, ndjson pretty
  printer; `tests/only.sh`: subset checks.

## Why Gruszka

Dried pears are a classic susz, a pear has pits inside, and pear trees get
rust.
