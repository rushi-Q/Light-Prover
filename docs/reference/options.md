# Presets and stage options

`fastverify/bin/fastverify PROJECT CHALLENGE OUT --preset NAME` selects a combination of build, export and check options.
Explicit `--build`, `--export`, `--check` and `--unsafe` flags override the preset, subject to the parser's compatibility
rules (for example, a required extra kernel with `--modulo-frontier`, or unsafe build items without B3, are refused). This
page lists the presets and every stage option with its trust assumption. The command-line syntax is in
[cli.md](cli.md); the reasoning behind "untrusted" is in [soundness.md](../concepts/soundness.md).

Status labels: **proven** = in the package (default or opt-in), reviewed, tested and measured (stable in v0.1); **staged** =
built and tested, not on a live path; **experimental** = exploratory, research-only or UNSAFE, or labelled EXPERIMENTAL in
v0.1 (the incremental machinery, theorem inference of the HTTP API); **retiring** = kept for
compatibility, research only; **retired** = removed from the package and refused (exit 2) with a message naming the
replacement; kept on the branch `archive/checkA`.

Numbers such as `007` refer to the regression tests in `fastverify/tests/NNN-*/`: each is a known way an option can
differ from the official flow, with its reproduction.

## Presets

| preset | build | export | check | `trust` | status | use |
|---|---|---|---|---|---|---|
| `sound-auto` | B3 or B0, chosen per project and host | E1 | CS | `sound` | proven | the default of `fv`, MCP and CI; any project, any machine |
| `sound` | B3 with the items tuned on the Riemann Hypothesis proof (the targeted overlap is opt-in: `--overlap-targets FILE`) | E1 | CS | `sound` | proven | RH-scale projects on large nodes (96 GB RAM or more) |
| `notary` | B0 | E0 | CN | `notary` | EXPERIMENTAL in v0.1 (needs `--experimental`) | archival sign-off with the unmodified official kernel libraries; definite rejections only, one challenge-configured kernel in v0.1 |
| `reference` | B0 | E0 | C0 | `official` | proven | the official flow, sandboxed: the ground-truth oracle of the challenge's release (C0 runs that release's own `lake comparator` from 4.37 on, the pinned 4.36.0 comparator for earlier releases; see C0); its ACCEPTED is never counted by `fv`, the services or CI |
| `fastest` | B3 with every legacy transform | E1 | C4 + `ignore-order` | `UNSAFE` | experimental | experiments only |
| ~~`fast-exact`~~ | B2 | E1 | C1 | — | retired | use `sound` or `sound-auto` |
| ~~`default`~~ | B1 | E1 | C1, C3, then C0 | — | retired | use `sound` or `sound-auto`; the official verdict: `reference` |

The presets `fast-exact` and `default` ran the legacy judge check A (C1), retired before v0.1 together with C2; its
successor is the sound judge CS. A retired preset or check option is refused with exit 2 and a message that names the
replacement; it is never mapped to another check. Without `--preset`, `--check` is required (the build is then B1 and the
export E1 unless given): a run with neither, formerly the implicit preset `default`, is refused the same way.

`sound` and `sound-auto` share the same judge and verdict rules. They differ in the untrusted build, and `sound-auto` also
chooses the export and judge implementations (low-memory exporter and judge, the 4.37 pins), thread counts and integrity
caching. `notary` uses
the official build, which takes about 7-21 h for the Riemann Hypothesis proof; for projects of that size, judge an
existing export with `check/notary/check-notary.sh` instead.

### What `sound-auto` decides

`sound-auto` reads the project sources as text (under a second for typical projects) and records every choice and its
reason in `result.json` under `autotune`. `python3 -I fastverify/lib/autotune.py PROJECT --json` prints the plan without
running it.

| project or host feature | decision |
|---|---|
| at most 4 modules in the targets' closure (or at most 32 modules with at most 64 KiB of source), no `decide +kernel` or `decide!` | official `lake build` (B0) + native export + judge |
| modules using `to_additive` / `to_dual` | those modules keep the build-time kernel check (`skip-kernel-tc=except-translate`) |
| few modules importing all of Mathlib, a memory budget below 96 GB, or a zygote toolchain that cannot start | no zygote items |
| module-system files | no up-front import-artifact walk in the planner (`importarts-empty`) |
| any fast build | only the solution module and its import closure are built (`closure-only`) |
| memory budget (cgroup `memory.max`, or MemAvailable) | build threads capped by memory; check threads from the export size |
| estimated judge memory above the budget | the low-memory judge, when it is installed and compatible (no frontier, no required extra kernel); independently, below a 16 GB budget, the low-memory exporter |
| repeated runs on one host | integrity records: toolchains verified in full once, then by stamp (`--no-integrity-cache` disables this) |
| a challenge on Lean 4.37.0-rc1 (its `lean-toolchain`; for export-only runs the challenge export's meta line, read strictly) | the 4.37 judge and its hide list; refused before the build if that judge is not installed |
| a failed transformed build | confirmed by the exact build B1 (and the official `lake build` B0 where the B1 planner declines, e.g. outside the sound fast path on Lake 4.36 / 4.37); a transformed build alone never gives REJECTED, so rejections take one exact build longer |

## Build options

| option | what it does | trust |
|---|---|---|
| **B0** official build | the release `lake build C` of a copy of the project without `.lake`, where C is the configured module as the comparator spells it (see below), in bubblewrap: read-only `/`, home hidden, no network, `env -i` plus `PATH`, `HOME`, `LANG`; dependencies read-only from the trusted workspace; `--threads N` is passed as `LEAN_NUM_THREADS` | the official Lean and Lake binaries, verified file by file |
| **B1** Lake-planned direct scheduler | Lake's own planning code (compiled against the release's `libLake`, or reused from the verified planner cache) computes the module set, the exact `lean` arguments and options, `setup.json`, `LEAN_PATH` and default targets; a DAG scheduler then runs the official `lean` per module with exactly those arguments in B0's sandbox. Sources are re-hashed before each `lean` starts and every output is fingerprinted and re-checked at the end. Any module error fails the build (no retries); outside sound mode the failure is confirmed by B0 (`--no-confirm-build-failure` skips that) | Lake's planning code and the official `lean`; the scheduler only orders invocations |
| **B2** early release | B1, plus dependents start when all output parts of a module exist, plus critical-path priorities; the verdict still needs every `lean` exit status 0 | as B1 |
| **B3** build items | B2's rules plus the untrusted items below (`--build B3 --unsafe LIST`) | none outside sound mode (result labelled UNSAFE); in sound mode the judge decides |

B1 and B2 also decline (and fall back to B0) on module name collisions, dependencies Lake does not consider up to date,
and self-modifying sources or outputs. One residual difference: the parent process of `lean` is the scheduler, not
`lake` (`--build B0` removes it).

### Which build runs

The official comparator builds the configured module with `lake build C`, where C is its canonical spelling
(`MOD.toName.toString`: `«Main»` becomes `Main`). Lake builds whatever target that name resolves to, with all its
imports, and any failure in it fails the official build. B0 runs exactly this command; C is computed by the pinned Lean
4.36 as the comparator computes it and passed as one argument. When C is `[anonymous]` (for example `Main.`) the result is
ERROR.

The fast builds (B1, B3) run only for the two project shapes in which their module set equals Lake's:

- a root `[[lean_lib]] MOD` whose roots include MOD, with no globs, `defaultFacets` or `extraDepTargets`, and no root
  claimed by another root target; or
- a module claimed by exactly one root library, with no untrusted `[[require]]`, no executable root MOD, and no name in
  any dependency's lakefile equal to MOD or a prefix of it.

A path dependency, a `configFile` entry or a nested manifest in `lake-manifest.json`, and a `[[require]]` without a
root `lake-manifest.json` also send the project to the official build. The planner is an exact port of Lake 4.33.1, so
B1, B2 and B3 run on Lean 4.33.1; on 4.36.0 and 4.37.0-rc1 only B3 with the sound presets' `sound-fast-path` runs (B1 and B2
decline, and a confirmation build is the official B0); other releases always use B0.

Both shapes also require that MOD and every root are plain ASCII identifiers, that `./MOD` is absent or a real directory,
that the project has no `lakefile.lean` anywhere in its tree (including path dependencies), and that every character of
`lakefile.toml` is printable ASCII, TAB, or a line end (LF or CRLF), comments included: a single non-ASCII character,
even in a comment such as `fun a ↦ b`, sends the project to the official build. Its non-comment lines must also use only
plain double-quoted strings (no literal or multi-line strings, no backslash escapes), and it must not use guillemets or
set `packagesDir`. A failed fast build counts as a failed build only when a
module inside the import closure failed; any other failure is a decline. In every other case the official build B0
decides, and so does the `--confirm-reject` confirmation. A doubt therefore leads to the official build or to no verdict,
never to a verdict on a module set other than Lake's.

### Build items (`--unsafe LIST`, B3)

The sound presets use these items as untrusted producers. Outside sound mode a result that used any of them is labelled
UNSAFE, with the regression tests that show how it can break.

| item | what it does | breaks outside sound mode |
|---|---|---|
| `zygote`, `zygote-prefix` | a pre-started `lean` that has imported Mathlib once forks one child per module (prefix mode: children continue a pre-imported prefix); needs a zygote-capable toolchain | exact presets must not use it |
| `j1-saturated` | elaboration thread count tuned for a saturated machine | - |
| `merge` | importer-closed groups of modules elaborated by one `lean` each, with split fallback and unmerged retry | changes module and private names (the export differs from the official one) |
| `fast-exact` | a plugin that decides `with_unfolding_all exact` with the kernel's definitional equality instead of the elaborator's check (unrelated to the retired preset of the same name) | skips the elaborator's own check |
| `premise-off` | suppresses premise-selection metadata | - |
| `lean-path-order` | reorders `LEAN_PATH`, root library first | - |
| `sound-fast-path` | skips guards that only serve exactness (plan and dependency checks, source digests); `sound-fast-path=importarts-empty` also skips the planner's up-front import-artifact walk | no exactness evidence for the export |
| `cost-hints`, `check-tail` | per-module costs of an earlier run steer priorities and threads; modules with long kernel jobs are built first (for the targeted overlap) | - |
| `closure-only` | only the import closure of the solution module is built, as the official `lake comparator` does; a failing module outside it does not fail the build | - |
| `skip-kernel-tc` | `-Ddebug.skipKernelTC=true`: no kernel check while building; `=except-translate` keeps it for modules that mention `to_additive` / `to_dual` | 007, 017, 030, 038 |
| `linter-off` | `-Dlinter.all=false` | 022 |
| `retries` | rebuilds a failed module once | 062 |
| `native-pkg` | the trusted packages' C code compiled once and loaded with `--load-dynlib` | 015, 057 |
| `toolchain-T1` | a Lean toolchain rebuilt with performance patches, with or without PGO | 004, 014, 020, 031, 037, 040, 046, 048, 050, 052, 061 |

`--unsafe all` selects `linter-off`, `native-pkg`, `retries`, `skip-kernel-tc` and `toolchain-T1` (plus `ignore-order`
on C3 / C4); the other items are named explicitly. Combination rule: `skip-kernel-tc` is only meaningful together with a full kernel
replay of the export.

## Export options

| option | what it does | trust |
|---|---|---|
| **E0** official exporter | the official `lean4export` (for Lean 4.35 and later, the release's bundled `leanexport`) in bubblewrap with `LEAN_ABORT_ON_PANIC=1`, into a fresh regular file | the official exporter binary, pinned by sha256 |
| **E1** native exporter | a C++ re-implementation of `lean4export`'s output (`sources/lean4export-native`): parallel loading of `.olean` files, parallel interning, output in the official order, the official `.olean` and IR header checks, and an independent closure guard (every target and every referenced constant is declared) | byte-identical by design and tested differentially; untrusted in sound mode |
| E1, low-memory | a byte-identical exporter for small memory budgets, chosen by `sound-auto` | as E1 |
| `--export FILE`, `--from-export FILE` | judge a private copy of an existing export (no solution build or export; the challenge is still prepared, and built officially if only its sources are given) | `sound` when CS decides; without CS/CN the caller's export makes it `UNSAFE` (also when C0 decides) |

E1 declines and falls back to E0 wherever it cannot reproduce the official output byte for byte: paths on which the
official exporter would panic and continue, strings that are not valid UTF-8, indices beyond 32 bits, undecidable
duplicates, and other Lean versions (4.36.0 and 4.37.0-rc1 have their own native builds). The package gives E1 at most
128 threads with the export in OUT and 256 in an external export directory. `--export-dir DIR` writes the export to a
fresh directory under DIR (for example `/dev/shm`) when DIR has at least 256 GB free and is not a tmpfs under a memory
budget below 512 GB; otherwise the export goes to OUT. `--preset sound` does this by default only with a memory budget
of at least 512 GB.

## Check options

| option | what it does | trust | status |
|---|---|---|---|
| **CS** sound judge | `check/sound/check-sound.sh`: `ccmp` (official 4.36 judge code), `pleanchecker` (parallel replay through the unmodified official v4.36.0 kernel sources), `gruszka` (mandatory second kernel); `--preset sound` and `sound-auto` select the Lean 4.37.0-rc1 judge for 4.37.0-rc1 challenges, and `--pins check/sound/pins-437.env` selects it explicitly; opt-in veto-only extra kernels `con-leche` and `nanoda`, both bundled with the official Lean v4.37.0-rc1 release | the trusted base; the extra kernels can only veto | proven |
| **CF** frontier | `check/frontier/check-frontier.sh`: for a nonempty frontier, two runs of the unchanged CS (the first can come from its cache) and CONDITIONAL, exit 3; an empty frontier is one ordinary check (ACCEPTED, exit 0). Selected with `--modulo-frontier`, not with `--check` | as CS | proven, opt-in |
| **CN** notary | `check/notary/check-notary.sh`: the unmodified official 4.36 release kernel libraries plus a three-leg canonical environment SHA-256 cross-check; the independent kernels with `--notary-kernels` (subset of `gruszka,con-ron,con-leche,nanoda`; `gruszka` always runs, every selected kernel is mandatory, a `con-ron` or `con-leche` rejection alone gives DECLINED) | the unmodified release libraries and the second kernel | EXPERIMENTAL in v0.1 |
| **C0** official comparator | the unmodified `lake comparator --challenge-from-export --solution-from-export` of the challenge's release (named in the challenge export's meta line): Lean 4.36.0 → the 4.36.0 comparator; Lean 4.37.0-rc1 (and any later registered release) → that release's own comparator, never 4.36's; earlier releases (no comparator of their own) → the 4.36.0 comparator after the cross-version gate; an unknown or unregistered release → ERROR. Each kernel in bubblewrap; its own limits are part of the reference verdict; `--official-timeout SEC` turns a timeout into ERROR | the official release of the challenge (verified file by file / whole tree) | proven (reference) |
| ~~C1~~ | check A: parallel replay linked against the official 4.36 kernel libraries, official judge code, and a parallel-parsing build of nanoda | — | retired (successor: CS) |
| ~~C2~~ | C1 with a performance-patched C++ kernel (unaudited patch) | — | retired |
| C3 | two independent kernels (`gruszka`, `nano-lean`) and an independent statement comparison (`kcompare`); declines on replay-order hazards, so it declines on the Riemann Hypothesis export by design | evidence, veto only | retiring |
| C4 | one independent kernel (`gruszka`) and `kcompare` | UNSAFE | experimental |

A gate, `prechk`, runs in front of C3 and C4 (never C0, CS or CN): one streaming pass over the export that makes those
checks decline exactly where the official comparator fails for its own reasons (format limits of nanoda, parser bounds,
the official replay order). Unsafe modifier of the legacy checks: `ignore-order` (C3, C4: do not decline on replay-order
hazards). Retired with check A (refused): `--check C1`, `--check C2`, the aliases `--check fast` (= C1,C3) and
`--check both` (= C1,C3,C0), `--fast-checks`, `--fast-policy checkA` and `--unsafe nanoda-c07`.

Options of the judge in sound mode: `--pins FILE` (a `pins*.env` file in `check/sound/`), `--check-hints FILE|none`
(declarations served first; order only), `--check-hide FILE|none` (the 4.37 hide list; availability only),
`--overlap`, `--overlap-targeted`, `--overlap-targets FILE` (opt-in; overlap the official-kernel leg with the build), `--modulo-frontier [auto|FILE]`,
`--frontier-pin DIR`, `--frontier-base RESULT`, `--confirm-reject` / `--no-confirm-reject`, `--comparator-sha256 HEX`,
`--require-sorried-holes` and the extra veto kernels (all below).

### Extra veto kernels (CS)

| option | what it does |
|---|---|
| (default) | both extra kernels are off: the judge is the two-kernel judge. (`con-leche`'s default is a one-line switch in check-sound.sh, `XK_CONLECHE_DEFAULT`; with `auto` it would run whenever the judge's own memory estimate - the three legs plus about 0.85 x the export size + 2 GiB for `con-leche` - fits the budget, and otherwise be recorded as `skipped (memory)`.) |
| `--extra-kernel NAME` | enable `con-leche` or `nanoda` as a veto-only kernel (check-sound.sh `--kernel NAME`): its own rejection of a declaration turns ACCEPTED into REJECTED; anything else is recorded as "not decided" and leaves the verdict. bin/fastverify passes no `--timeout` to the judge, so an enabled kernel is waited for without a time limit. |
| `--require-kernel NAME` | make it mandatory (check-sound.sh `--require-kernel NAME`): ACCEPTED also needs its acceptance; if it cannot decide there is no verdict. Uses the normal judge, never the low-memory one (which has no extra kernels); refused with `--modulo-frontier` and with any judge that cannot run extra kernels. |
| `--skip-extra-kernel NAME` | do not run it (check-sound.sh `--skip-kernel NAME`). |

One kernel name per option. check-sound.sh also takes `--kernel-jobs N` (threads of each extra kernel, default
min(threads, 64)) and `--kernel-grace S`, which bounds every optional extra kernel to S seconds after the two kernels
accepted ("not decided (timeout)" afterwards); without it a kernel named with `--kernel` is waited for (only `--timeout`
bounds it) and a default-on kernel gets the larger of 600 s and the judge's own wall time. Pass a grace when you enable `con-leche` in
check-sound.sh: after an invalid declaration it can run without end (see [limitations](../limitations.md)). A `--require-kernel` kernel is
always waited for. The low-memory judges run the two-kernel judge only (`result.json` records it). The frontier check runs
its live sound checks with the default extra kernels (none unless the default switch is on) and does not pass
`--extra-kernel` through. The notary judge selects its kernels with `--notary-kernels`; there every selected kernel is
mandatory.
  Inside CS an enabled extra kernel can only veto; `result.json` `extra_kernels` says what each one did.

### Sorried definition holes (CS, CN)

`--require-sorried-holes` (sound, notary; judge scripts and `fvcheckd serve`; `fv verify --extra-arg=--require-sorried-holes`):
apply the official Lean 4.37 comparator rule "a challenge definition must be sorried" to challenges of every release.
Default off: for releases before 4.37 the default (Lean 4.36) judge follows the official 4.36 comparator, which accepts a
challenge definition with a body as a hole (the cross-version gate still refuses, for every release, a hole that names a
kernel primitive or lies in the dependency closure of a kernel-evaluated primitive). With the switch a challenge whose
definition hole is not `sorry` is refused (DECLINED, exit 2); `result.json` records `require_sorried_holes`. Challenges
exported by Lean 4.37 always get the rule (violation: REJECTED, as the official comparator decides).

The off-default is the 4.36 judge's semantics. With the 4.37 judge selected explicitly (`--pins check/sound/pins-437.env`,
`fv --pins 437`), its 4.37 comparator code applies the sorried-hole rule to every challenge, so a 4.36 challenge whose
hole has a body is REJECTED there even with the switch off, while the official 4.36 comparator accepts it. Use the
default pins for challenges before 4.37.

## Verdict and trust of a combination

- **CS selected** (`sound`, `sound-auto`, or `--check CS` with any build and export): `verdict` is ACCEPTED iff CS
  accepted and no other selected check rejected; `trust = "sound"` (also for an ACCEPTED with `--modulo-frontier`, an
  empty frontier), or `"sound-conditional"` for a CONDITIONAL.
- **CN selected** (`notary`): CN decides; `trust = "notary"`.
- **CS and CN selected** (`--check CS,CN`): both decisions must accept (each one's requirements, e.g. `--require-kernel`,
  hold); REJECTED if either rejects, otherwise no verdict; `trust = "sound"`. `--modulo-frontier` cannot be combined with CN.
- In sound and notary mode every EXPLICITLY selected check (e.g. `--check CS,C0`) must accept for an ACCEPTED: a selected
  check that gives no verdict (ERROR, DECLINED, not run) makes the run DECLINED; a REJECTED of any selected check rejects.
- **C0 selected** without CS or CN (`reference`, or `--check C3,C0`): the selected official comparator decides (see C0;
  `result.json` `official_comparator` names the release and the comparator toolchain); `trust = "official"`, which `fv`,
  the services and CI never count
  (`"UNSAFE"` on a caller-given export or a B3 build). While C0 still
  runs after the legacy checks, `verdict` is `PENDING`; if C0 does not finish, ERROR.
- **Legacy checks only** (`fastest`, `--check C3` or `C4`): the strongest selected check decides (C3 > C4), every other
  one can only veto (`--fast-policy primary`; `any` is weaker, `all` stronger); `trust = "UNSAFE"` with
  `unsafe_reasons`. (`exact-by-design (unofficial)` was the label of a C1 decision; retired with check A.)

A build failure confirmed by the exact build is REJECTED (the official flow fails there too). A failure of the official
exporter, a stage stopped by a signal or a resource limit (`ulimit -f` / `-t`, `--guard fsize=`), host failures and an
interrupted run are ERROR (no verdict); a verdict is written to `result.json` only once the run is final (`PENDING`
before). Only an actual stop counts: a finite but unhit limit does not turn a confirmed build failure into a no-verdict. In
sound mode a failure of the transformed build that no exact build confirmed (`--no-confirm-build-failure`) is no verdict.
Fallbacks never lower trust: in sound mode a failed or declined B3 falls back to the exact B1 (then B0), and a
declined E1 to E0; in the legacy exact presets a declined B1 or B2 falls back to B0
(`--no-build-fallback` makes it ERROR instead), a declined B3 is ERROR, and a declined E1 falls back to E0.

## `--confirm-reject`

With `skip-kernel-tc`, meta code that uses the kernel's error as control flow (for example Mathlib's `@[to_dual]`) can
write kernel-invalid declarations into otherwise successful `.olean` files; the judge then correctly rejects the export
of a valid project. Both sound presets keep the build-time kernel check for modules that mention `to_additive` or
`to_dual`, which removes the known case. `--confirm-reject` (on by default in `sound` and `sound-auto`;
`--no-confirm-reject` turns it off) is a safety net for unknown ones: a REJECTED
verdict on the export of a successful B3 build triggers one exact B1 build, a new export and all selected checks again;
the second round decides (both rounds are recorded in `confirm_reject`). It costs time only on such a rejection. If B1
declines (on Lake 4.36 / 4.37 projects the B1 planner declines outside the sound fast path) the official `lake build` B0
confirms instead; if the exact build or its export cannot complete, the run is DECLINED (no verdict) - a REJECTED of a
transformed build's export is reported only once an exact build confirms it. With `--no-confirm-reject` such a rejection
is reported unconfirmed (DECLINED). The same
holds for the notary preset with `--build B3`. Cost: because confirm-reject is on by default, a REJECTED of a sound /
sound-auto run includes one full exact rebuild (measured on formal-conjectures: 42 s without it, 547-853 s with it).

## `--comparator-sha256 HEX` (required with `--challenge-sha256`)

The challenge's identity is the pair (challenge export, comparator config). The comparator configuration decides which
statements and axioms are checked, so it is pinned like the challenge. `--challenge-sha256` pins the export;
`--comparator-sha256` pins `comparator.json`: a config with another sha256 is refused, and the trusted judge verifies its
private copy against the same value. It is required wherever `--challenge-sha256` is: a sound, sound-auto, notary or
frontier run with a given challenge export is refused (exit 2, before anything runs) without it, and also when it does
not match. `fv verify`, `fv check` and the MCP verify tools enforce the same rule; the CI action (EXPERIMENTAL in v0.1,
opt-in input `experimental: "true"`) requires both pins (inputs `challenge-sha256`, `comparator-sha256`, 64 lowercase hex
digits). The attempt service (`fvserve`, `batchverify`, the HTTP API) needs no client pin: whoever runs the server registers the
problem set, and the service pins its own copy of the configuration for the judge. `result.json` records the pin
(`inputs.comparator_config.pinned_sha256`). The challenge directory's inputs (comparator config, `challenge.export`,
`lean-toolchain`) are copied once into the run's private directory before any decision; later changes of the directory
have no effect. Identity and mode options (`--challenge-sha256`, `--comparator-sha256`, `--comparator-config`, `--preset`,
`--check`, `--pins`, `--from-export`, `--export`) may be given once (a second occurrence, also abbreviated, is a usage
error), an empty pin value is a usage error, and `--check` cannot drop the deciding check of a trusted preset (CS for
`sound` / `sound-auto`, CN for `notary`). On a Lean 4.37+ challenge the check-B checks C3 / C4 are refused, also on their
own (they use the 4.36 tree); `batchverify` judges a private copy of the problem set's challenge export and comparator
config (checked against `--challenge-sha256`), selects that export's release judge the same way, and refuses another
release's `--pins` or an unreadable release (exit 2). The UNSAFE preset `fastest` (which selects C4) and standalone C3 /
C4 runs require the challenge export's release (its meta line) to be an entry of `check/xversion/releases.json`;
otherwise they are refused (exit 2).

In sound and notary mode a `lean-toolchain` beside a given challenge export must name the export's own release (its
meta line); otherwise the run is refused.
