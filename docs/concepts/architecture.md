# Architecture

Light-Prover (the `fastverify/` package) verifies a Lean 4 project in three stages - build, export, check - and makes
the first two as fast as possible without trusting them. This page describes the pipeline, how the fast path stays
outside the trust boundary, the judge and its variants, and the services built on top. What ACCEPTED means is defined in
[soundness.md](soundness.md); every option is listed in [options.md](../reference/options.md).

## The pipeline

```
project sources + trusted dependency workspace
   -> BUILD   (.olean files)                                  untrusted
   -> EXPORT  (lean4export NDJSON of the targets' closure)    untrusted
   -> CHECK   (the judge, against the pinned official challenge export)   trusted
   -> OUT/result.json
```

| step | what happens | fail-closed rule |
|---|---|---|
| preflight | the project's `lean-toolchain` must name a supported official release; the official toolchains are verified file by file against the manifests in `fastverify/toolchains/`; every component binary is checked against its pinned sha256 and must start on the host | a required component missing, modified or not starting: refuse (exit 2); an unavailable optional fast stage falls back to its official option (refused with `--require-fast`) |
| prepare | the project is copied without its `.lake` directory; every dependency of `lake-manifest.json` is resolved from the trusted workspace (read-only); the challenge export is taken (pinned) or built officially | unknown manifest version, path dependencies, revision mismatch: refuse |
| build | the official `lake build` or a fast build (below), sandboxed | a fast build that declines falls back to an exact build; a failed fast build is confirmed by the full exact build B1 (or B0) before REJECTED; host failures such as an OOM kill or a full disk are ERROR |
| export | the official exporter or the native exporter, sandboxed, into a fresh regular file | the native exporter declines (falls back to the official one) on anything it cannot reproduce byte for byte |
| check | the judge (or a judge variant) | any check that cannot decide exits 2 |
| result | `OUT/result.json`, rewritten after every stage (a decided verdict reads `PENDING` until the run is final); after the export has been checked, every toolchain tree, pinned binary and stage script is verified again | any change during the run: ERROR |

The stages are separate executables, most with the same convention (exit 0 = accept, 1 = reject, 2 = decline or could
not run, one JSON object, `--preflight`); the frontier judge adds exit 3, and the orchestrator normalizes every stage's
result.

## Stage options

Each stage has interchangeable options; presets combine them ([options.md](../reference/options.md)).

- **Build.** B0 is the official `lake build` in a sandbox. B1 is a direct scheduler that runs the official `lean` per
  module with exactly the arguments Lake's own planning code computes, which removes Lake's per-module bookkeeping. B2
  adds early release of dependents. B3 adds untrusted build items: a pre-started `lean` that has imported Mathlib once
  and forks one child per module (the *zygote*), module merging, a PGO toolchain, skipping the build-time kernel check,
  linters off and others.
- **Export.** E0 is the official exporter (`lean4export`, or the `leanexport` bundled with Lean 4.35 and later). E1 is a
  native C++ re-implementation that loads `.olean` files and writes the official format in parallel, guarded by an
  independent closure check. A low-memory exporter produces the same bytes under tight memory budgets.
- **Check.** CS is the sound judge. CN (notary) and CF (frontier) are judge variants. C0 is the unmodified official
  `lake comparator`, used as the reference oracle. C3 and C4 are legacy research checks; the legacy judge check A (C1,
  C2) was retired before v0.1 (CS is its successor).

## How the fast path stays outside the trust boundary

The judge reads only the pinned challenge identity and a private copy of the solution export. Everything upstream of it
can therefore be replaced by faster, less conventional code, provided it fails closed. The speed-ups of the sound presets,
and why none of them can cause a false ACCEPTED:

| speed-up | stage | why it cannot cause a false ACCEPTED |
|---|---|---|
| zygote toolchain: Mathlib imported once, every module forked from that process | build | it only produces `.olean` files; a crashed child is retried with plain `lean` |
| module merging: importer-closed groups of modules elaborated by one `lean` | build | as above; failures split the group and retry unmerged |
| `fast-exact` plugin for `with_unfolding_all exact` (the kernel's definitional equality instead of the elaborator's check) | build | the judge re-checks the exported declarations with both kernels |
| skip the build-time kernel check, linters off, premise-selection metadata off, PGO toolchain, natively compiled package code, retries | build | the judge re-checks the exported declarations with both kernels; modules using `to_additive` / `to_dual` keep the build-time kernel check because their elaboration depends on it |
| cost hints and priorities from earlier runs, planner shortcuts | build | they change order and thread counts only |
| native exporter, optionally on tmpfs | export | a wrong or truncated export is rejected or declined by the judge; the closure guard declines first |

Inside the judge, a few speed-ups are part of the trusted base and were reviewed and gated as such: the parallel replay
with priority scheduling of known long kernel jobs (order only), the opt-in targeted overlap of the longest jobs with the build,
and `gruszka` as the second kernel. Fallbacks never lower trust: a fast build that declines falls back to an exact build,
and a native export that declines falls back to the official exporter.

## Toolchain verification

Every Lean binary run on the project (`lean`, `lake`, `leanc`, the core libraries) is the unmodified official release named
by the project's `lean-toolchain`. `fastverify/lib/toolchain.py verify ROOT ID` compares the whole installed tree with the
pinned manifest `fastverify/toolchains/<id>.json` (sha256, executable bit and size of every file, every symlink target, the
directory set; no missing, extra or special files) and checks that `lean --version` and `lake --version` print the pinned
lines. This runs at the start and again at the end of every run; any change gives ERROR. `toolchain.py install` copies a
verified tree to a local directory, and `toolchain.py pin` writes a manifest for another official release
(`tools/addrelease.py` does this for the admitted releases). The patched and PGO build toolchains of `--preset sound` are
pinned by whole-tree manifests in `fastverify/toolchains/unofficial/` and used only as untrusted producers.

## The judge and its variants

The default judge, `fastverify/check/sound/check-sound.sh`, runs three legs concurrently and decides per leg: `ccmp` (the
official comparator judge code), `pleanchecker` (every safe, non-partial declaration through the official kernel, as
`Lean.Replay` does, plus its record checks) and `gruszka` (the independent second kernel, which also sees the
`unsafe` and `partial` records). All variants decide the same conditions with the same verdict rules and keep the second
kernel mandatory; they trade time for memory, add assurance, or support another Lean release.

| variant | entry point | how it differs | selected by | status |
|---|---|---|---|---|
| sound (default) | `check/sound/check-sound.sh` | three concurrent legs | `--preset sound`, `sound-auto` | proven |
| low-memory | `check/lowmem/check-sound-lowmem.sh` | legs run in sequence; the comparison leg streams the export and builds expressions only for what `compareAt` reads | `sound-auto` when its estimate exceeds the memory budget and the judge is installed and compatible (no required extra kernel, no frontier); `fv check --low-mem` | proven |
| ultra-low-memory | `check/lowmem/check-sound-ultralowmem.sh` | adds a paged expression store that evicts checked theorem bodies (linked against the unmodified official v4.36.0 libraries) and a disk-backed second kernel | run directly; no preset selects it | proven (known false rejects: [limitations](../limitations.md#assurance)) |
| warm delta | `check/warm/fvcheckd.py` | verifies a base export once with resident legs, then checks only changed declarations and their dependents with all three legs; a delta touching a kernel built-in (`Nat`, `Eq`, `Quot`, ...) answers "fallback required", never ACCEPTED | none: fvwork, fvserve and incr-reverify refuse it; the standalone daemon is research code | not in v0.1 (research code, not sound in its current form) |
| frontier (conditional) | `check/frontier/check-frontier.sh` | for a nonempty frontier, two runs of the unchanged judge (the first can come from its cache): a minted frontier challenge against the official one, and the export with the open lemmas as hypotheses against the frontier challenge; an empty frontier is the ordinary check | `--modulo-frontier`, `fv check --frontier` (`fvwork serve --check frontier` is experimental in v0.1) | proven, opt-in |
| notary | `check/notary/check-notary.sh` | the unmodified official 4.36 release kernel libraries plus a canonical environment SHA-256 that all three legs compute and must agree on; optional extra kernels | `--preset notary`, `fv check --notary` | EXPERIMENTAL in v0.1 (needs `--experimental`) |
| Lean 4.37.0-rc1 | `check-sound.sh --pins check/sound/pins-437.env` | built from the official 4.37.0-rc1 comparator judge code and kernel; encapsulated replay (below) | `--preset sound` and `sound-auto` for 4.37.0-rc1 challenges; `--pins` | proven |

**Encapsulated replay (Lean 4.37).** Lean 4.37's module system hides theorem bodies and non-exposed definition bodies from
importers, so the build-time kernel never unfolds them, while a flat export restores them; on large module-system
exports a plain replay can take extremely long. The 4.37 judge's kernel leg therefore first checks each declaration in
an environment in which earlier theorems and the definitions on a hide list are visible by type only, and an acceptance
there counts. That environment only lacks unfoldings of constants that exist with the same types in the full
environment; that an acceptance there holds in the full environment rests on the argument that typing is monotone in the
set of unfolding (delta) rules, checked by reading the kernel's rules, with a Lean kernel maintainer's confirmation
pending ([basis](soundness.md#the-trusted-base)). The hide list (`check/sound/hide/lean-4.37.0-rc1-no-expose.txt`) is untrusted: on any failure,
or after a per-attempt time budget, the declaration is checked in the full environment, which decides. A wrong list costs
time, never a verdict. The comparison leg and the second kernel are unchanged.

## Services on top of the pipeline

All of these are untrusted orchestration around the same judge (see [user-guide.md](../user-guide.md)):

- `fastverify/bin/fv` - the daily CLI (verify, check, attempt, watch, ci, init-challenge, audit, doctor, triage, lookup,
  diff, mint), with JSON, SARIF and LSP output.
- `tools/fvwork` - a per-repository daemon that keeps the pinned challenge and the last judged tree and answers each
  submitted tree with a whole-project sound verdict. In v0.1 every request takes the cold sound path (`bin/fastverify
  --preset sound` on the submitted tree); its incremental machinery (reuse of the last build tree, pre-warmed legs, the
  frontier and warm checks) is EXPERIMENTAL, behind `--experimental-incremental`, and never counted.
- `tools/fvserve` - an attempt service for provers and RL pipelines: fixed costs paid once, attempts for different
  theorems batched into one export and one check, per-attempt verdicts. `tools/http/fvapi.py` (Kimina-compatible HTTP)
  and `tools/mcp/fastverify-mcp` (MCP over stdio) sit in front of it.
- `tools/ci-action` - a CI and pull-request gate (EXPERIMENTAL); in v0.1 `fv ci` ignores `--cache-dir` (every run is
  cold) and `--disk` has no effect.
- `tools/guard` - per-run resource limits; a limit hit is always NO-VERDICT.

## Components and sources

The repository ships sources only. The fast binaries are built from the vendored [`sources/`](../../sources/) and the
stage sources and patches under `fastverify/` (some need build inputs that are not shipped, see
[limitations](../limitations.md#platform)) and pinned by sha256; a stage refuses to run when its binary is missing or
differs.

| directory | component |
|---|---|
| `fastverify/check/sound/src` (+ `src-437`, `overlap/src`, `check/{lowmem,warm,notary}/src`) | `ccmp`, `pleanchecker`, `pleanchecker_incr` and the low-memory / warm / notary / 4.37 judge binaries (the live trusted sources) |
| `sources/pchk` | Check A v3 (`d876802`) parallel checker base, the origin of the judge's `pleanchecker` walk and `ccmp` (check A itself was retired before v0.1); it also holds the official kernel sources of the judge's PGO builds |
| `sources/gruszka` (+ `fastverify/check/checkB/patches/gruszka-combined.diff`) | the independent second kernel (conformance patches applied for `gruszka` and `gruszka-lowmem`) |
| `sources/lean4export-native` | the native exporter |
| `sources/nano-lean`, `sources/kcompare` | an independent kernel and statement comparison used by legacy research checks |

Origins, pinned hashes and build recipes of every component are in
[`fastverify/PROVENANCE.md`](../../fastverify/PROVENANCE.md); building them is described in
[getting-started.md](../getting-started.md#4-build-the-pinned-fast-components).
