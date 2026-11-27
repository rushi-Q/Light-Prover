# Export stage (`export/`)

The export stage turns the built `.olean` files into `solution.export`: the lean4export NDJSON of the solution module's
import closure, restricted to the targets that the comparator derives from `comparator.json` (theorem names, definition
names, permitted axioms, the kernel primitives, `Quot.*`). The stage is untrusted: the judge checks the file it writes,
so a wrong export can cost a verdict but cannot produce an ACCEPTED for an invalid proof. Its contract is still strict:
the file must be byte-identical to what the official exporter writes for the same `.olean` files, or the stage declines
and the official exporter runs.

## Options

**E0, the official exporter.** The unmodified `leanprover/lean4export` tag v4.33.0 built with the official Lean 4.33.1
Lake (for 4.35 and later: the release's bundled `leanexport`), run in bubblewrap with `LEAN_ABORT_ON_PANIC=1`, so a panic
path (reachable only with kernel-unchecked declarations) aborts instead of exporting a substituted term. Single-threaded:
5,306 s and 164 GB peak on the full Riemann Hypothesis proof. At that scale it needs `vm.max_map_count` above about
500,000. E0 is also the fallback of every E1 decline.

**E1, the native exporter.** `export/export.sh` runs a C++ core that reads the `.olean` files in place, in parallel, and
reproduces lean4export's walk, index numbering and JSON rendering: 47.6-50.6 s on the full Riemann Hypothesis proof at
128 threads, peak about 270-290 GB. It declines (exit 2, no output) wherever it cannot reproduce the official bytes:
projection or bound-variable indices beyond 2^32, invalid UTF-8, duplicate constants it cannot decide exactly as Lean's
import does, numeric name components, panic paths of the official exporter, `.olean` or IR files with another githash or
a malformed header, lean4export options. An independent closure guard (`export/closure/closure_check.cpp`) then checks
every native export: every line a JSON object of a known shape, ids sequential, every reference and every target
declared. A violation is a decline. Releases: 4.33.1 by default; 4.36.0 and 4.37.0-rc1 through `natives_other` entries
of `components.json`; other releases always use E0.

**Low-memory exporter** (`export/export-lowmem.sh`, `components-lowmem.json`): E1 with output-neutral memory changes
(earlier release of IR buffers, 4 KB paging, release of clean `.olean` pages, a sequential dump with direct I/O). It
writes the same bytes; `sound-auto` selects it below a 16 GB budget.

Evidence for byte-identity: the full Riemann Hypothesis export equals the original-Lean export (sha256 `5ea74b91...`,
61,570,595,788 bytes) on three hosts and at 128 and 384 threads; 166 random-target exports of the Mathlib and rh-mid
environment are byte-identical to E0; the component cases of `tests/export/run.sh`. Equivalence is established by
construction and tests, not by proof; the judge does not depend on it.

## Pinned binaries

| binary | pin file | sha256 | source and build |
|---|---|---|---|
| E1, Lean 4.33.1 | `components.json` `native` | `6b26eb16c45e201dc90af2ad6a876d77a745ee8274c72bb64e85c3bb0c5fe404` | `sources/lean4export-native` (fork f581123 + `native-exporter-f04.patch`), `lake build` with the official 4.33.1 toolchain |
| E1, Lean 4.36.0 | `natives_other[0]` | `bb25a91e10fa83c61e462d4d2fa664a7b20da3370233cdacbc3f1fe16277c0b2` | the same source built with the official 4.36.0 toolchain |
| E1, Lean 4.37.0-rc1 | `natives_other[1]` | `174f3962414c76d79634c9d104c4986f065c86c55c723d66885bb7e5237ae8db` | plus `native-exporter-d22-v437.patch` (olean format v4), built with the official 4.37.0-rc1 toolchain |
| closure guard | `closure_check` | `60b84139b18e352ddcaf79e36e1c44d79e5636efe26dc3c47f6a727eac4211cc` | `g++ -O2 -std=c++17 -pthread -static -o closure_check export/closure/closure_check.cpp` |
| E0, Lean 4.33.1 | `official` | `805ab4cc6a88dcef109644d201c3142261f524aecaf58b04913a9f029e21e9b5` | upstream lean4export v4.33.0 (15f6055), `lake build` with the official 4.33.1 toolchain |
| low-memory exporter, Lean 4.33.1 | `components-lowmem.json` `native` | `a86e719879d88f189b6e58001deb0411426dedabcee6b4318883ba6b4caaecba` | E1 plus a memory patch applied by a script that is not shipped |
| low-memory exporter, Lean 4.37.0-rc1 | `components-lowmem.json` `natives_other[0]` | `9c4ae13d05feb8028f250d78ca39692ffefdc10fbf19383ef036f0faaa770f1e` | the 4.37 E1 plus the same memory patch (not shipped) |

Rebuild of E1 (4.33.1):

```bash
git clone <native lean4export fork> lean4export && cd lean4export && git checkout f581123
git apply fastverify/export/native-exporter-f04.patch        # = sources/lean4export-native
T33=$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1        # official release
env PATH=$T33/bin:/usr/bin:/bin $T33/bin/lake build          # -> .lake/build/bin/lean4export
```

For 4.37.0-rc1 apply `native-exporter-d22-v437.patch` as well and build with that toolchain; two builds from different
toolchain paths and directories gave the same sha256. The closure guard rebuilds byte-identically with the command in the
table. The low-memory exporters cannot be rebuilt from this repository (the patch script is not shipped); without them
`sound-auto` uses E1 or E0.

## Interface (`export/export.sh`)
```
export.sh --preflight TOOLCHAIN_PREFIX     # (natives_other: the entry of the toolchain's release is selected first) 0 iff the pinned native binary exists, matches its sha256, the toolchain is
                                           # Lean 4.33.1 (819816b2) and a tiny sandboxed export works on this host
export.sh --lean-path LP --module 'MOD [MOD..]' (--targets-nl TF | --targets-file TF) --toolchain TC --project PROJ [--binds TSV]
          --out OUT [--threads N] [--json F] [--official-fallback] [--verify] [--sha256]
```
`--targets-nl TF`: one target name per line, verbatim (use this; names such as `«a b»` contain spaces).
`--targets-file TF`: whitespace-separated names; a name split at whitespace (unbalanced `«`/`»`) makes the stage decline.
Exit 0 = OUT written; 1 = the official exporter failed (only with `--official-fallback`); 2 = declined, no OUT;
3 = `--verify` (also runs E0 and byte-compares, diagnostic) found a difference. One JSON object on stdout and in
`--json F` (exporter used, native exit/seconds/decline reason, official exit/seconds). The native exporter runs in
bwrap (read-only filesystem, tmpfs home/tmp, `--clearenv`, no network) with only PATH (toolchain bin), HOME, LANG,
LEAN_PATH, LEAN_ABORT_ON_PANIC=1, LEAN4EXPORT_THREADS (= --threads), LEAN4EXPORT_VERBOSE=1 and, when LEAN_PATH holds
more than 100k `.olean` files, LEAN4EXPORT_EXPR_ESTIMATE_LOG2=31 (initial table size; output-independent). Its stdout
is a private file created by the stage and renamed to OUT only after exit 0. The script is one function (parsed
completely before it runs), so replacing it during a run cannot corrupt that run.

## macOS

On macOS (Apple silicon, Lean 4.33.1) the stage runs E1 and E0 natively, in the sandbox of `lib/macos/stage.sh`.
Readable there: the toolchain, the project, the sources of `--binds`, the exporter itself and, as in every sandbox
start of that file, the developer directory (`xcode-select -p`) and the system's programs and libraries
(`lib/macos/sandbox-run.py` lists them). Writable: a private temporary directory; the output file is opened outside
the sandbox.

- **E0** is the official exporter that `tools/configure.py` pinned for the toolchain (`config/components.macos.json`):
  upstream lean4export v4.33.0 built on the Mac with the release toolchain.
- **E1 and the closure guard** are compiled on the machine by the system's C++ compiler, which differs from Mac to
  Mac, so the tree has no digest of them (it has one of the judge's Lean programs: the pinned toolchain's own compiler
  builds those). `export/build-macos.sh OUTDIR` builds `sources/lean4export-native` with
  `export/native-exporter-macos.patch` and `export/closure/closure_check.cpp`, and records both in
  `config/export-macos.env`, a file of the export stage alone: a comment line with the compiler and the SDK, then
  `SRC <program> <fingerprint of its sources>` and `PIN <program> <sha256> <path>`. `config/components.macos.json`
  pins the two fingerprints. `export.sh` uses a recorded program only if it was built from these sources and has the
  recorded sha256; without one, `--preflight` fails and `--official-fallback` gives E0.

The patch (40 added lines, each inside a test for macOS, applied to a private copy: the vendored sources stay as they
are) compiles the C++ core with libc++ instead of the libstdc++ glue, lets the output sink take its WRITE back end
(MAP and DIO reopen `/proc/self/fd/1`), grows an output buffer by copying (no `mremap`), leaves the parallel teardown
out, and takes the number of CPUs online as the default number of threads. The exporter is outside the trusted check:
the closure guard and the judge examine what it writes, so a wrong export can cost a verdict and cannot make one.

What differs from Linux:

- The stage waits for the native exporter's exit status. Linux returns at the exporter's last log line and kills the
  sandbox; on macOS that kill would not reach the sandbox's processes.
- A failing official exporter is exit 2 (no verdict), never exit 1, and under `--verify` exit 2, not 3: the failure can
  be the sandbox's or the guard's (a refused access; a physical footprint above the machine's memory).
- `--ro` is refused: its check of the directory's owner is written for Linux.
- E1 is built for Lean 4.33.1 only: no `natives_other` exporter and no low-memory exporter. Another toolchain with
  macOS pins is exported by its official exporter (`--official-fallback`).

## Tests
* `tests/export/macos.py [WORK]` (macOS only, about 1 min), in a copy of the tree, so that the machine's record is not
  touched: the recipe, which leaves the judge's record alone; E1 on a project with a dependency package,
  byte-identical to E0 inside and outside the sandbox, with the default threads and with one; no export without
  `--binds`, with a missing target or with `--ro`; the closure guard against a recorded program that leaves out a
  declaration; a recorded program that fails after its last log line; a record with another source fingerprint;
  `--verify` without E0.
* `tests/export/run.sh [WORK] [--heavy]` (also `tests/stage-export`): oleans built with the official 4.33.1 (some
  with `-Ddebug.skipKernelTC=true` to obtain kernel-invalid inputs); E1 vs E0 on: control, 008, 010, 013 (types differ:
  theorem and axiom), equal duplicates (incl. binder-name/-info differences), 018, 030, 033, foreign githash, IR parts
  (good / `.ir` missing / `.ir` githash / stray `.ir.sig`), missing target, options, path with spaces, a kitchen sink of
  valid constructs (escaped/control/astral strings, `«»` names with spaces, big Nat literals, nested and mutual
  inductives, structures, classes, imax/max, let/have, Quot, structural and well-founded recursion, opaque/partial/unsafe/
  noncomputable, axioms) and the same targets through the whitespace format (must decline); an unsafe target (guard
  declines); the closure guard against a fake native exporter that drops one declaration (must decline); an injected
  internal script error (exit 2); `--heavy` adds
  rh-mid. PASS = identical bytes, or E1 declines and the E0 fallback gives the official result.
  On macOS it runs with the recorded E1, without the two cases that copy the stage script (closure guard, internal
  error): `tests/export/macos.py` has them.
* `tests/export/difftest/difftest.sh WORK NRUNS SEED [JOBS]`: random-target differential test against E0 on the
  rh-mid environment (needs the compiled `ListConsts.lean`, see the script).
