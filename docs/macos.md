# macOS (Apple silicon)

On arm64 macOS the build, the export and the check run natively, each as its own stage script: no Linux virtual
machine and no container. The orchestrator (`bin/fastverify`, `fv`), the daemons and the services are not supported
there in this version, so a verification on a Mac is three commands, not one.

| stage | scripts | detail |
|---|---|---|
| build (untrusted) | `fastverify/build/official-build.sh` (B0), `fastverify/build/build.sh` (B1 to B3) | [build/README.md](../fastverify/build/README.md#macos) |
| export (untrusted) | `fastverify/export/export.sh` (E0, E1) | [export/README.md](../fastverify/export/README.md#macos) |
| check (trusted) | `fastverify/check/lowmem/check-sound-lowmem.sh`, `check-sound-ultralowmem.sh` | [check/sound/macos/README.md](../fastverify/check/sound/macos/README.md) |

What Linux gets from bubblewrap, bind mounts, cgroups and `timeout`, the macOS stages get from a sandbox profile that
denies by default (`fastverify/lib/macos/sandbox-run.py`: no network, writes only where the stage grants them, reads
there and in the system's program and library folders, only the environment the stage names), from links into the
trusted packages workspace in place of the bind mounts of the dependency packages, and from the resource guard
(`fastverify/tools/guard/fvguard.py`: memory, wall clock and the end of the stage, over the processes of the stage
that it has seen). The judge also runs its programs and reads its inputs from private clones. It compares the
digests of the programs and of its own self-test inputs with the pins before the first check and again after the
last, and the change stamp (size, times, inode) of every clone, the judged export among them, before and after each
check. The judged export is not hashed; the challenge and the configuration are hashed once, at the start.

The check runs the three checks of Linux in the same order: the comparison of the statements with the axiom check,
the official Lean 4.36 kernel and the independent second kernel. One program differs: the second kernel of the
ultra-low-memory judge is the default `gruszka`, on Linux its disk-backed variant. The programs are built on the Mac
from the sources and patches the Linux recipes use, with no source changed for macOS; the Lean programs are linked
with the unmodified libraries of the official Lean 4.36.0 release, so the official kernel is not compiled on the
Mac. The judge runs them only if their bytes are the ones this tree pins (`fastverify/check/sound/macos/pins.env`).
New in the trusted part is the driver that starts them and reads their results (`fastverify/check/sound/macos/`),
in place of the orchestration of the bash judge scripts.

## Setup

Needs: Apple silicon, macOS 15.4 or later (by Apple's published sources; everything was tested on macOS 27.2
only), the Xcode Command Line Tools or Xcode, elan
with `leanprover/lean4:v4.33.1` (projects) and `leanprover/lean4:v4.36.0` (judge), and the official `lean4export`
v4.33.0 built as [getting started](getting-started.md#3-official-toolchains-and-the-official-exporter) says. The
judge's second kernel also needs Rust 1.97.1 and the crate archives of `sources/gruszka/Cargo.lock`
(`cargo fetch --locked` there, once, with network).

```bash
# 1. the machine's configuration: the macOS pins of the toolchains, every pinned file checked
#    (--elan-home and --light-lean as in getting started, if elan or the exporter are not at their default places)
python3 -I fastverify/tools/configure.py

# 2. optional: the fast exporter E1 and the closure guard (without them: export.sh --official-fallback, E0)
fastverify/export/build-macos.sh OUTDIR

# 3. the judge's four programs; prints the digest of their record, the --pins-sha256 of every run that judges
fastverify/check/sound/macos/build-judge-macos.sh OUTDIR
fastverify/check/lowmem/check-sound-lowmem.sh --preflight
fastverify/check/lowmem/check-sound-ultralowmem.sh --preflight
```

Step 3 takes one to two minutes, uses no network, needs neither step 1 nor step 2 and stops unless the four programs
have the pinned bytes. OUTDIR has to stay: the record names the programs there. Its path may hold only letters,
digits and `. _ + @ -`.

## Running the stages

Each script takes the arguments it takes on Linux, apart from the options listed below as not on macOS, and writes
a JSON result with the fields of Linux where they mean the same (the check's result leaves out `ccmp_rc`, `leg_ms`
and `compare_ms` and adds its own, among them `wiring_sha256`, `selftests` and the `peak_footprint_bytes` of each
check). The exit statuses are the same except where the stage's README says otherwise (for example,
`export.sh --verify` ends with exit 2, not 3, when the official exporter did not finish). The interfaces are in the
three READMEs above. The check has one more required option on macOS: `--pins-sha256`, the digest that step 3
printed for its record of where the four programs are.

```bash
fastverify/check/lowmem/check-sound-ultralowmem.sh solution.export challenge.export comparator.json \
    --pins-sha256 DIGEST --challenge-sha256 "$PIN" --comparator-sha256 "$CPIN" --json verdict.json
```

`check-sound-lowmem.sh` replays with the official kernel and the whole export in memory;
`check-sound-ultralowmem.sh` streams the export through the same kernel, which is the one for an export of the size
of the Riemann Hypothesis proof on a Mac with 64 GB. For a large export, give `--workdir DIR` with an existing
folder on the export's volume: the judge's private copy of the export is then a clone that takes no space, and a
full copy anywhere else.

## Not on macOS in this version

- The orchestrator and everything on top of it (`fv`, daemons, services, the CI gate); `check-sound.sh`,
  `check-sound-svc.sh`, the notary and frontier judges; `tools/lowmem/fv_lowmem.py` (the judge command it builds
  names no record of the programs, so it gives no verdict); `--require-modules`; `--ro` of the export stage.
- Build items that need the patched Linux toolchains or bubblewrap: `toolchain-T1`, `zygote`, `native-pkg`.
- The fast exporter for other Lean releases than 4.33.1, and the low-memory exporter. E0 and E1 need more memory
  than the export is large: for the Riemann Hypothesis export (61.6 GB) that is estimated at more than 64 GB.
- Judges for other Lean versions than 4.36; the programs `gruszka-lowmem` and `ccmp`; kernels named by a comparator
  configuration (with `--keep-config-kernels` no verdict; without it they are dropped as on Linux); the incremental
  replay.

## What differs from Linux

- The sandbox is a profile, not a mount namespace: it hides no path. A sandboxed process can read the metadata of a
  file outside its grants (that it exists, its size and times), not its contents and not a directory's listing.
- In the build and export stages, an access the sandbox refuses is no verdict when the system's message reaches the
  output, because the same project could pass on Linux, where such a path is hidden or held in a tmpfs. In the
  check, a program that ends with the status of a rejection and an error of the operating system in its output is no
  verdict; the output of a program that accepts is not searched.
- Memory limits are enforced by polling the physical footprint of the process tree, not by a cgroup. A process that
  leaves the stage's process group before it is sampled once is neither counted nor ended with the stage; it stays
  inside the sandbox profile.
- The Linux judge scripts put no memory limit on a check. On macOS each of the three has one (the physical memory,
  or `--mem-budget-mb`), and a check stopped there is no verdict.
- Where the macOS check differs from Linux, it gives no verdict where Linux gives one: at a memory or time limit, and
  for some outputs of a program that the Linux scripts read as REJECTED or ACCEPTED (the table is in the judge's
  README). It never says ACCEPTED where Linux would not, by the content of an export.

## Tests

The CI workflow of the repository (`.github/ci-workflow.yml`, Linux; it is switched on by moving the file) runs the
rows of `fastverify/tests/macos-judge/run.py` that need no Mac. On a Mac, by hand:
`fastverify/tests/macos-sandbox/run.py`, `fastverify/tools/guard/test/test-fvguard-macos.py`,
`fastverify/build/test/macos.py`, `fastverify/tests/export/macos.py`, `fastverify/tests/macos-judge/run.py` and, with
the built programs, `fastverify/tests/macos-judge/programs.py`. The suites `build/test/run.sh`, `merge.sh`,
`premiseoff.sh`, `crash-retry.sh`, `tests/budget/run.sh` and `tests/export/run.sh` run on both systems; a few of
their cases print SKIP on a Mac.
