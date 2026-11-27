# The macOS judge (`check/sound/macos/`)

On arm64 macOS the judge scripts `check/lowmem/check-sound-lowmem.sh` and `check/lowmem/check-sound-ultralowmem.sh`
hand over to this directory: `enter.py` starts the driver `judge.py` and publishes its result. The driver runs the
legs of the script that was entered natively, one after another, with programs that `build-judge-macos.sh` compiles
on the Mac from the judge sources of this tree. The arguments, the exit status (0 ACCEPTED, 1 REJECTED, 2 no verdict)
and the fields of the JSON result are those of the script, with one added option: a run that judges must name the
record of the programs it trusts (`--pins-sha256`).

```
check/sound/macos/build-judge-macos.sh OUTDIR      # once: builds the four programs, prints the digest of their record
check/lowmem/check-sound-lowmem.sh --preflight     # the record, the programs and the self-tests
check/lowmem/check-sound-lowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON --pins-sha256 DIGEST [--threads N] ...
check/lowmem/check-sound-ultralowmem.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON --pins-sha256 DIGEST ...
```

## What it runs

| judge script | comparison | official-kernel leg | second kernel |
|---|---|---|---|
| `check-sound-lowmem.sh` | `ccmp-lowmem` | `pleanchecker` | `gruszka` |
| `check-sound-ultralowmem.sh` | `ccmp-lowmem` | `pleanchecker-lowmem --low-mem --evict=smart` | `gruszka`, where the Linux script runs `gruszka-lowmem` |

Each script runs the legs it runs on Linux, with one stated difference: the second kernel of the ultra-low-memory
judge is the default `gruszka`. The Riemann Hypothesis export on a Mac with 64 GB is a case for
`check-sound-ultralowmem.sh`, as on Linux.

A run, in this order: the arguments; the record of the programs; private copies of the programs and the inputs; the
configuration step of the judge script; the caller's `--challenge-sha256` and `--comparator-sha256`; the cross-version
gate (`check/xversion/xvcheck.py`); the self-tests; then the comparison, the official-kernel leg and the second kernel
on the judged export. ACCEPTED needs every leg to accept. As in the scripts, the legs get all processors unless
`--threads` says otherwise, and one worker per 256 MiB (at most 32) under a `--mem-budget-mb` below 65536.

**The arguments are read as the script reads them:** `--preflight` only in front, otherwise the three inputs in
front; the value of an option in the next argument; numbers in digits only; the last of a repeated option counts; any
other argument is unknown, also an option that only the other script has (`--pins` and `--hide` are options of
`check-sound-lowmem.sh`). Every option of the script is honored, or has nothing to do here because what runs without
it is at least what Linux runs with it, or gives no verdict:

| option | on Linux | here |
|---|---|---|
| `--integrity-cache DIR` | skips the hashing of the pinned files while their stamps are those of an earlier run | the directory is checked as on Linux; every pinned file is cloned and hashed at every run |
| `--incr-dir DIR` | lets the official-kernel leg ask an incremental replay started by the build; without one the plain replay runs | the path is checked as on Linux; the plain replay always runs |
| `--private-inputs` | the caller's word that nothing else writes the export; an input over 4 GiB is then linked, not copied | every input is cloned, whatever is said |
| `--keep-config-kernels` | the kernels that the config names run too and can veto | no verdict when the config names a kernel; nothing to do otherwise |
| `--mem-budget-mb MB` | caps the workers | caps the workers and is the memory limit of each leg, in place of the physical memory (below) |

**The other judge scripts.** `check/sound/check-sound.sh` runs three programs at once and needs `ccmp`: on macOS it
ends with DECLINED and names the two scripts above. `check/sound/check-sound-svc.sh`, `check/notary/check-notary.sh`
and `check/frontier/check-frontier.sh` run their Linux code, which needs bash 4, bubblewrap and the pinned Linux
programs, and end with DECLINED (exit 2). The orchestrator's sound check is `check-sound-svc.sh`, so `fastverify`
gives no sound verdict on macOS in this version; `tools/lowmem/fv_lowmem.py` builds a judge command without
`--pins-sha256` and gives none either. Support on macOS starts at the two judge scripts.

## Programs and pins

`pins.env` in this directory holds everything the tree pins for the macOS judge:

| pinned | line of `pins.env` |
|---|---|
| the SHA-256 of each of the four programs; a file without one of them is refused | `PIN <program> <sha256>` |
| the fingerprint of the sources of each of the four programs | `SRC <program> <sha256>` |
| the patch of the second kernel and the five self-test inputs of `check/sound/selftest` | `PIN <name> <sha256> <file>` |

**All four programs are pinned by their bytes, as on Linux.** They are compiled on the Mac, and the build gives the
same bytes every time. No compiler, linker, archiver or signing tool of Apple takes part in any of them: the C code
is compiled, and every program is linked and signed, by the clang and the lld of the Lean toolchain, and the Rust
code of the second kernel by `rustc`. The judge refuses other bytes than the pinned ones, whatever the record of the
machine says. So nothing that a build takes from the machine needs a pin of its own: what changes a byte of a
program is refused at the judge, and what changes nothing is harmless. A build takes three things from outside the
tree and the Lean toolchain:

| from the machine | for | checked by the recipe |
|---|---|---|
| the C headers of the SDK of the Command Line Tools or of Xcode | the C file of the comparison and the allocator of the second kernel | no; the record names the SDK |
| Rust 1.97.1 | the Rust code of the second kernel | by the line that `rustc --version` prints |
| the 31 crate archives of `Cargo.lock` | the second kernel | each by its SHA-256 in `Cargo.lock` |

| program | SHA-256 | bytes |
|---|---|---|
| `ccmp-lowmem` | `3a8b06a5280b83e7f86bdad93cc3323fce251e2b71a6bccfd7e295d2f30f571c` | 107,533,968 |
| `pleanchecker` | `263b1e0bff7e42dbe5ec6061c4a86e743998f3f76f013c97efc21e51912ebeb8` | 107,286,144 |
| `pleanchecker-lowmem` | `c2ace2888ae18ed15c85876dfa886557eb4f73327038ef2ab1936e8d7fb9f56b` | 108,156,064 |
| `gruszka` | `af94f856aaa0a9683a560e6a890bab7993840e17ae109c16ebeabdb8b7dad6a6` | 2,126,768 |

**What was measured.** Two Macs with macOS 27.2.1: an M4 with the Command Line Tools (SDK 26.2) and an M5 Pro with
Xcode (SDK 27.2). The three Lean programs: nine builds in different folders, with one, two and four build jobs, four
of them with the toolchain installed at another place. `gruszka`: seven builds, four of them the whole recipe and two
of those on the M5 Pro, with the C headers of the SDKs 15.2, 15.4, 26.2 and 27.2, in different folders, with one, two
and four build jobs, three with the toolchain at another place. One build of the whole recipe, on the M4, ran in a
sandbox that refuses to start the compilers, the assembler, the linkers, the archivers and the signing tools of the
system and of the Command Line Tools: it gave the same four programs. All four read `minos 11.0`, `sdk 11.0` and the
linker of the toolchain in their build version and hold no path of the machine. That a Mac with another macOS gives
the same bytes follows from the next two paragraphs and is not measured.

**What the recipe fixes for the Lean programs.** Two things of the machine would otherwise reach their bytes. The
clang of the toolchain takes the version of the running macOS as the oldest system a program is for, and the linker
writes it into the file: the recipe names macOS 11.0 (`MACOSX_DEPLOYMENT_TARGET`), the target of the toolchain's own
programs. And the C file of the comparison names `lean.h` by the place where the toolchain is installed: the
compiler is given `/lean-tc` for it. The recipe stops when a program holds the build folder, the place of the
toolchain or the home folder of whoever builds as text.

**And for the second kernel.** `gruszka` is a Rust program with an allocator in C. Compiled and linked by the C
compiler and the linker of the machine, it held their versions and the version of the SDK, and two Macs with other
developer tools gave other bytes. So the clang and the lld of the Lean toolchain do both, without `SDKROOT`, from
which clang takes the version of the SDK, and for macOS 11.0. The program loads `/usr/lib/libSystem.B.dylib` only.
Before every judgement it must still accept the known-good and reject the kernel-invalid self-test.

| program | sources, as the Linux recipe takes them |
|---|---|
| `ccmp_lowmem` | eight names of `check/sound/src` and five of `check/lowmem/src` (`tools/reproduce/rebuild-lowmem.sh`) |
| `pleanchecker` | `check/sound/src` (`tools/reproduce/rebuild-pchk.sh`) |
| `pleanchecker_lowmem` | `check/lowmem/src-ultralowmem/src/pleanchecker-lowmem` (`build-pleanchecker-lowmem.sh` there) |
| `gruszka` | `Cargo.toml`, `Cargo.lock`, `src` and `vendor` of `sources/gruszka` without `vendor/susz/tests`, with `check/checkB/patches/gruszka-combined-v6.diff` applied (`tools/reproduce/portable-gruszka.sh`) |

The fingerprint of a program's sources is the SHA-256 of what `find . -type f | LC_ALL=C sort | xargs sha256sum`
prints in the staged directory, so it can be computed on Linux; for `gruszka` it is the number that
`portable-gruszka.sh` prints as its source tree. Only regular files are sources: a symbolic link among them is refused.

**The record of the machine.** The recipe writes `fastverify/config/pins-macos.env`, which is not tracked, and prints
its SHA-256. It holds comment lines and two lines for each program, and nothing else:

```
SRC <program> <fingerprint of its sources>
PIN <program> <sha256> <absolute path>
```

**`--pins-sha256` is required for every run that judges.** Which bytes may run is fixed by `pins.env`, as on Linux:
the commit is the authority, and a record that names other bytes is refused. The record says where the four programs
are on this machine, a run takes its programs from nowhere else, and the caller names the record it means. Without
the option, or with another digest than the record's, there is no verdict, and no program that the record names is
read or started. Take the digest when the build ends. `--preflight` judges nothing and runs without it. A result
names the record and its digest (`pins`, `pins_sha256`) once the run has passed its first checks (the arguments, the
record and its lines for the programs, the output paths, the wiring), a preflight too; a run that was declined before
that names neither.

**The programs run from private copies.** A program is started by its path. On Linux the bind mount of the judge
fixes the file behind that path for the whole run; the macOS sandbox is path-based, so the driver fixes the bytes
itself. It clones the three programs of the judge script and the self-test inputs into the private directory of the
run, compares the SHA-256 of each clone with `pins.env`, where the record must name the same digest for a program,
starts only the clones, compares their change stamps before and after every leg and their SHA-256 again after the
last (`binaries_sha256` in the result). What the recorded path leads to after the clone was made does not matter.

The judge also gives no verdict when the record lacks the lines of a program it needs or names another fingerprint
than `pins.env` (the program is older than the sources). `--pins` names only a `pins*.env` file directly in
`fastverify/config`; without the option the record is `pins-macos.env` there, and a symbolic link that leads elsewhere
is refused. The first argument of the comparison program names a Lean installation; with `--compare-only` it uses
nothing of it, and it is given the system's empty directory.

## Building

Needs arm64 macOS with the Command Line Tools, the official Lean 4.36.0 toolchain (`elan toolchain install
leanprover/lean4:v4.36.0`) and Rust 1.97.1, the release of the Linux recipes for `gruszka` (`rustup toolchain install
1.97.1`; a `rustc` that prints another line than `rustc 1.97.1 (8bab26f4f 2026-07-14)` is refused). The build uses no
network. The 31 crate archives of
`sources/gruszka/Cargo.lock`, all from crates.io, must be on the machine: `cargo fetch --locked` run once in
`sources/gruszka` with network puts them into `~/.cargo/registry/cache`, where the recipe looks. All 31 are needed,
also the six that only the tests of one crate use and that are not compiled, which a `cargo build` alone never
downloads: cargo resolves the whole of `Cargo.lock` against what it is given.

```bash
fastverify/check/sound/macos/build-judge-macos.sh OUTDIR                  # LEAN_NUM_THREADS=N: build jobs (default 2)
fastverify/check/sound/macos/build-judge-macos.sh --sources-only OUTDIR   # only stage and compare the sources
```

`TC36`, `FV_RUST_BIN` (the directory with `cargo` and `rustc`) and `FV_CRATES` (a folder with the
`NAME-VERSION.crate` files) override the default places. The recipe

1. stages a private copy of the sources of each program, applies the patch of the second kernel (its SHA-256 is
   checked; it must apply without offset) and compares the fingerprints with `pins.env`;
2. checks the Rust version, and 23 files of the Lean toolchain against `config/components.macos.json` (the launchers,
   their shared libraries and what the programs are linked from), so that a wrong toolchain is named before an hour
   of compiling and not after;
3. builds the three Lean programs with `lake build`, each in an environment that the recipe writes;
4. builds `gruszka` with `cargo build --release --locked --offline -p gruszka -p susz`, the command of the Linux
   recipe, with the C compiler and the linker of the Lean toolchain (`cargo_build.py`, below);
5. stops if one of the four programs holds a folder of the machine as text, then compares the four programs with
   `pins.env` and stops, naming the ones that differ, if the build gave other bytes;
6. writes the record and prints the SHA-256 of the bytes it wrote. The comment lines of the record name Lean, Rust,
   macOS, the SDK and the selected developer directory.

**What cargo is given.** Only the checksums in `Cargo.lock` are trusted, and `Cargo.lock` is one of the fingerprinted
sources, so it does not matter where a crate archive comes from. Every archive must have the SHA-256 that
`Cargo.lock` names before one is unpacked. The recipe unpacks them itself, regular files inside the archive's own
folder only, and hands them to cargo as a directory source. cargo runs with a home and a target folder that are new
in the build directory, without a registry index and offline, in an environment that `cargo_build.py` writes: no
`RUSTFLAGS`, `CC` or `CARGO_*` variable of the caller reaches it. cargo also reads `.cargo/config.toml` in every
folder above the one it builds in, so the recipe stops if there is one above the build directory. The Rust toolchain
is checked by the line that `rustc --version` prints, not by a digest.

**What is done so that the program does not depend on the machine.** The build directory reaches `rustc` and the C
compiler as `/build` (`--remap-path-prefix`, `-ffile-prefix-map`), the toolchain as `/lean-tc` and the SDK as `/sdk`.
`rustc` gets its flag and the name of the linker through a wrapper, so that cargo, which forms the names of its
outputs from the flags, does not see the folder: the name under which the program is linked is part of its code
signature. The linker leaves out its list of the object files with their paths and times (`-S`). The link finds the
system library in the stub that the toolchain carries, not in the SDK, and a library that the program names and
does not use is not written into it (`-dead_strip_dylibs`): that is libiconv, which one crate names for every
program on macOS and for which `cargo_build.py` writes a stub of six lines. `SOURCE_DATE_EPOCH` is the one of the
Linux recipe, for the date that the C code of the allocator prints. A program that still names its build directory
is refused.

Every run gets a new directory `OUTDIR/build.XXXXXXXX` with the staged sources, the crates, the logs and `bin/`. Its
path may hold letters, digits and `. _ + @ -` only, because it is written into compiler flags. The programs stay
there: the record names them by absolute path. A build takes one to two minutes; the three Lean programs need about
600 MB of memory with one build job.

## Why an ACCEPTED is sound

**The legs are the legs of the Linux judges, built from the same sources.** No kernel source and no judge source is
changed or copied into this directory. The recipe builds exactly the trees whose fingerprints `pins.env` pins. The
Lean programs are linked from the unmodified libraries of the official v4.36.0 release (`libleancpp.a`, `libLean.a`,
`libStd.a`, `libInit.a`, `libleanrt.a`), so the kernel that decides is the kernel of the release itself: none of it is
compiled here. Nothing of the toolchain is loaded when a leg runs: the three Lean programs load only
`/usr/lib/libc++.dylib` and `/usr/lib/libSystem.B.dylib`, `gruszka` only `/usr/lib/libSystem.B.dylib`.
`ccmp-lowmem`, `pleanchecker` and `pleanchecker-lowmem` compute what
[check/lowmem/README.md](../../lowmem/README.md#why-an-accepted-is-sound) and
[check/sound/README.md](../README.md#why-an-accepted-is-sound) argue for them.

**The second kernel of both scripts is `gruszka`.** The ultra-low-memory judge of Linux runs `gruszka-lowmem`, the
same kernel with a disk-backed store and smaller worker tables. No such program is built here; the default second
kernel checks by the same rules and reads the export itself. Taking it removes no check and costs memory: it holds the
packed export in memory, runs after the replay has ended and never beside it, and ends without a verdict at the
memory limit when the memory is not there. The result says so in `basis`.

**The driver decides nothing about a proof.** It starts the legs and reads their ends by the rules of the script:

| leg | ACCEPTED needs | REJECTED is | everything else |
|---|---|---|---|
| comparison | exit status 0 and its line `Comparison and axiom check passed!` | exit status 1 and its first `error:` line | no verdict |
| official kernel | exit status 0 and a stdout that is its acceptance line and nothing else | exit status 1 and a rejection of its own: its rejection line first on stdout, the rejection of the quotient check after its acceptance line, or, with nothing on stdout, the exception that ended it before the replay (an export that does not parse) | no verdict |
| second kernel | exit status 0 and its line `accepted`, with no error or rejection beside it | exit status 1 and its `rejected:` line | no verdict |

**REJECTED needs a rejection that the program made.** With exit status 1, a line that reports a failure of the
machine or of the program itself makes a leg no verdict: memory, the stack, threads, a panic or an internal error at
the start of a line, and an error of the operating system in the words of Lean 4.36 (`... (error code: N, ...)`,
`end of file`) or of Rust (`... (os error N)`) anywhere in a line, also behind the 64 KiB that are kept of a long
one. A leg that prints such a line has not judged the export, and the answer is DECLINED with that line as the
reason. The rule about errors of the operating system applies to a leg that would otherwise be read as a rejection.
Acceptance is what it is in the scripts, exit status 0 with the acceptance line: the notes of a leg that accepts are
not searched for such texts, so that an hour of replay is not thrown away for a word in a note. A program that
cannot be started, that a signal ends, or that the guard stops or does not vouch for is no verdict either: the exit
status of a leg counts only when the guard's report and the guard's own exit status name the same one and the guard
reports no violation, and only then is a log of the leg read. The streaming replay's exit status 2 with its line
`Lean default kernel could not decide (no verdict)` is no verdict.

`tests/macos-judge/run.py` runs the scripts' own lines for the comparison and for the replay beside the driver, on
Linux too. Where the two differ, the driver gives no verdict:

| output of a leg | the Linux script | here |
|---|---|---|
| the replay ends with status 1 and Lean's stack failure, `(kernel) deep recursion detected, use ...` | REJECTED: its pattern for a stack failure ends after `detected` | no verdict |
| the replay ends with status 1 and `INTERNAL PANIC: out of memory` | REJECTED | no verdict |
| the replay ends with status 1 and an error of the operating system, as the exception that ended it or inside its rejection line (`interrupted system call (error code: 4, ...)`, `end of file`) | REJECTED | no verdict |
| the replay ends with status 1 and no rejection of its own: no output, progress lines only, another first line | REJECTED | no verdict |
| the replay ends with status 1 after its own acceptance line, without a rejection by the quotient check | REJECTED | no verdict |
| the replay ends with status 0 and its acceptance line beside other lines, or on stderr only | ACCEPTED | no verdict |
| the comparison ends with status 1 and an error of the machine that the scripts' list lacks (`permission denied`, `internal error:`, `short pread on export file`), names memory in a later line, or also prints its acceptance line | REJECTED | no verdict |
| the comparison ends with status 1 and an error of the operating system (`error: hardware fault (error code: 5)`, `error: end of file`) | REJECTED | no verdict |
| the second kernel ends with status 1 without a `rejected:` line, or with status 0 without `accepted` alone | REJECTED, ACCEPTED | no verdict |
| the second kernel ends with status 1 and a line that names an error of the operating system (`(os error 5)`) or an `error:` | REJECTED | no verdict |
| the second kernel declined for worker-table room, and its log holds a NUL byte or a byte that is not UTF-8 | a second run or none, by the `awk` of the system | with a NUL byte no second run and no verdict; other bytes are compared as they are |

The first row is deliberate: Lean 4.36.0 prints that text when the replay runs out of stack (seen with the built
program and a small stack), a failure of resources, which the scripts mean to be no verdict. The rows about errors of
the operating system have a price: an export can make a program print such a text inside a rejection (the name of a
declaration can hold it), and that export gets no verdict here where Linux says REJECTED. Neither is ACCEPTED.

**The rules of the judge scripts run as their own code where that is possible.** The configuration step (the
official comparator's reading of the config, permitted axioms, definition targets) is the Python text of the script
that was entered, located exactly and run unchanged; if it cannot be located, or has other arguments than the driver
knows, there is no verdict. The comparison is given the private configuration that the step wrote. One rule stands in
front of the step: a configuration with a number of more than 4,300 digits (an integer, or a numeric component of a
name) is no verdict, because the step refuses it under every Python that limits `int()` and the system Python of
macOS does not. The cross-version gate is `xvcheck.py` with `releases.json`, called and read as the scripts do. The
driver's own code follows the scripts for the remaining rules: the arguments, `--pins` and the caller's digests, a
path with a shell-special character, and the one-worker retry of the second kernel, whose condition `run.py` compares
with the wrapper each script writes. The rows of `run.py` that compare the driver with the scripts need no Mac and
run in CI, so a change of a judge script that the driver does not follow shows on Linux.

**No ACCEPTED without the self-tests in the same run, with the same programs.** Before the judged export is looked
at, all three legs must accept the known-good export, the comparison must reject the export with a custom axiom, and
each kernel by itself must reject the kernel-invalid export (`selftest-kbad.export`). The programs are compiled on
the machine, so a run does not rest on the digests alone: a rejection by each kernel is part of what it must see. A
control that ends any other way (a kernel that accepts, a crash, a limit) is no verdict.

**One program publishes, and only what it has examined.** On macOS the script replaces itself by `enter.py` with
one `exec`, so the process the caller started is the one that answers; before that it checks that its own path
resolves, that `/usr/bin/python3` starts and that `enter.py` is whole and loads: in an interpreter of its own, the
file is compiled and run under another name. So neither of its two blocks for a run starts, the one at its top with
the signal mask and the end handler and the one at its end, and what they do is not looked at. When the run of the
file has come back and its last statement has set a name, the interpreter prints `COMPLETE`, flushed, and ends with
exit status 0; an end handler gives every other way out of the look the status 1, and one that skips the handler
prints no word. The script wants that word alone on stdout and exit status 0: the file ran to its last statement,
and the interpreter said so. Any other end, whatever its status, is no hand-over: an exception that leaves the file,
an exit, an exit that skips the end of the interpreter. A file that is missing, does not compile, fails or exits in
its imports or definitions, is empty or is cut off at any place gets none, and the script says DECLINED itself. `enter.py` starts the driver as its child, with
a pipe on descriptor 3. The driver writes no result anywhere: it ends with a status of its own for each
verdict (40 to 43) and hands its whole result over on the pipe as its last act. `enter.py` publishes that result only
when the status and the result agree with each other, name the judge of the script that was entered, and answer what
was asked for, a judgement or a preflight. A positive result must also hold what it claims: the three controls with
their outcomes and, for ACCEPTED, the three legs with exit status 0. That is a second look at what the driver hands
over, not a second judgement. `enter.py` writes the `--json` file first, as a new file that is put in place in one
step, then the same line to stdout, and ends with the exit status of the verdict. For every other end (a driver that
is killed, an interpreter that fails, a status without a result, a result with another status or of the other script,
a positive result without its legs and controls, a failure of `enter.py` itself) it publishes a DECLINED of its own
with exit status 2. A result that cannot be written, to the file or to stdout, is DECLINED; a file that already
holds it and cannot be written again is emptied, through the descriptor it was written with, so also when its
folder and its mode no longer allow a change. The exit status is that of a verdict at one place only: in the last
block of `enter.py`, where `main` has returned and stdout has taken the line of one result, whose verdict gives the
status. Every other end, once `enter.py` has registered its end handler (with the signal mask, before its
definitions), has the status 2: the last block starts from it, and the handler gives it to every end outside that
block (an exception, an exit, the end of a file that is cut off below the handler). A signal before that is the
subject of the paragraph on signals below. A file that is changed between the look and the hand-over is outside
this, as is any change of the tree during a run.

**What a result is worth.** A verdict is the normal end of one invocation: its line on stdout together with the exit
status that the line names; the `--json` file, when one was asked for, agrees with them. A file alone establishes
nothing. A path that the command line names as `--json` does not go on holding a result that says more than this run
did: `enter.py` takes the result of an earlier run away when it starts, before it refuses anything, from every path that
is the value of a `--json`: the destination, one that a later `--json` replaces, and one behind an argument that ends
the reading. Which words those are is the reading of the driver, which gives every word a role: an option word; an
input, a file that the driver reads, which are the three inputs of a run that judges and the values of `--hints`,
`--hide` and `--pins` (but not `none` for the first two); the value of another option (`--threads 4`, a digest, a
folder); a value of `--json`; a value of `--log`. Where it refused a word, the roles of the words before it are known
and every word from the refused one on has an unknown role; where the driver cannot be read, every word has. Those words
are read as they stand, but never one of the three inputs. A word that follows a word `--json` is a value of `--json`,
whatever that `--json` is, and keeps nothing; a word `--json` is an option word only where it can be nothing else: the
first word without a role stands where an option name stands, and from there each word `--json` is the option and the
word after it its value, as long as the words at those places are `--json`. Every other word without a role keeps, also
a `--json`, which may be the value of an option that takes a file. So a word `--json` without a role outside that
leading chain keeps a destination that it names: `--bogus --json --json` keeps `./--json`, whose first `--json` may be
the value of `--bogus`; without a driver, `--threads 4 --json --json` keeps it too, since `--threads` stands where the
chain would start; and behind a refused value, `--log '' --hints --json --json ./--json` keeps `./--json`, the `--hints`
file, with the driver and without it. A slash at the end of a value of `--json` does not count, here as where the result
is written. It removes the file, or the symbolic link through which the path leads to one (the file behind a link is
neither written nor removed), and empties a file that it cannot remove, unless that file has another name, a hard link,
under which it would be emptied too. What it takes for a result is what this judge writes: a regular file of at most 1
MiB that holds one JSON object with the six fields every result has, `checker` (one of the two names of this judge),
`verdict` and `exit` (a verdict with its exit status), `wall_s`, `reason` and `wiring` (its one value,
`macos-sequential`). A file that has some of these keys, a comparator configuration with four of them, is none, and so
is a result of the Linux scripts, whose `wiring` is another value: a run that is declined before the driver has compared
the destination leaves it as it is. A path stays as it is if, and only if, another word whose role is an input, or
unknown, names the same file: the same path after resolving, or the same file where both exist, so a hard link, a
symbolic link and another spelling of the name count. Option words, the values of the other options, other values of
`--json` and the values of `--log` keep nothing, also where they are spelled like the path, and so does a word that
cannot be resolved or looked up (a loop of symbolic links, a name that is too long, a folder on its way that cannot be
searched): it names no file that the driver could read. So `--json --json` after the inputs takes an earlier result away
from `./--json`, with the driver and without it, and `--json --threads --threads 4` from `./--threads` where the driver
can be read (without it, the second `--threads` may be a file, and keeps it); `--json R R`, three inputs of which two
are R, keeps R, because R is an input; and after a refused argument, a word of unknown role that names the destination
keeps it, as `--bogus R --json R` after the inputs keeps R; but `--bogus --json R --json R` takes R away, since each R
follows a word `--json`, and so do `--json --json` and `--preflight --json R --json R` without a driver that can be
read. An input is never removed or emptied: if it reads as a result it stays as it was, and where it is the destination,
the run is declined for the two names of one file. Two things stay outside the rule, and the path then still reads as
the earlier result. One is a result that can be neither removed nor emptied: in a folder that cannot be written, one
behind a symbolic link, one in a file that cannot be written either and one in a file that has another name as well (a
hard link, which emptying would reach too); in any folder, one in a file that may not be changed at all (the flag
`uchg`). At the destination of the run, the run is then DECLINED (`cannot write JSON`) before it starts. At a `--json`
that a later one replaces, and at one behind an argument that is refused, the run goes on as it would without that word,
and the path keeps the earlier result: the run can still judge, and that path is never its reason for a DECLINED. The
other is an answer of the script itself, which reads no argument: its DECLINED with exit status 2 for a tree in which
`enter.py` is missing, cannot be loaded or is not whole. When `enter.py` cannot read the driver, it takes earlier
results away, says DECLINED and writes no file. On Linux a symbolic link at the destination is written through; here the
result replaces the link. A process that is killed between the file and the line leaves a file without a verdict, and
two runs with one destination write over each other: there is no lock, so one run per destination at a time. An exit
status without the line on stdout is no verdict either, whatever the status. With fewer than six file descriptors to
open the script itself can end that way, with exit status 2 or 127 or by an abort: bash 3.2 fails before the hand-over.

**The `--json` destination is never a file that the run reads.** Whether it may be written is decided once, when
`enter.py` starts, from the command line: not when it is the path of another word of the command line (an input, the
log, a record, the hints), existing or missing, compared after resolving, and not where the record of the programs
belongs. Then there is no run, and none when a word cannot be resolved (a loop of symbolic links), which the reason
says. This is wider than the rule of the scripts, which compare with the inputs: a destination spelled like the value
of another option is refused too. The driver compares the destination, like the log, with every file it reads (the
programs that the record names, the five self-test inputs that `pins.env` names, the wiring, the hints) as soon as it
has read the record and `pins.env`: by the resolved path, and by the file when both exist, so a symbolic link or a
hard link to one of them is refused too, and so is another letter case or Unicode form of its name on a volume that
takes them for the same. The file is looked up by the path as given and by the resolved path, so also behind more
symbolic links than the system follows in one look, which the driver's resolve follows to the file it reads; `enter.py`
compares in the same way. Two paths that do not exist yet can only be compared as texts; so the log and the JSON
destination are compared once more when the driver has made the log, and one new file under two spellings is refused
as one path. Where it refuses the destination, nothing is written there; where it refuses only the log, the JSON file
says so; and a refusal before that comparison is written as a new file only, never over one. Without a `pins.env` that
can be read and names all five self-test inputs, their places are not known: the destinations are still compared with
the other files, the run ends without a verdict, and neither has passed, so the log is not written and the JSON file
only as a new file. The lines of `enter.py` are written by a JSON encoder, and the name of the judge in them is a
constant.

**A run ends with the process the caller started.** TERM, INT and HUP for that process are passed on to the driver
as they come, and the driver stops the leg that runs. The answer is DECLINED when such a signal arrives before the
commit point: `enter.py` examines what the driver handed over, then blocks the three signals and looks whether one
was seen, immediately before the first write of a result. From there the result stands, whatever arrives. The three
are blocked from the first statement of `enter.py` until its handlers are set, and the driver starts with them
blocked until its own are set, so none is lost in between. One that arrives earlier still, from the start of the
script until `enter.py` has blocked them, ends the process by the signal and without a line. That holds for INT as
well, sent to the process alone or to its process group (Ctrl-C): bash does not drop an INT while it waits for a
command substitution, and the look at `enter.py` is one, like the two before it. One difference: an INT in the few
milliseconds while the interpreter of `enter.py` starts and imports its own modules ends it with exit status 1 and
no line, which is no verdict either. Measured on an M4, to the process and to the group alike: by the signal in the
first 100 ms and again from about 115 ms, exit status 1 between, and from about 165 ms the DECLINED of `enter.py`
for the signal. One rule holds for all
three: a signal that the caller ignores (`nohup`, a job in the background) is ignored by `enter.py`, by the driver
and by the legs, as on Linux. A driver that does not end within a minute, after the first signal that was passed on
or after it handed its result over, is killed, which is DECLINED; further signals do not put that off. When the
process the caller started is killed, the resource guard ends the leg that runs, the driver ends, and nothing more
is published.

**Nothing changes under a run.** The programs and the inputs are clones in the private directory of the run (mode 0500
and 0400), and their change stamps are compared before and after every leg. That directory is made in `--workdir`,
without the option in `/tmp`, and removed when the run ends; a clone takes no space on the volume of its file, and is a
copy of every byte on another volume, so `--workdir` belongs on the volume of a large export. `judge.py`, `support.py`,
`pins.env`, `enter.py`, the sandbox launcher, the guard, the judge script, `xvcheck.py` and `releases.json` are hashed
at the start and compared at the end (`wiring_sha256` in the result). The script hands over only after its
clean-environment step, and `enter.py` and the driver run under `python3 -I`; every program the driver starts gets an
environment the driver wrote. Files are created with umask 077; the caller's log is never written through a symbolic
link, and neither the log nor a file at the `--json` destination is written over before the path was compared with every
input. The log is a regular file or the null device (`--log /dev/null` discards it); the `--json` destination is a
regular file or a new one. Any other device is refused, and so is a descriptor (`/dev/fd/N`, `/dev/stdout`), which
is another file in the driver than in `enter.py`. All of this is said for a work directory and an installation (the
tree, the built programs, the record) that belong to the account of whoever verifies: stamps and digests show a
change between two checks, they do not keep out a process with the rights of that account.

**What binds a verdict to the bytes of the export.** As the Linux scripts, the driver does not hash the judged
export. It judges a private copy, whose change stamp (size, times in nanoseconds, inode) is compared before and after
every leg and at the end, and the result names its size. The challenge and the config are hashed
(`challenge_sha256`, `comparator_sha256`) and compared with `--challenge-sha256` and `--comparator-sha256` when the
caller gives them. Whoever must name the export by its bytes takes its digest before the run.

**What is started, and what vouches for it.**

| started | vouched for by |
|---|---|
| `ccmp-lowmem`, the replay program and `gruszka` | their SHA-256 in `pins.env`, compared with the clone that runs, before the first leg and after the last; for the two kernels also their rejection of the kernel-invalid self-test |
| `enter.py`, `judge.py`, `support.py` with `pins.env`, `lib/macos/sandbox-run.py`, `tools/guard/fvguard.py`, the configuration step of the judge script, `check/xversion/xvcheck.py` | the tree: tracked files, hashed at every run and named in the result |
| `/bin/bash`, `/usr/bin/env`, `/usr/bin/python3`, `/bin/cp`, `/usr/bin/uname`, `/usr/bin/readlink`, `/usr/bin/basename`, and the sandbox of `/usr/lib/libsandbox.1.dylib` | the operating system and its Command Line Tools; started by absolute path, never through `PATH` |

**The sandbox.** `lib/macos/sandbox-run.py` lets a leg read its program, its inputs and its own directory and write
only its own directory, without network. The record, a toolchain, the driver, the other inputs and the output files
of the legs lie outside, so a leg that an export has subverted cannot write another leg's answer. The launcher starts
the program itself, with the variables the driver names and no others. No shell stands in between: `/bin/sh` ends
with exit status 1, the status of a rejection, when it cannot start a program, while the launcher ends with 126,
which is no verdict. The log of the comparison holds `WARNING: Sandbox disabled, this run is not trustworthy.`, on
Linux too: it is the line of the official comparator for a run without its own sandbox, which the judge scripts
replace by one from outside, on macOS by this launcher.

**The memory limit of a leg.** A leg may use the physical memory of the machine, or less when the caller says so
with `--mem-budget-mb`; a value above the physical memory is refused. The guard stops a leg at the limit, and that is
no verdict: the reason says that the leg needs more memory than its limit and names the limit, the first line of the
log names it too, and the result holds what the guard measured of the leg (`legs.<leg>.ms`, `peak_footprint_bytes`).
On Linux the scripts put no limit on a leg: the bound is the machine or the caller's cgroup, and a leg that the system
kills is no verdict. macOS has no limit that its kernel enforces for a process tree, so the driver sets one and the
guard enforces it by looking: once a second it adds up the physical footprint of the processes of the leg that it has
seen, and it ends the leg when the sum is above the limit. The footprint also counts the pages of the leg that macOS
has compressed: it does not shrink when the system compresses. This bounds what a leg takes; it does not keep the
machine out of swap, and nothing here measures swap or the memory that is free. Without `--mem-budget-mb` the limit is
all the physical memory, and a leg that grows to it is stopped only after macOS has compressed or swapped out pages of
other applications and of the leg itself to make room. A caller who wants to protect the machine gives a lower
`--mem-budget-mb`, which also caps the workers as on Linux. The Riemann
Hypothesis export (61.6 GB) under `check-sound-ultralowmem.sh` with 12 workers on a Mac with 64 GB is the example:
13.2 GiB in the comparison, 36.5 GiB in the streaming replay and 28.7 GiB in `gruszka`. The comparison's own lines
`peak RSS N MB` are 1,024 times too large on macOS: its source, which is not changed, takes `ru_maxrss` for
kilobytes, and macOS gives bytes. The memory of a leg is `peak_footprint_bytes`.

**The resource guard.** `tools/guard/fvguard.py` starts each leg, passes its output on and reports its exit status;
it stops a leg at the time limit or the memory limit. Two things the driver takes from the guard as they are: the exit
status of a leg, and that the output is complete. The rest it checks itself: the exact acceptance line in the leg's
output, the programs' digests, the inputs' stamps, the self-tests. So a guard that fails (it stops a leg, dies, loses
output, reports another status) can only cost a verdict, because ACCEPTED needs status 0 together with the leg's own
acceptance line; only a guard that wrote that line itself could cause one, which is why the file is hashed with the
wiring at every run. A leg that could not be started (status 125, 126 or 127), that a signal ended or that the guard
stopped is no verdict, and so is output that the guard could not pass on completely (its violation `guard`). Three
things the guard does not do: a process that leaves the process group of its leg before the guard has seen it is
neither counted nor ended with the leg, though it stays inside the sandbox; the guard does not notice when its
watcher of the driver is killed, and the leg then runs on under the limits; and it measures the time limit on the
wall clock, so a `--timeout` can end a run when a laptop wakes from sleep. Each can only cost a verdict.

## The result

The JSON result has the fields of the script's result on Linux where they mean the same: `checker`
(`checkSoundLowMem`, `checkSoundUltraLowMem`), `verdict`, `exit`, `wall_s`, `reason`, `threads`,
`effective_threads`, `mode`, `version` and `toolchain` (from `pins.env`), `basis`, `binaries_sha256`, `legs` (`rc`,
`ms`, `message`, and `retry` of the second kernel), `inputs`, `private_inputs_asserted`, `pins`, `pins_sha256`
(the record of the machine), `hide`, `hide_sha256`. `wiring` is `macos-sequential` and tells a macOS result apart.
Not written: `ccmp_rc`, `leg_ms`, `compare_ms`. Added: `wiring_sha256`, `memory_limit_bytes`, `memory_limit_source`
(`physical memory` or `--mem-budget-mb`), `challenge_sha256`, `comparator_sha256`, `xversion`, `selftests`, and
`peak_footprint_bytes` of each leg. The line on stdout and the `--json` file hold the same bytes, both written by
`enter.py`. A DECLINED that `enter.py` makes itself has `checker`, `verdict`, `exit`, `wall_s`, `reason` and `wiring`
only; `json_error` is added to a DECLINED that could not be written to the file. Two lines have less: the last resort
of `enter.py`, for a failure of its own, has no `wall_s`, and the DECLINED of the judge script itself, before the
hand-over, has `checker`, `verdict`, `exit` and `reason`.

## Known limitations

- arm64 macOS and Lean 4.36 programs only; no `ccmp`, no extra veto kernels, no incremental replay, no kernels of a
  config; `check-sound.sh`, the service, notary and frontier scripts, the `fastverify` orchestrator and
  `fv_lowmem.py` give no verdict.
- The soundness gates of `tests/sound-gates` have no macOS harness. The check of a user's own build is
  `tests/macos-judge/programs.py`.
- A program is started by its path in the private directory of the run. The stamps of the clones are compared
  around every leg, the digests of the programs and of the self-test inputs before the first leg and after the last;
  unlike a bind mount, that does not fix the file for a process of the same user that exchanges the directory itself
  between two checks.
- Verdicts can differ from Linux by resources, never toward ACCEPTED by the content of an export: the memory limit
  of a leg, the stack of the arm64 programs, and the worker tables of `gruszka` under another worker count give no
  verdict on one side and a verdict on the other.
- The driver is stricter than the configuration step in two corners: a theorem name with a numeric component of more
  than 4,300 digits when the config lists no definitions, and a config nested deeper than the system Python's
  recursion limit allows.
- `check-sound-ultralowmem.sh` takes over what holds for the streaming replay `pleanchecker-lowmem`
  ([limitations](../../../../docs/limitations.md#assurance)): above its closure budget it gives no verdict, and the
  driver passes its line on as the reason. By design it accepts an export whose only defect is a loose bound variable
  in an unsafe inductive block: such a block is never handed to the kernel, its names are not in the checked
  environment, and the official replay accepts it too (`tests/lean-leg-record-checks/mk_c1only.py`). `pleanchecker`
  rejects such an export, and `programs.py` requires that the built `gruszka` does not accept it.
- The memory limit is enforced by polling once a second. A leg can exceed it for a moment, and the measured peak of
  a leg that ends within a second says nothing.

## Tests

- `tests/macos-judge/run.py`: the driver with stand-in programs, through both judge scripts (no Lean needed). On
  other systems it runs the rows that need no Mac; CI calls it.
- `tests/macos-judge/programs.py --work DIR --pins-sha256 DIGEST`: the built programs, alone and through the judge, on
  the attack exports and controls of this tree; SKIP without the record.
- `tests/macos-sandbox/run.py` and `tools/guard/test/test-fvguard-macos.py`: the sandbox launcher and the guard.
