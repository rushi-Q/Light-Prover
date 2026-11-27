# Build stage (`build/`)

The build stage turns the project's sources into `.olean` files for the export. It is untrusted: the judge checks the
export, so a build bug can cost a verdict but cannot produce an ACCEPTED for an invalid proof.

## Options

| option | what it does |
|---|---|
| B0, official build (`official-build.sh`) | `lake build C` of the release toolchain named by `lean-toolchain`, C = the configured module as the comparator spells it, in a sandbox (read-only `/`, home hidden, no network, clean environment), dependencies read-only from the trusted workspace |
| B1, exact fast build (`build.sh`) | runs exactly the `lean` processes `lake build` would start, with a DAG scheduler instead of Lake's job engine. A planner compiled against the release's own `libLake` (`planner/Planner.lean`) computes the module set, each `lean` argv, `setup.json` and `LEAN_PATH` with Lake's code; sources are re-hashed before each `lean` and every output is fingerprinted. Any module error fails the build |
| B2 | B1 with early release of dependents and critical-path priorities |
| B3 | B2 plus untrusted build items, used by `--preset sound` and `sound-auto` (`--unsafe LIST`): module merging, skipping the build-time kernel check, linters off, the zygote (a `lean` that holds Mathlib in memory and forks one process per module), cost and check-tail hints from earlier runs (`hints/`), and others. Outside sound mode a result that used them is labelled UNSAFE |

Which projects get a fast build, and the exact rule for falling back to B0:
[which build runs](../../docs/reference/options.md#which-build-runs). The items and what each can break:
[build items](../../docs/reference/options.md#build-items---unsafe-list-b3). On Lean 4.33.1 the planner is an exact port
of Lake; on 4.36.0 and 4.37.0-rc1 (`planner/Planner435.lean`) only B3 with the sound presets runs.

## Residual differences

The verdict-relevant inputs of every `lean` process are identical to `lake build` (argv, `setup.json`, environment, working
directory, `LEAN_PATH`, sources and imported `.olean` files, resource limits, sandbox). Project code that inspects the
machine can still see the parent process, the absence of Lake's bookkeeping files (`.trace`, `.hash`, `.log`) and the
number of concurrent `lean` processes; its export is judged like any other.

## macOS

On macOS (Apple silicon, Lean 4.33.1) B0 to B3 run natively, with the same scripts. They need macOS 15.4 or later (by
Apple's published sources: `date +%s.%N`, with which the scripts take their times, came with 15.4; the call with which
the guard signals a process came with 14.2; `readlink -f` came with 12.3; tested on macOS 27.2 only), the developer
tools (`/usr/bin/python3`, `xcode-select`; the Xcode Command Line Tools or Xcode, both tested) and the release
toolchain as elan installs it; `tools/configure.py` then writes the toolchain's macOS pins
(`config/components.macos.json`) into `config/components.json`. `lib/macos/stage.sh` supplies what the scripts take
from Linux:

| Linux | macOS |
|---|---|
| bwrap sandbox | a sandbox profile that denies by default (`lib/macos/sandbox-run.py`, which lists what it allows): the project writable, for the planner and the plan check also their output directory; the toolchain, the dependency packages and the developer tools readable; no network |
| dependency packages bind-mounted into the project | links into the trusted packages workspace, made once before project code runs and checked before every sandbox start; `LEAN_PATH` may name such a checkout |
| `--die-with-parent`, `timeout` | `tools/guard/fvguard.py` ends the build with its stage, at `--timeout`, and when its processes use more memory than the machine has (no verdict) |
| `nproc`, `MemAvailable`, cgroup limits | `lib/budget.py host`: the available memory and, from it, the default worker count `build_jobs` (below) |

Available memory is what macOS can hand out without compressing or swapping anything: the free, the file-backed and
the purgeable pages (`lib/budget.py`, `darwin_memory_estimate`), as `MemAvailable` on Linux. The figure is conservative
on purpose: macOS could give more by compressing idle applications, and that is the owner's decision. From it follow
the scheduler's rule to start a further worker only while 8 GB, or a quarter of the machine's memory if that is less,
are available, and the default worker count, `(available - reserve) / 2 GiB` with a reserve of 4 GiB (an eighth of the
memory if that is less), at least 1 and at most the number of CPUs. The figure is not the limit of a running build: it
moves by gigabytes within minutes, and a limit taken from it once would end a long build that the scheduler's rule
keeps within what is available. The guard's limit is the machine's memory: a sandbox start whose processes have a
larger physical footprint is ended as a whole (no verdict), not one worker of it.

What differs:

- The profile hides no path, as a mount namespace does. Of a file outside its grants a build can read the metadata
  (that it exists, its size and times, and of a symbolic link the text it holds), not the contents and not a
  directory's listing. `/etc`, `/usr/share`, `/dev/stderr` and `/dev/fd/N` cannot be opened, and the clock is UTC.
- The profile language has no rule for two things. A build can create System V shared memory, semaphores and message
  queues; it cannot attach to one, use one or remove one, so such an object stays after the stage, until `ipcrm` or
  a restart. And it can ask for the process group, session and priority of any process id.
- `HOME` and `TMPDIR` of the build are a private directory made next to the project for each sandbox start (Linux:
  `/tmp/home` in a tmpfs). It is removed when the sandbox ends, also when the stage is killed.
- An access the sandbox refuses is no verdict (`ERROR` from B0, `DECLINED` from the fast build) when the system's
  message for it ("Operation not permitted", "Permission denied") reaches the build's output: Linux hides such a path,
  mounts it read-only or holds it in a tmpfs, so the same build could pass there. A project that catches the refusal
  and fails with words of its own is `FAILED`.
- The guard follows the build's process group and the descendants of the build. A process that leaves both before the
  guard has sampled it once (a daemon: `setsid`, then its parent exits) is not counted for the memory limit and does
  not end with the stage. It runs on inside the sandbox profile, where it can write to the project and nowhere else.
  On Linux no process outlives the sandbox's PID namespace.
- A dependency's destination inside the project must not exist, and the project is not built if it ships a
  directory there (Linux mounts over it).
- `--targets` (B0) needs the pinned Lean 4.36.0, which spells the module name as the official comparator does; without
  that pin there is no build (`ERROR`). `--require-modules` is refused (`DECLINED`): its resolver reads
  `lakefile.toml` through `/proc`. The orchestrator (`bin/fastverify`), which passes both, is not supported on macOS
  in this version: the stages are run one by one.
- The merge planner, the premise-off generator and the `LEAN_PATH` check run outside the sandbox, as on Linux. One
  differs: the merge planner opens a source file with `O_NOFOLLOW_ANY` and then checks that it is a regular file
  (Linux checks an `O_PATH` descriptor first), so a source that is reached through a link is not merged.
- `--unsafe` items: `toolchain-T1` is refused (the unofficial toolchains are Linux builds), the `zygote` items are
  dropped (they need such a toolchain), and `native-pkg` has no effect (its helper needs bwrap).

## Tests

`test/macos.py [WORK]` (about 2 min, macOS only): a project with a dependency package, the rules of its link, `--timeout`,
a killed stage, a refused access, the private directory, the options and helpers that differ. `run.sh`, `merge.sh`,
`premiseoff.sh` and `crash-retry.sh` run on macOS as they are; `zygote.sh` has nothing to test there.

`test/run.sh [WORK]` (about 2 min, no Mathlib): small projects built by B1 and B2 are byte-identical to the sandboxed
`lake build`; self-modifying sources, sources changed during the build and tampered `.olean` files decline; B3 runs and is
labelled `exact: false`. `test/cmp_official.sh PROJECT_SRC FRESH_WORK PACKAGES_WS [TC]` compares any project with the
official build (`CMP: SAME`, `DIFFERENT` or `DECLINED`). `test/zygote.sh`, `test/merge.sh` and `test/premiseoff.sh` test
the corresponding items.
