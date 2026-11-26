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

## Tests

`test/run.sh [WORK]` (about 2 min, no Mathlib): small projects built by B1 and B2 are byte-identical to the sandboxed
`lake build`; self-modifying sources, sources changed during the build and tampered `.olean` files decline; B3 runs and is
labelled `exact: false`. `test/cmp_official.sh PROJECT_SRC FRESH_WORK PACKAGES_WS [TC]` compares any project with the
official build (`CMP: SAME`, `DIFFERENT` or `DECLINED`). `test/zygote.sh`, `test/merge.sh` and `test/premiseoff.sh` test
the corresponding items.
