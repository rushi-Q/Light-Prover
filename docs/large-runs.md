# Running large verifications

How to run `fastverify` on a project the size of the Riemann Hypothesis proof (RH) on one large host: deploy and
preflight, run, what to watch in `result.json`, and what to do when something goes wrong. Options and verdict rules:
[reference](README.md#reference); measured results: [benchmarks](benchmarks.md).

Variables: `$FASTVERIFY` = this package's root (keep the same absolute path on every host, so `config/components.json`
and every stage's pins stay valid); `$HOST` = the large host; `$SCRATCH` = a local scratch directory.

## 1. Deploy and preflight

```
fastverify/tools/deploy.sh $HOST [SRC_NODE]
```

Copies the package to the same absolute path on `$HOST` by a directory swap (a live copy is never edited in place,
because bash reads a running script incrementally), mirrors the pinned binaries, verifies every `SHA256SUMS` there and
runs `bin/fastverify --preset sound --preflight-only` on `$HOST`. Start only after `fastverify: preflight OK`, and re-run
it after any change of the package or of a binary. The preflight checks `bwrap`, `git`, `/usr/bin/python3`, the official
toolchains (whole trees, file by file), the official exporter, the clean challenge and the judge's pinned files and
self-test inputs.

Host settings: `vm.max_map_count` above the number of modules the main module imports (RH: at least about 192,000), and
memory for the judge as in the [machine-budget table](benchmarks.md#judging-an-export-by-machine-budget).

Optional smoke test of the whole chain (seconds): copy `$FASTVERIFY/tests/011-*/x/proj/b` and `.../x/challenge` to
`$SCRATCH/fv-smoke/` and run `$FASTVERIFY/bin/fastverify $SCRATCH/fv-smoke/b $SCRATCH/fv-smoke/challenge
$SCRATCH/fv-smoke/out --preset sound-auto --threads 16`; it must end ACCEPTED.

## 2. Run

```
nohup $FASTVERIFY/tools/rh-sound.sh OUT [THREADS] > run.log 2>&1 &
```

`tools/rh-sound.sh` runs `bin/fastverify RH_PROJECT RH_CHALLENGE OUT --preset sound --threads THREADS
--no-build-fallback` with the pinned RH challenge and comparator pins, `--export-dir /dev/shm` when at least 256 GB are
free there, and `--reference-export $RH_REF` when `RH_REF` names an original-Lean export; at the end it prints the verdict,
trust, basis, export sha256 and stage times. `RH_PROJECT` and `RH_CHALLENGE` override the default locations next to the
package. For any other project: `bin/fastverify PROJECT CHALLENGE OUT --preset sound --challenge-sha256 HEX
--comparator-sha256 HEX`, or `--preset sound-auto`, which chooses the build items, threads and judge for the project
and host. OUT must not exist; to repeat a run, use a new OUT.

## 3. What to watch

`OUT/result.json` is rewritten atomically after every stage; `run.log` has the stage log lines. The deciding fields are
`verdict`, `trust` (`sound`), `verdict_basis` and `checks.sound` (each kernel leg's exit status and time in
`stage.legs`). `stage_seconds` gives the wall time per stage, `build.mode` and `export.mode` whether the fast build and
the native exporter ran, `export.sha256` and, with a reference export, `export.reference.identical`. Field definitions:
[result.json](reference/result-json.md).

## 4. Memory and host limits

- The untrusted export goes to `/dev/shm` only with at least 256 GB free there and, for the sound presets, a memory
  budget of at least 512 GB: tmpfs pages are unreclaimable RAM next to the judge. Otherwise it is written to OUT.
- With less memory, `--preset sound-auto` switches to the low-memory exporter and judge; the ultra-low-memory judge
  `check/lowmem/check-sound-ultralowmem.sh` is run directly ([check/lowmem/](../fastverify/check/lowmem/README.md)).
- Inside a cgroup or CPU affinity set, give `--threads N`: Lake sizes its job pool by the host's hardware concurrency, and
  `build/official-build.sh` passes N as `LEAN_NUM_THREADS`.
- A `lean` of the official build killed from outside (OOM killer) or a full disk is a host failure: ERROR, never
  REJECTED. On very large Lean 4.37 trees Lake's setup records alone can take hundreds of GB of disk.

## 5. If something goes wrong

- `verdict = ERROR` with `verdict_basis` "refused ...": a pinned component, an input or a host limit is not as expected and
  nothing was judged; read `verdict_basis` and the tail of `run.log`.
- Build declined (`build.attempts[0].stage.detail`): with `--no-build-fallback` the run stops with ERROR; without it the
  official `lake build` runs, which takes many hours on RH.
- The run can be killed at any time. It never leaves a verdict it did not reach: `result.json` says what finished, and an
  interrupted run records `interrupted` and exits 2.
- A component validated up to N threads caps itself at N: the native exporter, for example, runs with at most 128
  threads (256 when it writes to tmpfs).
