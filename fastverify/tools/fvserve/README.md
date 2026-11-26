# Attempt service (`tools/fvserve/`)

`fvserve` is a daemon for provers that submit single proof attempts against a fixed problem set (attempt, verdict,
feedback loops, best-of-N sampling, RL rewards, evaluation). Each attempt gets a verdict (ACCEPTED, REJECTED or
NO-VERDICT), the compiler output and stage times. Opt-in; no preset or trusted file changes. For rewards, count
NO-VERDICT like REJECTED. Usage, profiles and HTTP access: [user guide](../../../docs/user-guide.md#serve-proof-attempts-to-provers-and-rl-pipelines);
throughput: [benchmarks](../../../docs/benchmarks.md); limits: [limitations](../../../docs/limitations.md#services).

```
tools/fvserve/fork/build.sh TC FORKDIR          # optional compile worker, built with the official toolchain TC
tools/fvserve/fvserve.py serve --state ST --pset NAME=PSETDIR:SHA256 [--pset ...] --packages WS --toolchain TC \
    --threads N [--profile shared|laptop] [--fork-server FORKDIR/fvfork] [--pins check/sound/pins-437.env]
tools/fvserve/fvserve.py submit --state ST --pset NAME --theorem T attempt.lean     # one JSON verdict
tools/fvserve/fvserve.py stats|stop --state ST
```

`PSETDIR` holds `challenge.export`, the official export of a challenge that states every problem with `:= sorry`, and
`comparator.json` listing all problems. An attempt is a complete module that declares `theorem T`. Protocol: one JSON line
per connection on the Unix socket `ST/sock` (mode 0600): `{"op":"verify","pset":..,"theorem":..,"source":..}`,
`{"op":"stats"}`, `{"op":"stop"}`. Clients must keep the connection open until the answer arrives; an attempt whose
client is gone is dropped before any work. `--packages` defaults to `$FV_PACKAGES`, else
`<repository root>/verify/challenge`; without either the service refuses to start. `fvclient.py` (`seq`, `burst`,
`bestof`, `stream`) and `bench/loop.py` are benchmark clients; `bench/setup.sh ROOT FV WS` regenerates their inputs.

## What it saves

| fixed cost per attempt | without the service | with it |
|---|---|---|
| package and exporter preflight | ~2 s every run | once at start |
| header `import Mathlib` | 2-4 s per `lean` (0.5-1.4 s with the official `--incr-load` snapshot) | loaded once by the fork server; compile 0.5-0.7 s per attempt, of which ~0.35 s is the official `writeModule` |
| judge integrity checks (pins, toolchain tree) | ~3 s of a 3.4-4.0 s check | `--svc-check`: full check at start, then a stamp comparison; check 0.9 s |
| export and check | one per attempt | attempts of different theorems that wait together share one export and one check |

## Why the service cannot create an ACCEPTED

- The verdict logic is `tools/batchverify.py`'s, unchanged: ACCEPTED only if a trusted judge run exited 0 with a
  configuration that lists the theorem, and the theorem is credited to its own attempt.
- The judge is `check/sound/check-sound.sh`, or with `--svc-check` `check-sound-svc.sh`: the same judge, self-test and
  verdict mapping, with the per-run re-hashing of pins and toolchain tree replaced by a stamp comparison against a record
  written after a full verification. A changed pinned file changes its ctime or inode and triggers a full verification.
- Each problem set's challenge export is copied into the private state directory (mode 0700) and compared with its pin
  at start and before every check. Exports go to a private 0700 directory, one file per batch.
- Untrusted, so each can only lose a verdict: the queue, batching, the isolation of suspicious attempts (those mentioning
  `sorry`, `axiom`, `native_decide`, `unsafe`, `addDecl`, `run_cmd`, ... are checked alone), the fork server and the
  exporter call.
- Attempts are elaborated only in bubblewrap without network (read-only `/`, home hidden, environment cleared). The fork
  server runs in the same sandbox with only the batch directory writable, and each forked child restricts its writes to
  its own output directory with Landlock.

## Fork server (`fork/`, untrusted)

`fork/FvFork.lean` and `fork/shim.c`, built by `fork/build.sh TC OUT` with an official toolchain (4.33.1 or 4.37.0-rc1;
Linux 5.13 or later for Landlock). It links against the toolchain's `libleanshared` like the official `lean`, loads the
official `lean --incr-header-save` snapshot of the header once as `Lean.Elab.runFrontend` does, and forks one child per
attempt that runs the rest of `runFrontend`. Three private helpers of `Lean/Elab/Frontend.lean` (v4.33.1) are copied and marked
(Apache 2.0). On the tested attempts its `.olean` files are byte-identical to those of the official `lean --incr-load`;
a child takes 18-68 ms of elaboration on competition proofs plus ~0.35 s of `writeModule`. A worker built for another
toolchain is not started. If the worker dies it is restarted (at most once per 10 s) and the attempt at hand is compiled
by the official `lean`. A compile failure under the snapshot or fork server is re-compiled by plain `lean` before it can
become REJECTED: on 4.33.1 and 4.37.0-rc1 only failures without an error at an attempt position, on other releases every
failure; `stats` counts these (`confirm_plain`, `confirm_flips`). On 4.37.0-rc1, 1,944 real model attempts were run with
every failure re-compiled: 0 of 992 failures flipped. See also [PROVENANCE](../../PROVENANCE.md#5-other-pinned-components).

## Isolation and memory

- `--profile shared` and `--profile laptop` expand to measured option sets (later flags override); the expansion is in the
  [user guide](../../../docs/user-guide.md#share-one-verifier-limits-and-isolation).
- `--limits SPEC` runs every compile under the guard (`tools/guard/fvguard.py`); a limit hit is NO-VERDICT. A compile
  killed by SIGKILL (OOM killer, cgroup limit) is NO-VERDICT too. A forked child that exceeds `--attempt-timeout` is killed
  with its process tree.
- `--max-pending N` and `--max-pending-per-client N` answer NO-VERDICT "queue full" when the queue is full;
  `--request-timeout S` is a total deadline for the request line.
- `--slow-after S --max-slow N` moves long batches to a slow lane. With 24 concurrent agents and 5 % runaway attempts, the
  p99 latency of honest attempts went from 29.5-37.9 s to 11.1-13.6 s (9.9 s without runaways).
- `--fair` batches per client round-robin (the request's `"client"` field, else the connecting process). With 15 agents
  and one client submitting 400 attempts at once, the agents' p90/p99 during the burst went from 46.5/50.8 s to
  8.4/10.0 s.
- Memory (16 hardware threads, 8 agents, the whole service in one cgroup): about 1.7 GB plus 3.1 GB per batch in flight.
  `--max-inflight 1` peaked at 4.8 GB, the default `--max-inflight 4` at 14.1 GB; under a 12 GB cap the default
  configuration was OOM-killed. Use `--max-inflight 1` on 8 GB machines and at most 2-3 on 16 GB.
- `stats` reports `code` (sha256 of the loaded `fvserve.py`, `batchverify.py`, `fvguard.py` and fork-server binary) and
  `stale` (those changed on disk since start); restart when `stale` is not empty.

## Lean 4.37.0-rc1

Pass a 4.37 `--toolchain`, a 4.37 `--packages` workspace and `--pins check/sound/pins-437.env`; build the fork server
with the 4.37 toolchain. On machine C (12-problem corpus on Mathlib `31ce06ea`, 6 concurrent clients), all 18 verdicts
matched the official 4.37 flow (12 honest attempts ACCEPTED, 6 cheat variants REJECTED by the 4.37 judge), all 18 were
compiled by the 4.37 fork server, at about 5 s per attempt. `tools/batchverify.py --pins` gave the same verdicts.

## Tests

`test/test-fvserve.sh`.
