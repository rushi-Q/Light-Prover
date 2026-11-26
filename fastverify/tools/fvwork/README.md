# Per-repository daemon (`tools/fvwork/`)

`fvwork` is a daemon per (repository, challenge) for the edit loop: an editor hook, a proving agent, a CI job or many
agents send it project states (a working tree, a git revision or a set of changed files), and it answers each with the
sound verdict of the whole project plus compiler feedback. Opt-in; no preset or trusted file changes. Usage:
[user guide](../../../docs/user-guide.md#re-verify-on-every-edit); limits:
[limitations](../../../docs/limitations.md#services).

**v0.1 runs the cold sound path.** Every request runs `bin/fastverify --preset sound` on exactly the submitted tree (the
top-level `.lake` excluded, as in a direct run), with the challenge and comparator pins given to `fvwork init`. Nothing of
the base, earlier requests or a memo is reused, so a request costs about a cold run of the project. The incremental
machinery is EXPERIMENTAL (see below).

```
fvwork.py init  --state S --project P --challenge C --challenge-sha256 H --comparator-sha256 H2 [--packages WS] [--threads N] [--closure-only]
fvwork.py serve --state S [--jobs K] [--job-threads N] [--pins check/sound/pins-437.env] [--guard SPEC|none] [--slow-lane SEC]
fvwork.py verify --state S (--tree DIR | --git REPO --rev REV | --files CHANGES.json) [--no-advance | --merge] [--stream] [--label L]
fvwork.py watch --state S --tree DIR [--interval SEC] [--initial]
fvwork.py status|stop --state S
```

- `init` runs a cold `bin/fastverify P C S/cold --preset sound --keep-work` (or adopts such a run with `--adopt OUT`) and
  runs the cross-version gate on the pinned challenge export. Both pins are required. A project whose fast build hands off
  to the official build (a root `lakefile.lean`, a `lean_lib` with globs) also gets a state if the run reaches a sound
  verdict (ACCEPTED or REJECTED); otherwise no state is made.
- Keep `S` on a local file system, not under `/home` or `/tmp` (both are hidden in the kernel sandbox). A `--git`
  repository may lie anywhere: the git sandbox binds it read-only.
- `--git REPO --rev R` runs `git archive` in a sandbox without network: a partial (blobless) clone fails with an error
  instead of giving a truncated tree. Use a full clone or `--files`.
- `verify` exits 0 ACCEPTED, 1 REJECTED, 2 no verdict; the answer's `"exit"` is the same. For rewards and merge gates,
  everything but 0 counts as not accepted.
- `watch` verifies on every save and prints `file:line:col: severity: message` lines.

## Many agents on one repository

`--jobs K` runs K requests at once, each with `--job-threads` (default threads / K). Requests that may move the base
(the default, or `--merge`) are serialized by a merge lock and judged on the base current at their turn; with `--merge` a
tree enters the base only if ACCEPTED. Candidates (`--no-advance`) run concurrently. `--slow-lane` (default 120 s): a
longer request stops counting against `--jobs`. `stop` or SIGTERM ends every in-flight build, export and check; their
answers are NO-VERDICT.

## Protocol

One JSON line per connection on the Unix socket `S/sock` (mode 0600, same user only):
`{"op":"verify", "tree": DIR | "git": REPO, "rev": REV | "files": {"rel/path.lean": "content" | null}, "advance": true,
"merge": false, "stream": false, "label": "..."}`, `{"op":"status"}`, `{"op":"stop"}`. With `"stream": true`, event lines
(`start`, `build` with per-module diagnostics, `export` with the sha256, `check` with verdict and reason) precede the final
line, which has `"final": true` and carries `verdict`, `exit`, `why`, `basis`, `trust`, `export_sha256`,
`challenge_sha256`, the stage times and `source`.

## Why the daemon cannot create an ACCEPTED

- The verdict is that of the trusted check on the export of this request; the daemon only maps its exit status to a word.
- Everything else is untrusted and can only lose a verdict: source materialization, scheduling and the request queue.
- The challenge export is the daemon's private 0400 copy, compared with its pin before every check; the comparator
  configuration is the private copy taken at `init`. Exports are written into the private state directory (0700).
- Project code is elaborated only in the build sandbox. `git archive` and its extraction run in a sandbox where only the
  fresh source directory is writable. `files` paths are confined to the source directory: no `..`, no absolute paths, no
  writes through symlinks, nothing under `.lake` or `.git`.
- `--guard SPEC` (default `wall=3600`; `none` turns it off) runs every untrusted build and export under
  `tools/guard/fvguard.py`, for example `mem=64G,procs=4096,wall=1800,out=64M`. A violation kills the tree and the answer
  is NO-VERDICT. The trusted check is not wrapped.

## EXPERIMENTAL: incremental machinery

`serve --experimental-incremental` enables reuse of the last build tree (`--mode full|optimistic|interface`), the
frontier check (`--check frontier`, with `--allowed` and `--pinned`), `--build lake` states, `--copy-mode
hardlink|farm`, `--reuse-identical` and statement-drift reports (`--expdiff`, `--drift`). It is not claimed sound, and
none of its ACCEPTED or CONDITIONAL answers counts: they are reported as NO-VERDICT (exit 2) with `"provisional"` and
trust `none`. Without the flag, `serve` refuses `--check frontier` and `--build lake` states. A state made from an
official-build base serves the cold path only; `--experimental-incremental` refuses it. `--check warm` (the warm delta
judge) is not in v0.1 and is refused.

`replay.py`, `mkedits.py`, `simfill.py`, `simfill_select.py` and `edits2trees.py` generate and replay edit streams for
benchmarks of this machinery.
