# `bin/fv` (`tools/cli/`)

`fastverify/bin/fv` is the everyday command line. It wraps `bin/fastverify`, the standalone judges, the services and the
advisory tools; it adds no trusted code, and every verdict comes from the unchanged judge. `fv_cli.py` here is its
implementation. `bin/fv` starts it with an empty environment except `HOME`, `USER`, `TMPDIR`, `FV_CLI_ROOTS` and
`FV_EXPERIMENTAL_CI`.

```
fastverify/bin/fv doctor [--project DIR]
fastverify/bin/fv verify PROJECT --challenge DIR --challenge-sha256 HEX --comparator-sha256 HEX [--json-out FILE]
fastverify/bin/fv check EXPORT --challenge DIR --challenge-sha256 HEX --comparator-sha256 HEX [--low-mem | --frontier]
```

The synopsis of every subcommand (`verify`, `check`, `attempt`, `init-challenge`, `doctor`, the advisory `audit`,
`lookup`, `diff`, `mint`, and the EXPERIMENTAL `watch`, `triage`, `ci`) and the exit codes are in the
[command-line reference](../../../docs/reference/cli.md#binfv); the output formats are in
[result JSON](../../../docs/reference/result-json.md). The rules below apply to all subcommands.

## Paths

Paths are checked without being resolved: each is made absolute, normalized lexically, mapped onto the longest anchor
(the current directory, a directory listed in `FV_CLI_ROOTS`, else `/`) and walked from there with `O_NOFOLLOW`. A symlink
below the anchor is refused (exit 2, ERROR). Set `FV_CLI_ROOTS` (`:`-separated, matched as written) for a workspace you
reach through a symlink of your own.

- Inputs are judged as private copies made from the opened files; outputs (`--json-out`, `--sarif`, `--lsp-out`,
  `--reading-set`, the output directories of `init-challenge` and `mint`) are created without following links.
- `--pins`, `--toolchain`, `--state`, `--fvserve-state`, `--build-cache`, `--cache-dir` and `--incr-base` are checked the
  same way; `--cache-dir` and `--incr-base` may contain no symlink or special file at all.
- A `lakefile.toml` whose path keys leave the project is refused. A `.git` file (worktree or submodule checkout) is
  skipped and never followed; a `.git` symlink is refused.
- Without `--packages`, `fv verify` and `fv ci` use the challenge directory as the packages workspace when its
  `.lake/packages` is a real directory, read-only and in place.

## Errors and output files

- Exit 1 always means REJECTED. Usage errors, invalid inputs, an unavailable service and internal failures exit 2; with
  `--json` the error is printed as an `ERROR` envelope (`verify`, `check`, `attempt`, `watch`) or as
  `{"ok": false, "error": ...}`.
- If a requested output file or stdout cannot be written, the command reports ERROR (exit 2) whatever the judge decided,
  and every output file that can still be written gets the same `ERROR` envelope. No output file keeps a verdict that the
  exit status does not report, including a verdict from an earlier run.
- `--quiet` (`verify`, `check`, `attempt`) writes nothing to the terminal; results go only to the output files and errors
  to stderr.

## `fv check --timeout S`

`S` is passed to the selected judge's own `--timeout`, and its scope differs per judge. Sound judge (default) and
`--notary`: it bounds each judging step after setup and self-test, so the whole command can take longer than `S`.
`--low-mem`: one budget counted from the judge's start, so setup and self-test are included. `--frontier`: `S` applies to
each stage and to each inner sound-judge run. An expired timeout gives DECLINED (exit 2). To bound the whole command, use
`--guard wall=S`.

## Signals and invocation

- SIGTERM, SIGINT or SIGHUP is forwarded to the running child (`bin/fastverify`, the judge, `fv-ci.sh`), which stops and
  records the interruption; `bin/fv` waits up to 60 s, then kills it, and reports ERROR (exit 2). Children also receive
  SIGTERM if `bin/fv` is killed.
- Run `fastverify/bin/fv` directly, never `bash fastverify/bin/fv`: run as `bash FILE`, bash applies the caller's
  `BASH_ENV` and `SHELLOPTS` before the script's first line, which the `#!/bin/bash -p` line otherwise prevents.
