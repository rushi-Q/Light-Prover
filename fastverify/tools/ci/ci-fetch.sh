#!/bin/bash
# tools/ci/ci-fetch.sh REPO_GIT LAST_COMMIT N ROOT [--paths "P1 P2 ..."]
#   Export the first-parent history window of a project for the CI benchmark: the N first-parent commits before
#   LAST_COMMIT plus LAST_COMMIT itself -> ROOT/commits/NNN-<sha12>/ (NNN = 000 for the base = oldest, ..., N for
#   LAST_COMMIT), one `git archive` per commit (no .git, nothing is run), and ROOT/commits/list.tsv
#   (index, sha, date, subject, changed paths). Only public git; no code of the project is executed here.
set -eu
REPO=$1 LAST=$2 N=$3 ROOT=$4; shift 4
mkdir -p "$ROOT/commits"
L=$ROOT/commits/list.tsv; : > "$L"
mapfile -t CS < <(git -C "$REPO" log --first-parent --format=%H -n $((N + 1)) "$LAST" | tac)
i=0
for c in "${CS[@]}"; do
  d=$ROOT/commits/$(printf %03d $i)-${c:0:12}
  if [ ! -d "$d" ]; then mkdir -p "$d.tmp"; git -C "$REPO" archive "$c" | tar -x -C "$d.tmp"; mv "$d.tmp" "$d"; fi
  ch=$( [ $i -gt 0 ] && git -C "$REPO" diff --name-only "$c^1" "$c" | tr '\n' ' ' || echo base)
  printf '%s\t%s\t%s\t%s\t%s\n' "$i" "$c" "$(git -C "$REPO" log -1 --format=%cI "$c")" "$(git -C "$REPO" log -1 --format=%s "$c" | tr '\t' ' ')" "$ch" >> "$L"
  i=$((i + 1))
done
echo "$ROOT/commits: $i commits"
