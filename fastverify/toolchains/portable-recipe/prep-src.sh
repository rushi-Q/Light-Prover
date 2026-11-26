#!/bin/bash
# prep-src.sh REPO COMMIT OUT git|nogit   - the source tree of a pinned toolchain exactly as the harness's ensure_toolchain made it
# (the benchmark harness's benchrun.py): tree of COMMIT, src/CMakeLists.txt githash pinned to the v4.33.1 release commit.
#  git   : OUT is a git repository whose HEAD tree = COMMIT's tree (so stage0's `git ls-tree HEAD stage0 --object-only` gives the
#          same stage0 githash d297d678... as the original builds of d5e35ef223 / s01zy, embedded in the stage1 .olean headers)
#  nogit : no repository (the original build of 7586a50cec ran git 2.34, which lacks --object-only -> EMPTY stage0 githash)
set -euo pipefail
REPO=$1 C=$2 OUT=$3 MODE=$4 STOCK=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
[ -e "$OUT" ] && chmod -R u+w "$OUT"; rm -rf "$OUT"; mkdir -p "$OUT"
git -C "$REPO" archive --format=tar "$C" | tar -x -C "$OUT"
if [ "$MODE" = git ]; then
  (cd "$OUT" && git init -q && git add -A -f && git -c gc.auto=0 -c maintenance.auto=false -c user.name=D21 -c user.email=d21@localhost commit -q -m "tree of $C" && \
   [ "$(git rev-parse HEAD^{tree})" = "$(git -C "$REPO" rev-parse "$C^{tree}")" ] && echo "tree ok $(git rev-parse HEAD^{tree}) stage0 $(git rev-parse HEAD:stage0)")
fi
python3 - "$OUT/src/CMakeLists.txt" "$STOCK" <<'PY'
import sys
p, stock = sys.argv[1], sys.argv[2]; s = open(p).read()
old = 'get_git_head_revision(GIT_REFSPEC GIT_SHA1 ALLOW_LOOKING_ABOVE_CMAKE_SOURCE_DIR)'
assert s.count(old) == 1, 'githash line not found exactly once'
s = s.replace(old, old + '\n  set(GIT_SHA1 "%s")  # bench: pinned githash' % stock)
open(p, 'w').write(s)
PY
echo "$C $MODE $(date -u +%FT%TZ)" > "$OUT.SRCINFO"; git -C "$REPO" log -1 --format=%ct "$C" > "$OUT.SDE"; echo "src ok: $OUT"
