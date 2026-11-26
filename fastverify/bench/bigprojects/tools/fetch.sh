#!/bin/bash
# fetch.sh NAME [ROOT] : clone the project of projects.tsv (public git, outside any sandbox: no code is run), export the pinned
# commit to ROOT/projects/NAME (no .git), apply the documented port (lean-toolchain v4.33.1, manifest mathlib rev 0df444a,
# per-project edits) and copy the challenge to ROOT/projects/NAME-challenge. Nothing is built here.
set -eu
H=$(cd "$(dirname "$0")/.." && pwd); N=$1; ROOT=${2:-/scratch/$USER/bigprojects}
read -r _ REPO C _ <<<"$(awk -F'\t' -v n="$N" '$1==n' "$H/projects.tsv")"
[ -n "${REPO:-}" ] || { echo "unknown project $N" >&2; exit 2; }
mkdir -p "$ROOT/src" "$ROOT/projects"; S=$ROOT/src/$(basename "$REPO")
[ -d "$S" ] || git clone -q --filter=blob:none --no-checkout "$REPO" "$S"
P=$ROOT/projects/$N; rm -rf "$P"; mkdir -p "$P"; git -C "$S" archive "$C" | tar -x -C "$P"
ML=0df444a360eaa60ab8c11dca51a86af692955474
if ! grep -q "$ML" "$P/lake-manifest.json"; then          # port from db584cd6 (v4.33.0) = one Mathlib commit (toolchain bump)
  echo "leanprover/lean4:v4.33.1" > "$P/lean-toolchain"
  python3 -I - "$P/lake-manifest.json" "$ML" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
for p in m["packages"]:
    if p["name"] == "mathlib":
        assert p["rev"].startswith("db584cd6"), p["rev"]
        p["rev"] = sys.argv[2]
json.dump(m, open(sys.argv[1], "w"), indent=1); open(sys.argv[1], "a").write("\n")
PY
fi
case $N in
  flt) sed -i "s/db584cd6d46c92f209a44c0f1c829460d327499d/$ML/g" "$P/lakefile.toml" "$P/lake-manifest.json" ;;
  carleson) sed -i 's/^defaultTargets = \["Carleson"\]/defaultTargets = ["Carleson", "Solution"]/' "$P/lakefile.toml" ;;
  compfileslib) sed -i 's/^defaultTargets = .*/defaultTargets = ["ProblemExtraction", "Compfiles"]/' "$P/lakefile.toml" ;;
  physleanport) sed -i '/^enableArtifactCache = true$/d; /^restoreAllArtifacts = true$/d' "$P/lakefile.toml" ;;
esac
CH=$N; case $N in compfileslib) CH=compfiles;; physleanport) CH=physlean;; esac
rm -rf "$P-challenge"; cp -a "$H/challenges/$CH" "$P-challenge"
echo "$P ($(find "$P" -name '*.lean' | wc -l) .lean files) + $P-challenge"
