#!/bin/bash
# fetch.sh NAME [ROOT] : clone the project of ../projects.tsv (public git, outside any sandbox: no code is run), export the
# pinned commit to ROOT/projects/NAME (no .git), apply the documented port (lean-toolchain v4.33.1, manifest mathlib rev
# db584cd6 (tag v4.33.0) -> 0df444a (tag v4.33.1) = one Mathlib commit that only bumps lean-toolchain), and write the clean
# challenge to ROOT/projects/NAME-challenge (from the repository's own comparator setup where it has one, else from
# ../challenges/NAME). Nothing is built here.
set -eu
H=$(cd "$(dirname "$0")/.." && pwd); N=$1; ROOT=${2:-/scratch/$USER/mathapps}
read -r _ REPO C _ <<<"$(awk -F'\t' -v n="$N" '$1==n' "$H/projects.tsv")"
[ -n "${REPO:-}" ] || { echo "unknown project $N" >&2; exit 2; }
mkdir -p "$ROOT/src" "$ROOT/projects"; S=$ROOT/src/$(echo "$REPO" | sed -E 's#https://github.com/##; s#/#_#')
[ -d "$S" ] || git clone -q "$REPO" "$S"
if [ "$N" = flt-ai ]; then REV=$C exec "$H/tools/prep-flt-ai.sh" "$S" "$ROOT"; fi
P=$ROOT/projects/$N; CH=$P-challenge; rm -rf "$P" "$CH"; mkdir -p "$P" "$CH"
SUB=; case $N in fm-eth) SUB=eth;; fm-3sum-*) SUB=3sum-apsp;; esac   # multi-project repository: one subdirectory
if [ -n "$SUB" ]; then git -C "$S" archive "$C" "$SUB" | tar -x -C "$P" --strip-components=1
else git -C "$S" archive "$C" | tar -x -C "$P"; fi
ML=0df444a360eaa60ab8c11dca51a86af692955474; OLD=db584cd6d46c92f209a44c0f1c829460d327499d
echo "leanprover/lean4:v4.33.1" > "$P/lean-toolchain"
grep -q "$ML" "$P/lake-manifest.json" || { grep -q "$OLD" "$P/lake-manifest.json"; sed -i "s/$OLD/$ML/" "$P/lake-manifest.json"; }
case $N in
  hopf)   # the repository's own comparator setup: Challenge.lean + comparator/config.json (+ definition_names = [])
    cp "$P/Challenge.lean" "$CH/"
    python3 -I - "$P/comparator/config.json" "$CH/comparator.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); c.setdefault("definition_names", [])
json.dump(c, open(sys.argv[2], "w"), indent=2); open(sys.argv[2], "a").write("\n")
PY
    ;;
  fm-*)   # Palomar layout: the project's own trusted files + comparator config; the challenge lakefile keeps the
          # project's [leanOptions] and the [[lean_lib]] blocks of the trusted libraries (lake comparator elaborates
          # the challenge module inside the same package, with the package's options)
    case $N in
      fm-eth) TF="Challenge.lean MainResults.lean"; LIBS="MainResults Challenge"; CFG=comparator.json ;;
      fm-3sum-end) TF="Challenge EndStatement.lean PaperStatements.lean"; LIBS="EndStatement PaperStatements Challenge"; CFG=comparator-endstatement.json ;;
      fm-3sum-paper) TF="Challenge EndStatement.lean PaperStatements.lean"; LIBS="EndStatement PaperStatements Challenge"; CFG=comparator-paperstatements.json ;;
    esac
    for f in $TF; do cp -a "$P/$f" "$CH/"; done
    cp "$P/$CFG" "$CH/comparator.json"
    python3 -I - "$P/lakefile.toml" "$CH/lakefile.toml" "$ML" $LIBS <<'PY'
import re, sys
src, dst, ml, libs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
blocks = re.split(r'(?m)^(?=\[)', open(src).read())
opts = [b for b in blocks if b.startswith('[leanOptions]')]
keep = [b for b in blocks if b.startswith('[[lean_lib]]') and re.search(r'(?m)^name\s*=\s*"([^"]+)"', b).group(1) in libs]
out = 'name = "challenge"\ndefaultTargets = [%s]\n\n' % ", ".join('"%s"' % l for l in libs)
out += "".join(opts)
out += "".join(re.sub(r'(?m)^#.*\n', '', b) for b in blocks if b.startswith('[[require]]'))   # verbatim (= manifest inputRev)
out += "".join(re.sub(r'(?m)^#.*\n', '', b) for b in keep)
open(dst, "w").write(out)
PY
    ;;
  *) cp -a "$H/challenges/$N/." "$CH/" ;;
esac
# challenge workspace files: the project's manifest (same package set, renamed) and a lakefile requiring mathlib
cp "$P/lean-toolchain" "$CH/"
python3 -I - "$P/lake-manifest.json" "$CH/lake-manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1])); m["name"] = "challenge"
json.dump(m, open(sys.argv[2], "w"), indent=1); open(sys.argv[2], "a").write("\n")
PY
[ -f "$CH/lakefile.toml" ] || printf 'name = "challenge"\ndefaultTargets = ["Challenge"]\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "%s"\n\n[[lean_lib]]\nname = "Challenge"\n' "$ML" > "$CH/lakefile.toml"
echo "$P ($(find "$P" -name '*.lean' | wc -l) .lean files) + $CH"
