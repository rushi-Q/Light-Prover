#!/bin/bash
# export/build-macos.sh [--sources-only] OUTDIR
# Builds the native exporter E1 and the closure guard on macOS (Apple silicon) and records them in
# fastverify/config/export-macos.env, the export stage's own file on this machine, where export.sh looks for them.
#   lean4export_native   sources/lean4export-native with export/native-exporter-macos.patch, built by the Lake of the
#                        pinned Lean 4.33.1 (tools/configure.py), its C++ core by the system's c++
#   closure_check        export/closure/closure_check.cpp, c++ -O2 -std=c++17 -pthread
# Every run builds in a new subdirectory of OUTDIR from a private copy of the sources: the vendored sources are never
# changed, and the patch must apply to the copy exactly. The fingerprint of a program's sources is the SHA-256 of the
# list of the SHA-256 of each of their files. config/components.macos.json pins the two fingerprints; this recipe builds
# nothing else, and export.sh uses a recorded program only if its fingerprint is the pinned one.
# --sources-only stages the sources, prints their fingerprints, compares them with the pins and stops.
# The record, which replaces an earlier one: a comment line with the compiler and the SDK, then one
# `SRC <program> <fingerprint>` and one `PIN <program> <sha256> <absolute path>` line per program. The tree has no
# digest of the two programs, because the system's compiler, which differs from Mac to Mac, compiles them.
set -euo pipefail
only=0; if [ "${1:-}" = --sources-only ]; then only=1; shift; fi
[ $# -eq 1 ] || { echo "usage: $0 [--sources-only] OUTDIR" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd -P); fv=${here%/*}; PY=/usr/bin/python3
mkdir -p "$1"; run=$(mktemp -d "$(cd "$1" && pwd -P)/build.XXXXXXXX")
mkdir "$run/closure_check" "$run/home"
/usr/bin/rsync -a --exclude=.git --exclude=.lake --exclude=.DS_Store "${fv%/*}/sources/lean4export-native/" \
  "$run/lean4export_native/"
cp "$here/closure/closure_check.cpp" "$run/closure_check/"
(cd "$run/lean4export_native" && LC_ALL=C /usr/bin/patch --batch --fuzz=0 -p1 < "$here/native-exporter-macos.patch") \
  > "$run/patch.log" 2>&1 && ! LC_ALL=C /usr/bin/grep -Eiq 'offset|fuzz|FAILED|reversed' "$run/patch.log" \
  || { cat "$run/patch.log" >&2; echo "native-exporter-macos.patch does not apply exactly" >&2; exit 2; }
for p in lean4export_native closure_check; do
  (cd "$run/$p" && /usr/bin/find . -type f | LC_ALL=C /usr/bin/sort | while IFS= read -r f; do
    /usr/bin/shasum -a 256 "$f"
  done) > "$run/$p.sources"
done
"$PY" -I - "$fv/config/components.macos.json" "$run" <<'PINNED' || { echo "not the pinned sources" >&2; exit 2; }
import hashlib, json, sys
pinned = json.load(open(sys.argv[1]))["export_sources"]
staged = {p: hashlib.sha256(open(f"{sys.argv[2]}/{p}.sources", "rb").read()).hexdigest() for p in pinned}
print("\n".join(f"{staged[p]}  {p}" for p in sorted(staged)))
sys.exit(staged != pinned)
PINNED
[ $only = 0 ] || exit 0

[ "$(/usr/bin/uname -sm)" = "Darwin arm64" ] || { echo "requires arm64 macOS" >&2; exit 2; }
tc=$("$PY" -I -c 'import json, sys
print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.33.1"]["prefix"])' \
  "$fv/config/components.json") && "$fv/build/official-build.sh" --preflight "$tc" \
  || { echo "the pinned Lean 4.33.1 is not in place: run tools/configure.py" >&2; exit 2; }
(cd "$run/lean4export_native" && /usr/bin/env -i PATH="$tc/bin:/usr/bin:/bin" HOME="$run/home" LANG=C.UTF-8 \
    "$tc/bin/lake" build) > "$run/lake.log" 2>&1 || { tail -n 30 "$run/lake.log" >&2; exit 1; }
/usr/bin/c++ -O2 -std=c++17 -pthread -o "$run/closure_check/closure_check" "$run/closure_check/closure_check.cpp"

record=$fv/config/export-macos.env
with="$(/usr/bin/c++ --version | /usr/bin/head -n 1), SDK $(/usr/bin/xcrun --sdk macosx --show-sdk-version)"
"$PY" -I - "$record" "$run" "$with" <<'RECORD'
import hashlib, os, sys
record, run, compiler = sys.argv[1:]
lines = [f"# export: built by export/build-macos.sh in {run} with {compiler}"]
for name, program in (("closure_check", "closure_check"), ("lean4export_native", ".lake/build/bin/lean4export")):
    lines.append(f"SRC {name} " + hashlib.sha256(open(f"{run}/{name}.sources", "rb").read()).hexdigest())
    with open(f"{run}/{name}/{program}", "rb") as built:
        lines.append(f"PIN {name} {hashlib.sha256(built.read()).hexdigest()} {run}/{name}/{program}")
with open(record + ".new", "w", encoding="utf-8") as new:
    new.write("\n".join(lines) + "\n")
os.replace(record + ".new", record)
print("\n".join(lines))
RECORD
echo "Recorded in $record"
