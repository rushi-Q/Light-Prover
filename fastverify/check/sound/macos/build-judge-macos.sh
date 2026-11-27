#!/bin/bash -p
# Build the programs of the macOS judge on Apple silicon and record them in fastverify/config/pins-macos.env.
#
# Usage: build-judge-macos.sh [--sources-only] OUTDIR
#   OUTDIR          directory for build runs; every run gets a new subdirectory with its sources, logs and bin/
#   --sources-only  stage the sources, print their fingerprints, compare them with pins.env and stop
#                   (needs neither Lean nor Rust)
#
# Programs and their sources, all from this tree and unchanged:
#   pleanchecker         check/sound/src                                        official Lean 4.36 kernel replay
#   ccmp-lowmem          check/sound/src plus five files of check/lowmem/src    comparison
#   pleanchecker-lowmem  check/lowmem/src-ultralowmem/src/pleanchecker-lowmem   streaming kernel replay
#   gruszka              sources/gruszka plus check/checkB/patches/gruszka-combined-v6.diff   second kernel
# Tools: the official Lean 4.36.0 toolchain for arm64 macOS (TC36, default
# ${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.36.0), whose files are checked against the digests in
# config/components.macos.json before any of them runs; Rust 1.97.1, the release of the Linux recipes for gruszka
# (FV_RUST_BIN: the directory with cargo and rustc, default the toolchain 1.97.1 of rustup; another version is
# refused); and of the Command Line Tools or of Xcode the SDK, for its C headers, which the record names. The C code
# of gruszka is compiled, and gruszka is linked, by the clang and the lld of the Lean toolchain, like the Lean programs.
# The crate archives of sources/gruszka/Cargo.lock (NAME-VERSION.crate) are taken from the folder FV_CRATES, by
# default from the folders registry/cache/* of ${CARGO_HOME:-$HOME/.cargo}, where `cargo fetch` puts them. Only the
# checksums in Cargo.lock are trusted: cargo_build.py checks every archive and unpacks it, and cargo runs offline
# with a home of its own in the build directory.
# LEAN_NUM_THREADS sets the number of build jobs (default 2). No other variable of the caller reaches a compiler.
#
# pins.env of this directory holds the fingerprints of the sources and the SHA-256 of the four programs. A build
# that gives other bytes for one of them stops here, because the judge refuses such a program.
# The record: one `SRC <program> <fingerprint of its sources>` and one `PIN <program> <sha256> <absolute path>`
# line per program. An earlier record is replaced.
set -euo pipefail
PATH=/usr/bin:/bin
sources_only=0
if [ "${1:-}" = --sources-only ]; then sources_only=1; shift; fi
[ "$#" -eq 1 ] || { echo "usage: $0 [--sources-only] OUTDIR" >&2; exit 2; }
here=$(cd "$(/usr/bin/dirname "$0")" && pwd -P)
project=$(cd "$here/../../../.." && pwd -P)
fv=$project/fastverify
jobs=${LEAN_NUM_THREADS:-2}
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo 'invalid LEAN_NUM_THREADS' >&2; exit 2; }

/bin/mkdir -p "$1"
out=$(cd "$1" && pwd -P)
run=$(/usr/bin/mktemp -d "$out/build.XXXXXXXX")
/bin/mkdir -p "$run"/{src,bin,logs,tmp,home}

# Every build starts from a private copy of the sources. support.py stages them (regular files only; the patch of
# the second kernel must have its pinned digest and apply exactly); pins.env holds the fingerprints they must have.
if ! /usr/bin/python3 -I - "$here" "$project" "$run" <<'SOURCES'
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import support

try:
    pins = support.TreePins()
    found = support.stage_sources(Path(sys.argv[2]), Path(sys.argv[3]), pins.files['gruszka_patch'])
except support.Declined as error:
    sys.exit(str(error))
for name in sorted(found):
    print(f'{found[name]}  {name}')
sys.exit(0 if found == pins.sources else 1)
SOURCES
then
  echo 'not the sources that pins.env pins' >&2
  exit 2
fi
if [ "$sources_only" = 1 ]; then
  echo "the staged sources under $run/src are the ones pins.env pins"
  exit 0
fi
# The build folder is written into compiler flags, so its path must be plain. cargo_build.py has the rule and
# applies it when the second kernel is built; it is asked here, before anything is compiled.
/usr/bin/python3 -I - "$here" "$run" <<'FOLDER' || exit 2
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import cargo_build

if not cargo_build.PLAIN.fullmatch(sys.argv[2]):
    sys.exit(f'the build folder {sys.argv[2]} must be a path of letters, digits and . _ + @ -: it is written into '
             'compiler flags')
FOLDER

[ "$(/usr/bin/uname -sm)" = "Darwin arm64" ] || { echo 'requires arm64 macOS' >&2; exit 2; }
tc=$(cd "${TC36:-${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.36.0}" && pwd -P)
rustbin=${FV_RUST_BIN:-${RUSTUP_HOME:-$HOME/.rustup}/toolchains/1.97.1-aarch64-apple-darwin/bin}
[ -x "$rustbin/rustc" ] && [ -x "$rustbin/cargo" ] \
  || { echo "no rustc and cargo in $rustbin: install Rust 1.97.1 (rustup toolchain install 1.97.1)" >&2; exit 2; }
rustbin=$(cd "$rustbin" && pwd -P)
if [ -n "${FV_CRATES:-}" ]; then crates=("$FV_CRATES"); else crates=("${CARGO_HOME:-$HOME/.cargo}"/registry/cache/*); fi
# The second kernel is built with the Rust of the Linux recipes (check/checkB/build.sh,
# tools/reproduce/portable-gruszka.sh): the release 1.97.1, told by the whole line that rustc prints and checked
# before anything is compiled.
rustc_wanted='rustc 1.97.1 (8bab26f4f 2026-07-14)'
rustc_version=$(/usr/bin/env -i HOME="$run/home" PATH="$rustbin:/usr/bin:/bin" "$rustbin/rustc" --version) \
  || rustc_version=unknown
[ "$rustc_version" = "$rustc_wanted" ] || {
  echo "requires $rustc_wanted, the Rust of the Linux recipes for gruszka; $rustbin/rustc is: $rustc_version" >&2
  exit 2
}
echo "Building the macOS judge programs under $run"

# Files of the official Lean 4.36.0 toolchain for arm64 macOS: the three launchers that build the judge, the shared
# libraries that hold their code and every archive, stub and library that the judge's programs are linked from.
# Their digests are pinned in config/components.macos.json; they are checked before any of them runs.
/usr/bin/python3 -I - "$fv/config/components.macos.json" > "$run/logs/toolchain.sha256" <<'TOOLCHAIN'
import json
import sys

for path, digest in json.load(open(sys.argv[1]))['lean_toolchains']['leanprover/lean4:v4.36.0']['sha256'].items():
    print(f'{digest}  {path}')
TOOLCHAIN
(cd "$tc" && /usr/bin/shasum -a 256 --status -c "$run/logs/toolchain.sha256") \
  || { echo "$tc: not the official Lean 4.36.0 toolchain for arm64 macOS" >&2; exit 2; }

# Of the system only the SDK is used, for its C headers: the C file of the comparison and the allocator of the
# second kernel include them. The compilers and the linker are those of the two toolchains. The SDK is asked for
# in an environment of this script, and the record names it.
system=(/usr/bin/env -i PATH=/usr/bin:/bin)
sdk=$("${system[@]}" /usr/bin/xcrun --sdk macosx --show-sdk-path)
compilers="macOS $(/usr/bin/sw_vers -productVersion) ($(/usr/bin/sw_vers -buildVersion))"
compilers+="; SDK $("${system[@]}" /usr/bin/xcrun --sdk macosx --show-sdk-version) at $sdk"
compilers+="; developer directory $("${system[@]}" /usr/bin/xcode-select -p)"
# The three Lean programs are built in an environment of this script. Two things of the machine would otherwise get
# into their bytes. The clang of the toolchain takes the version of the running macOS as the oldest system the
# programs are for, and the linker writes it into them: MACOSX_DEPLOYMENT_TARGET names 11.0, the oldest macOS on
# Apple silicon and the target of the toolchain's own programs. And the C file of the comparison names lean.h by
# the place where the toolchain is installed: the compiler is given /lean-tc for it, as in
# tools/reproduce/rebuild-lowmem-437.sh.
clean=(/usr/bin/env -i HOME="$run/home" TMPDIR="$run/tmp" PATH="$tc/bin:/usr/bin:/bin" LANG=C.UTF-8
       LEAN_NUM_THREADS="$jobs" MACOSX_DEPLOYMENT_TARGET=11.0)
lake_build() {
  local label=$1; shift
  (cd "$run/src/$label" && "${clean[@]}" "$tc/bin/lake" -v build "$@") > "$run/logs/$label.build" 2>&1 || {
    /usr/bin/tail -n 35 "$run/logs/$label.build" >&2; return 1;
  }
}
lake_build pleanchecker pleanchecker
lake_build pleanchecker_lowmem pleanchecker
(cd "$run/src/ccmp_lowmem" && "${clean[@]}" "$tc/bin/leanc" -c -O3 -Wall -Wextra -Wno-unused-parameter \
    -ffile-prefix-map="$run/src/ccmp_lowmem"=. -ffile-prefix-map="$tc"=/lean-tc \
    -isystem "$sdk/usr/include" lowmem_arena.c -o lowmem_arena.o)
lake_build ccmp_lowmem ccmp-lowmem
/bin/cp "$run/src/pleanchecker/.lake/build/bin/pleanchecker" "$run/bin/pleanchecker"
/bin/cp "$run/src/pleanchecker_lowmem/.lake/build/bin/pleanchecker" "$run/bin/pleanchecker-lowmem"
/bin/cp "$run/src/ccmp_lowmem/.lake/build/bin/ccmp-lowmem" "$run/bin/ccmp-lowmem"
# The second kernel: cargo_build.py checks and unpacks the crates and runs cargo in an environment it writes.
/usr/bin/python3 -I - "$here" "$run" "$rustbin" "$jobs" "$sdk" "$tc" "${crates[@]}" <<'SECOND' \
  || { /usr/bin/tail -n 35 "$run/logs/gruszka.build" >&2 2> /dev/null; exit 1; }
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import cargo_build

run = Path(sys.argv[2])
try:
    program = cargo_build.build(run, Path(sys.argv[3]), [Path(folder) for folder in sys.argv[7:]], int(sys.argv[4]),
                                sys.argv[5], sys.argv[6])
except cargo_build.Declined as error:
    sys.exit(str(error))
shutil.copyfile(program, run / 'bin/gruszka')
(run / 'bin/gruszka').chmod(0o755)
SECOND

# No program may hold a folder of this machine as text, and the four programs must be the ones pins.env pins. Then
# they are recorded.
record=$fv/config/pins-macos.env
versions="$("$tc/bin/lean" --version); $rustc_version; jobs=$jobs"
/usr/bin/python3 -I - "$here" "$run" "$record" "$versions" "$compilers" "$tc" "${HOME:-}" <<'RECORD'
import hashlib
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, sys.argv[1])
import support

run, record = map(Path, sys.argv[2:4])
files = {'pleanchecker': 'pleanchecker', 'ccmp_lowmem': 'ccmp-lowmem', 'pleanchecker_lowmem': 'pleanchecker-lowmem',
         'gruszka': 'gruszka'}
programs = {name: run / 'bin' / files[name] for name in files}
# The build folder, the place of the toolchain and the home folder of whoever builds, under which the two usually
# lie: bytes that hold one of them could be rebuilt only on a machine with the same folders.
places = {'the build folder': run, 'the place of the Lean toolchain': sys.argv[6], 'the home folder': sys.argv[7]}
held = [f'  {files[name]}: {what}' for name in sorted(programs)
        for what in support.machine_paths(programs[name], places)]
if held:
    sys.exit('\n'.join(['a program holds a folder of this machine as text, and nothing was recorded:', *held]))
pins = support.TreePins()
built = {name: hashlib.sha256(programs[name].read_bytes()).hexdigest() for name in pins.programs}
differ = [f'  {files[name]}: SHA-256 {built[name]}, pinned {pins.programs[name]}' for name in sorted(built)
          if built[name] != pins.programs[name]]
if differ:
    sys.exit('\n'.join(['not the programs that pins.env pins; the judge refuses them, and nothing was recorded:',
                        *differ, '  built with: ' + sys.argv[4]]))
notes = [f'built by check/sound/macos/build-judge-macos.sh in {run}', sys.argv[4], sys.argv[5]]
lines, sha256 = support.write_record(record, programs, pins.sources, notes)
print('\n'.join(lines))
# The digest of the bytes that were written, not of the file read again.
print(f'Recorded in {record} (SHA-256 {sha256})')
RECORD
