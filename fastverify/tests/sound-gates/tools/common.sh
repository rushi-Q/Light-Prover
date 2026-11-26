# sourced by the sound-gates helper scripts: HERE (tests/sound-gates), FV (package root), W (node-local work dir), fvmut
HERE=$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")/.." && pwd)
FV=${FV_UNDER_TEST:-$(cd "$HERE/../.." && pwd)}   # the package under test (default: the one containing tests/sound-gates)
W=${SOUND_GATES_WORK:-${TMPDIR:-/tmp}/$USER-soundgates}
mkdir -p "$W"
fvmut_bin() {   # the mutation tool (tools/fvmut.cpp): $FVMUT, or compiled once per
  # host with g++/clang++ (on a host without a compiler, build it on one that has and set FVMUT=/path/to/fvmut)
  if [ -n "${FVMUT:-}" ] && [ -x "$FVMUT" ]; then echo "$FVMUT"; return 0; fi
  if [ ! -x "$W/fvmut" ]; then
    for cxx in g++ clang++; do command -v $cxx > /dev/null && $cxx -O2 -std=c++17 -pthread -o "$W/fvmut" "$HERE/tools/fvmut.cpp" && break; done
  fi
  [ -x "$W/fvmut" ] || { echo "fvmut: no C++ compiler on this node; set FVMUT" >&2; return 1; }
  echo "$W/fvmut"
}
