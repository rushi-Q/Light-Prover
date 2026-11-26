#!/bin/bash
# portability.sh : every binary the package runs must start on THIS host (finding 001: the deployed gruszka was built with
# target-cpu=native on the AMD host and SIGILLed on Intel hosts; 031/037: host-dependent dynamic libraries).
# Checks (one PASS/FAIL line each):
#   * every ELF file under the package's binary dirs (/scratch/fastverify-next on this node, FV_BINDIRS overrides):
#     no AMD-only SSE4a instructions (insertq/extrq), required GLIBC <= this host's glibc, no unresolved shared library
#   * every stage's --preflight succeeds on this host (pinned sha256 + the binaries start), so the package can run here
set -u
FV=${FV_ROOT:-$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)}
DIRS=${FV_BINDIRS:-/scratch/fastverify-next}
HG=$(ldd --version | head -1 | grep -oE '[0-9]+\.[0-9]+$')
ver_le() { [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | head -1)" = "$1" ]; }
n=0
# opt-in UNSAFE toolchain trees (menu option T1, $DIRS/tc/<name>): host-restricted by design (the PGO build needs glibc
# 2.38): instead of the per-file checks, the package's own verifier must ACCEPT the tree where it can start and REFUSE it
# (exit 2) where it cannot - never use a toolchain that cannot run here.
for t in $(find $DIRS -mindepth 2 -maxdepth 2 -path '*/tc/*' -type d 2>/dev/null | sort); do
  tn=$(basename "$t"); out=$(python3 -I "$FV/lib/toolchain.py" verify-unofficial "$t" "$tn" 2>&1); rc=$?
  starts=0; env -i PATH=/usr/bin:/bin "$t/bin/lean" --version > /dev/null 2>&1 && starts=1
  if { [ $starts = 1 ] && [ $rc = 0 ]; } || { [ $starts = 0 ] && [ $rc = 2 ]; }; then
    echo "PASS unsafe T1 toolchain tc/$tn: starts here=$starts, toolchain.py verify-unofficial exit $rc (refused iff it cannot start)"
  else echo "FAIL unsafe T1 toolchain tc/$tn: starts here=$starts but verify-unofficial exit $rc: $(echo "$out" | tail -1 | cut -c1-150)"; fi
done
# optional local copies of OFFICIAL toolchains ($DIRS/elan/toolchains/<name>, e.g. for 4.37.0-rc1): not package
# binaries (the package verifies a toolchain file by file before it uses it), so they are not checked per file here: a
# copy that starts is a PASS, one that is broken or incomplete here is a SKIP (use another copy or ~/.elan)
for t in $(find $DIRS -mindepth 3 -maxdepth 3 -path '*/elan/toolchains/*' -type d 2>/dev/null | sort); do
  if env -i PATH=/usr/bin:/bin "$t/bin/lean" --version > /dev/null 2>&1; then echo "PASS local toolchain copy starts: ${t#/scratch/}"
  else echo "SKIP local toolchain copy ${t#/scratch/} does not start here (optional, not a package binary): $(env -i PATH=/usr/bin:/bin "$t/bin/lean" --version 2>&1 | head -1 | cut -c1-120)"; fi
done
for f in $(find $DIRS \( -path '*/tc/*' -o -path '*/elan/*' \) -prune -o -type f -print 2>/dev/null | sort); do
  head -c 4 "$f" 2>/dev/null | grep -q $'\x7fELF' || continue; n=$((n+1)); r=${f#/scratch/}
  a=$(objdump -d --no-show-raw-insn "$f" 2>/dev/null | grep -cE '\s(insertq|extrq)\s')
  [ "$a" = 0 ] && echo "PASS no SSE4a insertq/extrq: $r" || echo "FAIL $a AMD-only SSE4a instructions (insertq/extrq): $r"
  g=$(objdump -T "$f" 2>/dev/null | grep -oE 'GLIBC_[0-9]+\.[0-9]+' | sed 's/GLIBC_//' | sort -V | tail -1)
  if [ -z "$g" ] || ver_le "$g" "$HG"; then echo "PASS glibc requirement ${g:-none} <= host $HG: $r"; else echo "FAIL needs GLIBC_$g > host $HG: $r"; fi
  if ldd "$f" 2>&1 | grep -q 'not found'; then echo "FAIL unresolved shared library: $r ($(ldd "$f" 2>&1 | grep 'not found' | head -2 | tr -s ' \n' ' '))"
  else echo "PASS shared libraries resolve: $r"; fi
done
[ $n -gt 0 ] || echo "FAIL no package binaries found under $DIRS (deploy /scratch/fastverify-next on $(hostname))"
T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}   # run_all.sh: the registered toolchain (lib/paths.sh)
pf() { local name=$1; shift; [ -e "$1" ] || { echo "FAIL preflight $name: $1 missing"; return; }
  out=$(timeout 600 "$@" < /dev/null 2>&1); rc=$?
  [ $rc = 0 ] && echo "PASS preflight $name (exit 0)" || echo "FAIL preflight $name: exit $rc $(echo "$out" | tail -2 | tr '\n' ' ' | cut -c1-200)"; }
pf build/build.sh "$FV/build/build.sh" --preflight "$T33"
pf build/official-build.sh "$FV/build/official-build.sh" --preflight "$T33"
pf export/export.sh "$FV/export/export.sh" --preflight "$T33"
pf check/official "$FV/check/official/check.sh" --preflight
pf check/checkB "$FV/check/checkB/check-b.sh" --preflight
pf check/prechk "$FV/check/prechk/prechk.sh" --preflight
