#!/bin/bash
# tests/portable-toolchains/run.sh [--docker]   (~10 s without --docker, ~1 min with)
# Regression test of the PORTABLE build toolchains (toolchains/unofficial/*-portable.json, recipe toolchains/portable-recipe):
#  1. manifests: every .olean/.ilean/.ir/.olean.private/.olean.server/.c/.json (and their .hash) of each portable tree has the
#     SAME sha256 as in the original tree's manifest (pure JSON check, no tree needed) and the file sets are equal;
#  2. per tree present on this host (/scratch/fastverify-next/tc/NAME): lib/toolchain.py verify-unofficial (whole tree + starts),
#     every ELF in bin/ and lib/: max GLIBC symbol version <= 2.17, no GLIBCXX, DT_NEEDED only from the glibc/libgcc set;
#  3. the package's static startup probe (lib/autotune.py) predicts 'starts' for each present portable tree on this host and
#     `bin/lean --version` really starts (no false start);
#  4. --docker: `lean --version` + elaboration of compat/T.lean inside centos:7 (glibc 2.17) for each present tree, and the
#     produced .olean equals the official 4.33.1's (591a37da... for this file).
#  5. lean4-v4.37.0-rc1-pgo-portable: version line == the release's, verify-unofficial, max GLIBC_2.25; --docker: ubuntu:18.04
#     elaboration .olean == the official 4.37.0-rc1's (8663025e...);
#  6. build.sh hostcc_for (the host-C-compiler fallback for the planner / fast-exact plugin): live function + a real link.
# Prints PASS/FAIL/SKIP rows and RESULT: PASS|FAIL.
set -u
D=$(cd "$(dirname "$0")/../.." && pwd); TC=/scratch/fastverify-next/tc; fail=0
ok() { echo "PASS $*"; }; bad() { echo "FAIL $*"; fail=1; }; skip() { echo "SKIP $*"; }
PAIRS="lean4-s01zy-3cf5641cbd-pgo-portable:lean4-s01zy-3cf5641cbd-pgo lean4-d5e35ef223-pgo-portable:lean4-d5e35ef223-pgo lean4-7586a50cec-nopgo-portable:lean4-7586a50cec-nopgo"
for pr in $PAIRS; do
  n=${pr%%:*}; o=${pr#*:}; m=$D/toolchains/unofficial/$n.json; om=$D/toolchains/unofficial/$o.json
  [ -f "$m" ] || { bad "$n: manifest missing"; continue; }
  r=$(python3 -I - "$m" "$om" <<'PY'
import json, sys, re
a = json.load(open(sys.argv[1])); b = json.load(open(sys.argv[2]))
fa, fb = a["files"], b["files"]
if set(fa) != set(fb) or set(a["dirs"]) != set(b["dirs"]): print("file/dir sets differ"); sys.exit()
lean = re.compile(r"\.(olean|ilean|ir|c|json)(\.(private|server|sig))?(\.hash)?$")
sel = [p for p in fa if lean.search(p) and not p.endswith(".c.o.export.hash")]
d = [p for p in sel if fa[p][0] != fb[p][0]]
print(f"{len(sel)} lean artifacts compared, {len(d)} differ" + (f" e.g. {d[:3]}" if d else ""))
PY
)
  case $r in *", 0 differ") ok "$n vs $o manifests: $r";; *) bad "$n vs $o manifests: $r";; esac
  if [ ! -d "$TC/$n" ]; then skip "$n: tree not installed on this host"; continue; fi
  python3 -I "$D/lib/toolchain.py" verify-unofficial "$TC/$n" "$n" > /dev/null 2>&1 && ok "$n: verify-unofficial (tree + starts)" || bad "$n: verify-unofficial"
  e=$(python3 -I - "$TC/$n" <<'PY'
import os, re, subprocess, sys
allowed = {"libc.so.6", "libm.so.6", "libdl.so.2", "libpthread.so.0", "librt.so.1", "libgcc_s.so.1", "ld-linux-x86-64.so.2",
           "libInit_shared.so", "libleanshared.so", "libleanshared_1.so", "libleanshared_2.so", "libLake_shared.so"}
worst = (2, 0); probs = []; n = 0
for d in ("bin", "lib"):
    for root, _, fs in os.walk(os.path.join(sys.argv[1], d)):
        for f in fs:
            p = os.path.join(root, f)
            if os.path.islink(p) or open(p, "rb").read(4) != b"\x7fELF": continue
            n += 1
            t = subprocess.run(["objdump", "-T", "-p", p], capture_output=True, text=True).stdout
            for v in re.findall(r"GLIBC_2\.(\d+)", t): worst = max(worst, (2, int(v)))
            if "GLIBCXX_" in t: probs.append(f"{f}: GLIBCXX")
            for lib in re.findall(r"NEEDED\s+(\S+)", t):
                if lib not in allowed: probs.append(f"{f}: NEEDED {lib}")
print(f"{n} ELF files, max GLIBC_{worst[0]}.{worst[1]}" + (f"; {probs[:4]}" if probs else "") + ("" if worst <= (2, 17) and not probs else " BAD"))
PY
)
  case $e in *BAD) bad "$n: $e";; *) ok "$n: $e";; esac
  p=$(python3 -I - "$D" "$TC/$n" <<'PY'
import importlib.util, os, sys
spec = importlib.util.spec_from_file_location("autotune", os.path.join(sys.argv[1], "lib", "autotune.py"))
at = importlib.util.module_from_spec(spec); spec.loader.exec_module(at)
t = sys.argv[2]; g = at.glibc_version(); req = at.required_glibc(t); rx = at.required_glibcxx(t); miss = at.missing_libs(t)
print("starts" if (g and req and g >= req and rx is None and not miss) else f"refuse req={req} cxx={rx} miss={miss}")
PY
)
  if env -i PATH=/usr/bin:/bin "$TC/$n/bin/lean" --version > /dev/null 2>&1; then
    [ "$p" = starts ] && ok "$n: probe says starts and it starts" || bad "$n: probe says '$p' but it starts (false refuse)"
  else bad "$n: does not start on this host (probe: $p)"; fi
  if [ "${1:-}" = --docker ]; then
    if command -v docker > /dev/null && docker image inspect centos:7 > /dev/null 2>&1; then
      s=$(docker run --rm --network none --user "$(id -u):$(id -g)" -e HOME=/tmp -v "$TC/$n":/tc:ro -v "$D/toolchains/portable-recipe/compat/T.lean":/t/T.lean:ro centos:7 \
          sh -c 'cd /tmp && cp /t/T.lean . && /tc/bin/lean -o T.olean T.lean > /dev/null 2>&1 && sha256sum T.olean | cut -c1-16')
      [ "$s" = 591a37dad6c84c95 ] && ok "$n: centos:7 (glibc 2.17) elaborates, .olean = the official 4.33.1's" || bad "$n: centos:7 elaboration ($s)"
    else skip "$n: docker/centos:7 not available"; fi
  fi
done
# 5. the tier-2 tree lean4-v4.37.0-rc1-pgo-portable (unmodified 4.37.0-rc1 sources): its pinned version line must equal the
#    OFFICIAL release's (toolchains/leanprover--lean4---v4.37.0-rc1.json); installed tree: verify-unofficial, max GLIBC_2.25
#    (the release's own requirement, weak getentropy), allowed DT_NEEDED only
n=lean4-v4.37.0-rc1-pgo-portable; m=$D/toolchains/unofficial/$n.json
if [ -f "$m" ]; then
  r=$(python3 -I -c 'import json,sys; a=json.load(open(sys.argv[1])); b=json.load(open(sys.argv[2])); print("same" if a["lean_version"]==b["lean_version"] else "DIFF "+a["lean_version"])' "$m" "$D/toolchains/leanprover--lean4---v4.37.0-rc1.json")
  [ "$r" = same ] && ok "$n: pinned lean --version line == official 4.37.0-rc1" || bad "$n: version line $r"
  if [ -d "$TC/$n" ]; then
    python3 -I "$D/lib/toolchain.py" verify-unofficial "$TC/$n" "$n" > /dev/null 2>&1 && ok "$n: verify-unofficial (tree + starts)" || bad "$n: verify-unofficial"
    w=$(for f in "$TC/$n"/bin/* "$TC/$n"/lib/lean/*.so; do objdump -T "$f" 2>/dev/null | grep -o 'GLIBC_2\.[0-9]*'; done | sort -t. -k2 -n | tail -1)
    nd=$(for f in "$TC/$n"/bin/* "$TC/$n"/lib/lean/*.so; do objdump -p "$f" 2>/dev/null | awk '/NEEDED/{print $2}'; done | sort -u | grep -v -E '^(libc\.so\.6|libm\.so\.6|libdl\.so\.2|libpthread\.so\.0|librt\.so\.1|libgcc_s\.so\.1|ld-linux-x86-64\.so\.2|lib(Init|Lake|leanshared(_[0-9])?)_?shared\.so|libleanshared(_[0-9])?\.so|libInit_shared\.so|libLake_shared\.so)$' | tr '\n' ' ')
    [ "$w" = GLIBC_2.25 ] || [ "$(printf '%s\n' "$w" GLIBC_2.25 | sort -t. -k2 -n | tail -1)" = GLIBC_2.25 ] && [ -z "$nd" ] && ok "$n: max $w, DT_NEEDED only glibc/libgcc/own libs" || bad "$n: max $w, extra NEEDED: $nd"
    if [ "${1:-}" = --docker ]; then   # oldest glibc image the RELEASE runs on (CentOS 7 runs neither): same .olean as the release
      if command -v docker > /dev/null && docker image inspect ubuntu:18.04 > /dev/null 2>&1; then
        s=$(docker run --rm --network none --user "$(id -u):$(id -g)" -e HOME=/tmp -v "$TC/$n":/tc:ro -v "$D/toolchains/portable-recipe/compat/T.lean":/t/T.lean:ro ubuntu:18.04 \
            sh -c 'cd /tmp && cp /t/T.lean . && /tc/bin/lean -o T.olean T.lean > /dev/null 2>&1 && sha256sum T.olean | cut -c1-16')
        [ "$s" = 8663025e93f1f9c3 ] && ok "$n: ubuntu:18.04 (glibc 2.27) elaborates, .olean = the official 4.37.0-rc1's" || bad "$n: ubuntu:18.04 elaboration ($s)"
      else skip "$n: docker/ubuntu:18.04 not available"; fi
    fi
  else skip "$n: tree not installed on this host"; fi
fi
# 6. build.sh hostcc_for (54e3017d): where a toolchain's bundled clang cannot run (the official 4.33.1's needs GLIBC_2.29),
#    build.sh compiles the planner / fast-exact plugin with leanc + LEAN_CC=<host cc> + -L TC/lib. Checks the LIVE function:
#    (a) a toolchain whose bin/clang runs -> no host cc; (b) a fake toolchain whose bin/clang fails / is missing -> the first
#    of /usr/bin/cc, gcc, clang; (c) the fallback link itself: a Lean program compiled by the official lean and linked by its
#    leanc with LEAN_CC=<host cc> and -L TC/lib (the compile_planner flags) runs.
eval "$(sed -n '/^hostcc_for() {/,/^}/p' "$D/build/build.sh")"
if ! command -v hostcc_for > /dev/null; then bad "hostcc_for: not found in build/build.sh"; else
  OT=${OFFICIAL_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}; W=$(mktemp -d "${TMPDIR:-/tmp}/portable-hcc.XXXXXX")
  hc=; for c in /usr/bin/cc /usr/bin/gcc /usr/bin/clang; do [ -x "$c" ] && { hc=$c; break; }; done
  mkdir -p "$W/fail/bin" "$W/none/bin"; printf '#!/bin/sh\nexit 1\n' > "$W/fail/bin/clang"; chmod +x "$W/fail/bin/clang"
  [ "$(hostcc_for "$W/fail")" = "$hc" ] && [ "$(hostcc_for "$W/none")" = "$hc" ] \
    && ok "hostcc_for: bundled clang failing/missing -> host cc '${hc:-none}'" || bad "hostcc_for: fake toolchains -> '$(hostcc_for "$W/fail")' / '$(hostcc_for "$W/none")', expected '$hc'"
  if [ -x "$OT/bin/lean" ]; then
    if env -i PATH=/usr/bin:/bin "$OT/bin/clang" --version > /dev/null 2>&1; then
      [ -z "$(hostcc_for "$OT")" ] && ok "hostcc_for: official toolchain's clang runs here -> bundled clang kept" || bad "hostcc_for: official clang runs but host cc chosen"
    else
      [ -n "$(hostcc_for "$OT")" ] && ok "hostcc_for: official toolchain's clang cannot run here -> host cc $(hostcc_for "$OT")" || bad "hostcc_for: official clang cannot run and no host cc"
    fi
    if [ -n "$hc" ]; then
      printf 'def main : IO Unit := IO.println "hostcc-link-ok"\n' > "$W/H.lean"
      if env -i PATH=/usr/bin:/bin LEAN_PATH="$OT/lib/lean" "$OT/bin/lean" -R "$W" -c "$W/H.c" "$W/H.lean" > "$W/log" 2>&1 \
         && env -i PATH=/usr/bin:/bin LEAN_CC="$hc" "$OT/bin/leanc" -O1 "$W/H.c" -o "$W/H" -L"$OT/lib/lean" -rdynamic -L"$OT/lib" >> "$W/log" 2>&1 \
         && [ "$("$W/H")" = hostcc-link-ok ]; then ok "hostcc_for: leanc + LEAN_CC=$hc + -L TC/lib links a runnable Lean program"
      else bad "hostcc_for: fallback link failed: $(tail -3 "$W/log" | tr '\n' ' ' | cut -c1-300)"; fi
    else skip "hostcc_for: no host C compiler on this host (the fallback cannot apply)"; fi
  else skip "hostcc_for: official toolchain $OT not installed"; fi
  rm -rf "$W"
fi
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"; exit $fail
