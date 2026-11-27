#!/bin/bash
# build/official-build.sh PROJ PACKAGES_WS TOOLCHAIN_PREFIX [--threads N] [--json FILE] [--lean-path-out FILE] [--log DIR]
#                         [--timeout SEC] [--targets 'MOD...']
# build/official-build.sh --preflight TOOLCHAIN_PREFIX
#
# The OFFICIAL build, sandboxed: the unmodified release `lake build` (no targets = the project's default targets, exactly
# as the official flow runs it) of the prepared project copy PROJ (sources + manifest, no .lake; see bin/fastverify),
# with the toolchain at TOOLCHAIN_PREFIX (official elan release, sha256-pinned in config/components.json).
# Sandbox (modelled on Lean 4.36 `lake comparator`'s own sandboxed build, Lake/CLI/Check.lean safeLakeBuild):
#   env -i bwrap --ro-bind / / --tmpfs /home /root /tmp /run /var --dir /tmp/home --dev /dev --proc /proc
#   --unshare-all (no network) --die-with-parent --new-session --clearenv; PATH=$TC/bin:/usr/bin:/bin HOME=/tmp/home;
#   toolchain and dependency packages read-only (each dependency of PROJ/lake-manifest.json bound from PACKAGES_WS after
#   lib/manifest.py verified name/url/rev/...); PROJ (a private copy) writable.
# Unlike `lake comparator` the build does NOT set LEAN_ABORT_ON_PANIC (the official flow is a plain `lake build`); the
# export step sets it (finding 030).
# After a successful build, `lake env printenv LEAN_PATH` (same sandbox) gives the search path for the exporter.
# Exit: 0 = built, 1 = `lake build` failed (official verdict: REJECTED), 2 = could not run (sandbox/preflight/inputs).
set -u
D=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
PY=/usr/bin/python3
# macOS: a sandbox profile, links and the guard stand in for bwrap, bind mounts and timeout (lib/macos/stage.sh)
STAGE_OS=; [ -x /usr/bin/uname ] && STAGE_OS=$(/usr/bin/uname -s)
if [ "$STAGE_OS" = Darwin ]; then
  STAGE_PID=$$ STAGE_WALL=0; export D PY STAGE_OS STAGE_PID STAGE_WALL; . "$D/lib/macos/stage.sh" || exit 2
fi

bindok() { # bindok SRC DST PROJ: a binds.tsv line this script may act on: plain absolute paths (no
  # control character, no empty/'.'/'..' component), DST strictly inside PROJ (lib/manifest.py's dependency binds)
  local src=$1 dst=$2 proj=$3
  case "$src$dst" in *[[:cntrl:]]*) return 1 ;; esac
  case "$src" in /*) ;; *) return 1 ;; esac
  case "$dst" in /*) ;; *) return 1 ;; esac
  case "$src/" in */../*|*/./*|*//*) return 1 ;; esac
  case "$dst/" in */../*|*/./*|*//*) return 1 ;; esac
  [ -n "$proj" ] || return 1
  case "$dst" in "$proj"/?*) return 0 ;; esac
  return 1
}

mkbinds() { # mkbinds BINDFILE PROJ: create the bind destinations ONCE, before any untrusted code runs: never
  # through a symlink (realpath = the path itself, before and after), never outside PROJ (bindok)
  local src dst
  if [ "$STAGE_OS" = Darwin ]; then macos_deps "$1" "$2"; return; fi   # no bind mounts: links, by the same rule
  while IFS=$'\t' read -r src dst; do
    [ -n "$src" ] || continue
    bindok "$src" "$dst" "$2" || return 2
    [ "$(realpath -m -- "$dst")" = "$dst" ] || return 2
    mkdir -p -- "$dst" || return 2
    [ "$(realpath -e -- "$dst")" = "$dst" ] || return 2
  done < "$1"
}

sandbox() { # sandbox PROJ TC BINDFILE CMD... (stdout/stderr passed through)
  local proj=$1 tc=$2 binds=$3; shift 3
  if [ "${STAGE_OS:-}" = Darwin ]; then   # no bwrap: a sandbox profile with the same grants (lib/macos/stage.sh)
    . "$D/lib/macos/stage.sh" || return 126
    macos_sandbox "$proj" "$tc" "$binds" "" "${THREADS:-}" "$@"; return
  fi
  local args=(--ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /tmp --dir /tmp/home
              --tmpfs /run --tmpfs /var --dev /dev --proc /proc --clearenv)
  # every other top-level directory except the system ones is hidden too (/scratch, /data, /mnt, /opt,
  # ...: service state dirs, sockets, FIFOs, other runs' and tenants' files); the run's own dirs are bound back below
  # (read-only after the binds below: only visibility changes, a write there fails with EROFS as before)
  local d ro=()
  for d in /*; do
    [ -d "$d" ] && [ ! -L "$d" ] || continue
    case "${d#/}" in bin|sbin|lib|lib32|lib64|libx32|usr|etc|dev|proc|sys|nix|gnu|home|root|tmp|run|var) ;; *) args+=(--tmpfs "$d"); ro+=(--remount-ro "$d") ;; esac
  done
  args+=(--ro-bind "$tc" "$tc")
  [ -n "$proj" ] && args+=(--bind "$proj" "$proj")
  if [ -n "$binds" ]; then
    while IFS=$'\t' read -r src dst; do
      [ -n "$src" ] || continue
      # no host-side mkdir here (mkbinds made the destinations before the untrusted build ran); a destination that
      # is missing or now reached through a symlink (planted by the build) -> no sandbox (fail closed)
      bindok "$src" "$dst" "$proj" || return 2
      [ -d "$dst" ] && [ "$(realpath -e -- "$dst")" = "$dst" ] || return 2
      args+=(--ro-bind "$src" "$dst")
    done < "$binds"
  fi
  # Lake sizes its job pool by the HOST's hardware concurrency, not by the cgroup / affinity CPU set:
  # inside a 4-CPU scope on a 224-thread node the 4.33.1 `lake build` ran 103 `lean` processes at once (44 GB in 150 s).
  # LEAN_NUM_THREADS bounds the pool (and every `lean`'s own thread pool) to --threads, default = the CPU set's size
  # (nproc), so an unlimited host is unchanged. Outputs do not depend on the thread count.
  args+=(${ro[@]+"${ro[@]}"})
  [ -n "${THREADS:-}" ] && args+=(--setenv LEAN_NUM_THREADS "$THREADS")
  args+=(--setenv PATH "$tc/bin:/usr/bin:/bin" --setenv HOME /tmp/home --setenv LANG C.UTF-8
         --unshare-all --die-with-parent --new-session --chdir "${proj:-/}")
  env -i /usr/bin/bwrap "${args[@]}" -- "$@"
}

preflight() { # preflight TC
  local tc=$1 bad=0
  local spec; spec=$("$PY" -I - "$D/config/components.json" "$tc" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
for name, t in c["lean_toolchains"].items():
    if t["prefix"] == sys.argv[2]:
        print(t["lean_version"])
        for k, v in t["sha256"].items():
            print(k, v)
        break
else:
    sys.exit(1)
PY
) || { echo "official-build: preflight: toolchain $tc is not pinned in config/components.json" >&2; return 1; }
  local want; want=$(echo "$spec" | head -n 1)
  while read -r rel sum; do
    [ -n "$rel" ] || continue
    local have; have=$(sha256sum "$tc/$rel" 2>/dev/null | cut -d' ' -f1)
    [ "$have" = "$sum" ] || { echo "official-build: preflight: $tc/$rel sha256 mismatch (have '${have:-missing}')" >&2; bad=1; }
  done < <(echo "$spec" | tail -n +2)
  local v; v=$(sandbox "" "$tc" "" "$tc/bin/lean" --version 2>&1)
  [ "$v" = "$want" ] || { echo "official-build: preflight: lean --version in the sandbox = '$v', expected '$want'" >&2; bad=1; }
  sandbox "" "$tc" "" "$tc/bin/lake" --version > /dev/null 2>&1 || { echo "official-build: preflight: lake does not start in the sandbox" >&2; bad=1; }
  return $bad
}
if [ "${1:-}" = --preflight ]; then preflight "${2:?toolchain prefix}"; exit $?; fi

[ $# -ge 3 ] || { sed -n 2,4p "$0" >&2; exit 2; }
PROJ=$(readlink -f "$1"); WS=$2; TC=$(readlink -f "$3"); shift 3
# macOS: the workspace as spelled on disk (a volume may ignore letter case, and Lake prints the disk's spelling)
[ "$STAGE_OS" != Darwin ] || WS=$(readlink -f "$WS" 2>/dev/null || printf %s "$WS")
JSON=; LPOUT=; LOG=; TIMEOUT=0; THREADS=; TARGETS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --threads) case "${2:-}" in ''|0|*[!0-9]*) echo "official-build: --threads needs a positive integer" >&2; exit 2 ;; esac
               THREADS=$2; shift 2 ;;   # becomes LEAN_NUM_THREADS inside the sandbox (lake has no job option)
    --json) JSON=$2; shift 2 ;;
    --lean-path-out) LPOUT=$2; shift 2 ;;
    --log) LOG=$2; shift 2 ;;
    --timeout) TIMEOUT=$2; shift 2 ;;
    --targets)   # build exactly what the official comparator builds:
                 # Lake/CLI/Check.lean safeLakeBuild runs `lake build MOD` with the configured module's name as a BARE target
                 # (Lake resolves it as a target declaration, then a package, then the module), instead of the defaults
      # ONE configured module per --targets (repeat the option for
      # more): a legal Lean name may contain spaces or dots inside «...» (`«Final Result»`, `«Answer..Final»`), so the
      # value is never split; it is canonicalized below as the official comparator does and passed to Lake as
      # ONE argument. Validation:
      # printable, no leading '-', no '/' or '\' (Lake target-spec syntax), whitespace only inside «...», and no empty
      # dot-separated component outside «...»
      "$PY" -I -c 'import sys
m, comps, cur, inq, ok = sys.argv[1], [], "", False, True
for c in m:
    if not c.isprintable() or c in "/\\" or (c.isspace() and not inq) or (c in "«»" and inq == (c == "«")):
        ok = False
    if c == "«":
        inq = True
    elif c == "»":
        inq = False
    if c == "." and not inq:
        comps.append(cur); cur = ""
    else:
        cur += c
comps.append(cur)
sys.exit(0 if ok and m and not m.startswith("-") and not inq and all(comps) else 1)' "$2" 2>/dev/null \
        || { echo "official-build: bad --targets module '$2'" >&2; exit 2; }
      TARGETS+=("$2")
      [ ${#TARGETS[@]} -gt 0 ] || { echo "official-build: empty --targets" >&2; exit 2; }
      shift 2 ;;
    *) echo "official-build: unknown argument $1" >&2; exit 2 ;;
  esac
done
# without --threads the bound is the CPU set this build may use (nproc honours cgroup cpusets and affinity;
# on an unlimited host it is the host's thread count, i.e. Lake's own default).
[ -n "$THREADS" ] || THREADS=$(nproc 2>/dev/null || true)
case "$THREADS" in ''|0|*[!0-9]*) THREADS= ;; esac
export THREADS   # the build runs sandbox() in a child bash (declare -f carries the function, not the variables) - D20's review
[ -n "$LOG" ] || LOG=$PROJ/../log
mkdir -p "$LOG"; LOG=$(readlink -f "$LOG")
T0=$(date +%s.%N)
emit() { # status exit detail
  local sec; sec=$(echo "$(date +%s.%N) - $T0" | bc)
  local line; line=$("$PY" -I -c 'import json,sys; print(json.dumps({"stage":"build","mode":"official","tool":"lake build (official release, sandboxed)","status":sys.argv[1],"exit":int(sys.argv[2]),"detail":sys.argv[3],"seconds":float(sys.argv[4]),"log":sys.argv[5]}))' "$1" "$2" "$3" "$sec" "$LOG/build.log")
  echo "$line"; [ -n "$JSON" ] && echo "$line" > "$JSON"
}
[ -d "$PROJ" ] || { emit ERROR 2 "no project dir $PROJ"; exit 2; }
[ -e "$PROJ/.lake" ] && { emit ERROR 2 "$PROJ/.lake exists: the project copy must not carry build state (finding 066/067)"; exit 2; }
preflight "$TC" 2>> "$LOG/build.log" || { emit ERROR 2 "preflight failed (see $LOG/build.log)"; exit 2; }
"$PY" -I "$D/lib/manifest.py" "$PROJ" "$WS" > "$LOG/binds.tsv" 2>> "$LOG/build.log" || { emit ERROR 2 "dependencies cannot be resolved offline (see $LOG/build.log)"; exit 2; }
mkbinds "$LOG/binds.tsv" "$PROJ" || { emit ERROR 2 "dependency bind destinations are not plain directories inside the project"; exit 2; }
# the official comparator does not pass the configured name verbatim: it runs
# `lake build (MOD.toName.toString)` (Lean 4.36 Lake/CLI/Check.lean :733 `cfg.solution_module.toName`, :357
# `targets.map (·.toString)`), and Lake resolves that spelling path-first. So each --targets value is canonicalized with
# the comparator's own release (the pinned 4.36 `lean --run`: trusted core code on the trusted configured name, no
# project code): `«Main»` -> `Main`, `Main.01` -> `Main.1`. A name whose canonical form is `[anonymous]` (`Main Draft`,
# `Main.`) cannot be built by the comparator either: no verdict (ERROR), never a build of something else.
if [ ${#TARGETS[@]} -gt 0 ]; then
  TC36=$("$PY" -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["lean_toolchains"]["leanprover/lean4:v4.36.0"]["prefix"])' \
         "$D/config/components.json" 2>/dev/null)
  [ -n "$TC36" ] && [ -x "$TC36/bin/lean" ] || { emit ERROR 2 "cannot canonicalize the target name: the pinned Lean 4.36 is not available"; exit 2; }
  printf '%s\n' 'def main (args : List String) : IO UInt32 := do' '  for a in args do IO.println a.toName.toString' '  return 0' \
    > "$LOG/canonical-name.lean" || { emit ERROR 2 "cannot write $LOG/canonical-name.lean"; exit 2; }
  CAN=()
  for m in "${TARGETS[@]}"; do
    c=$(cd "$LOG" && env -i PATH=/usr/bin:/bin LEAN_PATH="$TC36/lib/lean" "$TC36/bin/lean" --run "$LOG/canonical-name.lean" "$m" 2>> "$LOG/build.log") \
      || { emit ERROR 2 "cannot canonicalize the target name '$m' (lean --run failed)"; exit 2; }
    case "$c" in
      ''|'[anonymous]'|*$'\n'*) emit ERROR 2 "target '$m' has no canonical Lean name ('$c'): the official comparator cannot build it either"; exit 2 ;;
    esac
    [ "$c" = "$m" ] || echo "official-build: target '$m' -> canonical '$c' (as the official comparator passes it)" >> "$LOG/build.log"
    CAN+=("$c")
  done
  TARGETS=("${CAN[@]}")
fi

TO=(); [ "$TIMEOUT" != 0 ] && TO=(timeout --signal=KILL "$TIMEOUT")
[ "$STAGE_OS" != Darwin ] || TO=(/usr/bin/env "STAGE_WALL=$TIMEOUT")   # the sandbox's guard enforces it
"${TO[@]}" bash -c "$(declare -f sandbox bindok); sandbox \"\$@\"" _ "$PROJ" "$TC" "$LOG/binds.tsv" "$TC/bin/lake" build ${TARGETS[@]+"${TARGETS[@]}"} >> "$LOG/build.log" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  if [ $rc -ge 124 ]; then emit ERROR 2 "lake build killed/timed out (exit $rc)"; exit 2; fi
  # macOS: `lake build` exits 1 when the build fails; any other status is the sandbox's or the guard's. And the
  # sandbox refuses (EPERM, EACCES) what the Linux sandbox hides, holds in a tmpfs or mounts read-only, so a build
  # whose log carries such a refusal, in any line (the rule of build/sched.py), has not failed by itself. Both: no
  # verdict (fail closed), never REJECTED
  if [ "$STAGE_OS" = Darwin ]; then
    [ $rc -eq 1 ] || { emit ERROR 2 "lake build could not run (exit $rc)"; exit 2; }
    denied=$(grep -m1 -E "[Oo]peration not permitted|[Pp]ermission denied" "$LOG/build.log" | cut -c1-200)
    [ -z "$denied" ] || { emit ERROR 2 "lake build exit $rc: the sandbox refused an access: $denied"; exit 2; }
  fi
  # a host resource failure is not the project's failure: no verdict (fail closed), never REJECTED
  if grep -qE "No space left on device|Cannot allocate memory|Resource temporarily unavailable|failed to create thread|Too many open files|mmap.*failed|out of memory|Stale file handle|failed to read file '" "$LOG/build.log"; then
    emit ERROR 2 "lake build exit $rc with a host resource error: $(grep -m2 -E "No space left on device|Cannot allocate memory|Resource temporarily unavailable|failed to create thread|Too many open files|mmap.*failed|out of memory|Stale file handle|failed to read file '" "$LOG/build.log" | tr '\n' ' ' | cut -c1-300)"; exit 2
  fi
  # a `lean` of the build killed from OUTSIDE - SIGKILL by the kernel's OOM killer under a memory limit, or
  # SIGTERM/SIGKILL by a job manager - makes `lake build` print "error: Lean exited with code 137/143" and exit 1; that is a
  # host/resource failure like the ones above (the module did not fail to elaborate), so it is no verdict (fail closed),
  # never REJECTED. (lib/fastverify.py maps the official exporter's rc 137/143 the same way.)
  if grep -qE "^error:.*Lean exited with code (137|143)\b" "$LOG/build.log"; then
    emit ERROR 2 "lake build exit $rc: a lean process was killed from outside (OOM killer / job manager): $(grep -m2 -E 'Lean exited with code (137|143)' "$LOG/build.log" | tr '\n' ' ' | cut -c1-200)"; exit 2
  fi
  # the build's DISK filled up - in one observed run the official 4.37 `lake build` of community main died
  # at 122,149 of 146,883 modules with "error: resource exhausted (error code: 28, no space left on device)" and the run ended
  # REJECTED ("the official lake build fails"). ENOSPC is a host/resource failure exactly like the external kill above: no verdict, never
  # REJECTED. (Only the availability direction changes: a REJECTED becomes ERROR when the official log shows the error.)
  if grep -qE "resource exhausted \(error code: 28|[Nn]o space left on device" "$LOG/build.log"; then
    emit ERROR 2 "lake build exit $rc: the build ran out of disk space (ENOSPC): $(grep -m2 -E 'resource exhausted|[Nn]o space left on device' "$LOG/build.log" | tr '\n' ' ' | cut -c1-200)"; exit 2
  fi
  # `lake build` had to WRITE into a dependency package of the trusted workspace, which is bound read-only (a
  # lean_exe default target compiling a dependency's native code, Lake's artifact cache): every error is such an EROFS
  # on a path under PROJ/.lake/packages -> a normal checkout would build: no verdict (fail closed), never REJECTED
  nerr=$(grep -E '^error' "$LOG/build.log" | grep -cvx 'error: build failed'); nro=$(grep -cE '^error: (failed to cache artifact: )?read-only file system' "$LOG/build.log")
  if [ "$nro" -gt 0 ] && [ "$nerr" = "$nro" ] && ! grep -A1 -E '^error: (failed to cache artifact: )?read-only file system' "$LOG/build.log" \
       | grep -E '^  file: ' | grep -vqF "  file: $PROJ/.lake/packages/"; then
    emit ERROR 2 "lake build exit $rc: it must write into the read-only trusted dependency workspace ($nro x EROFS under $PROJ/.lake/packages, e.g. $(grep -m1 -A1 -E 'read-only file system' "$LOG/build.log" | tail -1 | cut -c1-160)); a lean_exe default target or Lake's artifact cache needs writable dependency packages"; exit 2
  fi
  emit FAILED 1 "lake build exit $rc: $(grep -m3 -E 'error' "$LOG/build.log" | tr '\n' ' ' | cut -c1-300)"; exit 1
fi
if [ -n "$LPOUT" ]; then
  sandbox "$PROJ" "$TC" "$LOG/binds.tsv" "$TC/bin/lake" env printenv LEAN_PATH > "$LOG/lean_path.txt" 2>> "$LOG/build.log" \
    || { emit ERROR 2 "lake env failed after a successful build"; exit 2; }
  # LEAN_PATH is computed from the UNTRUSTED lakefile; the export stage acts on its directories on the
  # host -> every entry must be a plain path inside PROJ (or TC/lib/lean), else no verdict
  if [ "$STAGE_OS" = Darwin ]; then   # a dependency is a link there, not a mount: the rule of lib/macos/stage.sh
    macos_lpconfined "$LOG/lean_path.txt" "$PROJ" "$TC" "$LOG/binds.tsv" 2>> "$LOG/build.log" \
      || { emit ERROR 2 "LEAN_PATH after the build leaves the project (see $LOG/build.log)"; exit 2; }
  else
  "$PY" -I -c '
import os, sys
lp, proj, tc = open(sys.argv[1]).read().strip(), sys.argv[2], sys.argv[3]
for e in lp.split(":"):
    if not e or e == os.path.join(tc, "lib", "lean"):
        continue
    if any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in e) or not os.path.isabs(e) or ".." in e.split("/"):
        sys.exit("LEAN_PATH entry is not a plain absolute path: %r" % e)
    n = os.path.normpath(e)
    if not n.startswith(proj + os.sep) or os.path.realpath(n) != n:
        sys.exit("LEAN_PATH entry outside the project %s (or through a symlink): %r" % (proj, e))' "$LOG/lean_path.txt" "$PROJ" "$TC" 2>> "$LOG/build.log" \
    || { emit ERROR 2 "LEAN_PATH after the build leaves the project (see $LOG/build.log)"; exit 2; }
  fi
  tr -d '\n' < "$LOG/lean_path.txt" > "$LPOUT"
fi
emit BUILT 0 "lake build ok"
exit 0
