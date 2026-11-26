#!/bin/bash
# tools/rh-sound.sh OUT [THREADS] [EXTRA fastverify ARGS...]
# The RH complete verification in SOUND mode (preset sound) on this host (use a whole machine):
#   bin/fastverify $RH_PROJECT $RH_CHALLENGE OUT --preset sound --threads THREADS --no-build-fallback
#     --challenge-sha256 3cf404f4...b91d (the official challenge export, soundness rule S1(1)) --comparator-sha256 d419c0d8...84c0
#     (its comparator.json; required with the challenge pin) [--reference-export $RH_REF]
# Environment:
#   RH_PROJECT    the RH Lean project (not redistributed, see docs/benchmarks.md); default <repository root>/alpoge-rh/lean
#   RH_CHALLENGE  the challenge workspace (challenge.export, comparator.json); default <repository root>/verify/challenge
#   RH_REF        optional: an export of the same project made with the official toolchain; if the file exists the run
#                 also reports whether its own export is byte-identical to it
# Verdict, basis, export sha256, stage seconds: OUT/result.json (printed at the end). Exit 0 ACCEPTED / 1 REJECTED / 2 none.
set -u
OUT=${1:?usage: rh-sound.sh OUT [THREADS] [EXTRA ARGS...]}; THREADS=${2:-$(nproc)}; shift; [ $# -gt 0 ] && shift
PKG=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
# forwarded options: build / check TUNING only (exact names, also as --opt=VALUE); anything that
# could change the judged solution or the challenge identity (--from-export, --export, pins, preset, checks, ...) is refused
ALLOW=" --threads --build --unsafe --export-dir --keep-work --no-build-fallback --no-integrity-cache --build-cache --overlap --overlap-targeted --overlap-targets --extra-kernel --require-kernel --skip-extra-kernel --check-hints --check-hide --official-timeout --parallel-checks --sequential-checks --no-confirm-build-failure --confirm-build-failure-full --confirm-reject --no-confirm-reject --reference-export --require-sorried-holes --preflight-only "   # pure tuning: threads, build option, transforms, checks' tuning (amdjob-sound.sh)
for x in "$@"; do
  case "$x" in
    --*) case "$ALLOW" in *" ${x%%=*} "*) ;; *) echo "rh-sound.sh: forwarded option ${x%%=*} is not a tuning option: refused (allowed:$ALLOW)" >&2; exit 2;; esac;;
    -*) echo "rh-sound.sh: forwarded option $x refused" >&2; exit 2;;
  esac
done
P=${RH_PROJECT:-$PKG/../alpoge-rh/lean}; C=${RH_CHALLENGE:-$PKG/../verify/challenge}
[ -d "$P" ] || { echo "rh-sound.sh: RH project not found at $P: set RH_PROJECT" >&2; exit 2; }
[ -d "$C" ] || { echo "rh-sound.sh: challenge workspace not found at $C: set RH_CHALLENGE" >&2; exit 2; }
REF=${RH_REF:-}
REFARG=(); [ -n "$REF" ] && [ -f "$REF" ] && REFARG=(--reference-export "$REF")
EXPD=(); [ -d /dev/shm ] && EXPD=(--export-dir /dev/shm)   # untrusted export on tmpfs (only if >= 256 GB free)
"$PKG/bin/fastverify" "$P" "$C" "$OUT" --preset sound --threads "$THREADS" --no-build-fallback "${EXPD[@]}" \
  --challenge-sha256 3cf404f445fe1625876703c422434811e9536e5dd567afd3f40290cbc883b91d \
  --comparator-sha256 d419c0d8cd8696eb6c3ebc01deb500038fb5820f04c6edc2b1b4ec24673b84c0 "${REFARG[@]}" "$@"
rc=$?
/usr/bin/python3 -I - "$OUT/result.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
e = r.get("export") or {}
print("RESULT verdict=%s trust=%s basis=%s" % (r.get("verdict"), r.get("trust"), r.get("verdict_basis")))
print("RESULT export sha256=%s size=%s identical_to_reference=%s option=%s" % (e.get("sha256"), e.get("size"),
      (e.get("reference") or {}).get("identical"), e.get("option")))
print("RESULT build option=%s attempts=%s" % ((r.get("build") or {}).get("option"),
      [(a.get("option"), a.get("exit"), a.get("seconds")) for a in (r.get("build") or {}).get("attempts", [])]))
print("RESULT stage_seconds=%s" % json.dumps(r.get("stage_seconds")))
cs = (r.get("checks") or {}).get("sound") or {}
print("RESULT check=%s %s s legs=%s" % (cs.get("verdict"), cs.get("seconds"), json.dumps((cs.get("stage") or {}).get("leg_ms"))))
print("RESULT started=%s finished=%s warnings=%s" % (r.get("started"), r.get("finished"), r.get("warnings")))
PY
exit $rc
