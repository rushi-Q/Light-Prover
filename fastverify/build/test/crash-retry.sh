#!/bin/bash
# build/test/crash-retry.sh [WORK] (S04): B3 'retries' also covers a lean that DIES (signal) with the unsafe settings:
# the module is rebuilt once with the exact official invocation; without --retry-exact the build still DECLINES.
# Fault injection: a --lean wrapper that SIGSEGVs on FX/A.lean (projects/fast-exact) and otherwise execs the official lean.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); D=$(cd "$H/../.." && pwd)
W=${1:-/tmp/fv-crashretry-$$}; rm -rf "$W"; mkdir -p "$W"; W=$(readlink -f "$W")
TC=${FV_TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
cp -a "$H/projects/fast-exact" "$W/proj"; mkdir -p "$W/nopkg"
"$D/build/build.sh" "$W/proj" "$W/nopkg" "$TC" --plan-only --log "$W/log" > "$W/plan.out" 2>&1 || { echo "FAIL plan: $(tail -1 "$W/plan.out")"; echo "RESULT: FAIL"; exit 1; }
printf '#!/bin/bash\ncase "$*" in *FX/A.lean*) kill -SEGV $$;; esac\nexec "%s/bin/lean" "$@"\n' "$TC" > "$W/crashlean.sh"; chmod +x "$W/crashlean.sh"
fail=0
run() { (cd "$W/proj" && rm -rf .lake/build && env -i PATH=/usr/bin:/bin /usr/bin/python3 -I "$D/build/sched.py" 2 "$@" \
  --extra-arg -Dlinter.all=false --lean "$W/crashlean.sh" < "$W/log/plan.jsonl" > "$W/sched.$1.out" 2>&1); }
run --retry-exact; rc=$?
if [ $rc = 0 ] && grep -q '"event": "retry-exact", "module": "FX.A", "rc": -11, "reason": "crash"' "$W/sched.--retry-exact.out"; then
  echo "PASS crash with --retry-exact: retried exactly, built"; else echo "FAIL crash with --retry-exact: rc=$rc $(tail -1 "$W/sched.--retry-exact.out")"; fail=1; fi
run --memfloor 0; rc=$?
if [ $rc = 3 ] && grep -q "DECLINE: lean died" "$W/sched.--memfloor.out"; then echo "PASS crash without --retry-exact: DECLINED as before"
else echo "FAIL crash without --retry-exact: rc=$rc $(tail -1 "$W/sched.--memfloor.out")"; fail=1; fi
[ $fail = 0 ] && echo "RESULT: PASS" || echo "RESULT: FAIL"; exit $fail
