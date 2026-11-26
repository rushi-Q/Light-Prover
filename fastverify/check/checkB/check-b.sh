#!/bin/bash
# check/checkB/check-b.sh EXPORT CHALLENGE_EXPORT COMPARATOR_JSON [--threads N] [--json FILE] [--timeout SEC]
#                         [--dual|--single|--mode dual|single] [--unsafe ignore-order] [--workdir DIR] [--bin DIR]
# menu: C3 = --dual (default), C4 = --single (UNSAFE opt-in); --unsafe ignore-order (UNSAFE opt-in, see README.md)
# check/checkB/check-b.sh --preflight [--bin DIR]
# FAST CHECK B (unofficial): kcompare (statement/axiom comparison as Lean 4.36 lake comparator) + independent kernels
# gruszka and nano-lean (+ the official nanoda binary when the config names nanoda) + the official-limits pre-check.
# Exit 0 ACCEPTED / 1 REJECTED / 2 DECLINED (fail closed); one JSON object on stdout (and in --json FILE).
# Implementation and exact semantics: check_b.py (same directory). Nothing verdict-relevant is taken from the environment.
exec env -i PATH=/usr/bin:/bin LANG=C.UTF-8 TMPDIR="${TMPDIR:-/tmp}" /usr/bin/python3 -I "$(dirname "$(readlink -f "$0")")/check_b.py" "$@"
