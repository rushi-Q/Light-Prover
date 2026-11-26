#!/bin/bash
# tests/frontier-adversarial/test.sh [WORKDIR] [--oracle DIR] [--plain PATH]: adversarial regression test
#   of the CONDITIONAL verdict (check/frontier/check-frontier.sh): 21 source cases built with the official Lean 4.33.1 +
#   official lean4export (bwrap, no network) + 13 crafted export mutants, judged by the published check-frontier.sh;
#   REJ rows must never be accepted (exit 0/3), OK rows must give exactly the expected frontier. See test.py.
# finding: frontier soundness cases (native_decide axiom, TOCTOU, m05b non-Prop theorem, duplicate names: --project-scale; --e2e = through bin/fastverify --modulo-frontier)
exec /usr/bin/python3 -I "$(dirname "$(readlink -f "$0")")/test.py" "$@"
