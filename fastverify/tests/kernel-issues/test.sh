#!/bin/bash
# tests/kernel-issues/test.sh [WORK] [--warm]: upstream kernel/replay issues fixed after v4.36.0 (#16489 loose
#   bvar in inductive ctor types, #15100 ctor name mismatch, #15101 arbitrary quotInfo incl. a smuggled axiom; L8-L10 Replay's
#   unsafe-constructor paths, each also outside the target's closure; control C0 must be ACCEPTED) against every
#   trusted path present (sound, lowmem, ultralowmem, notary, frontier; --warm: the warm daemon + a poisoning probe).
#   Any ACCEPTED/CONDITIONAL of a crafted export = FAIL CRITICAL. Needs tests/frontier-adversarial (helpers). See test.py.
# finding: upstream kernel issues #16489 / #15100 / #15101 (no accept on any trusted path; the warm daemon was poisoned by the
#   #15100 check-full, fixed); L8-L10: the official-kernel leg alone accepts 5 of 6, only the second kernel rejects (INFO rows).
exec /usr/bin/python3 -I "$(dirname "$(readlink -f "$0")")/test.py" "$@"
