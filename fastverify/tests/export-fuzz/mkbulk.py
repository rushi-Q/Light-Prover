#!/usr/bin/env python3
"""mkbulk.py CHECK_SOUND_SH OUT_SH : derive the bulk-fuzzing variant of check-sound.sh. Identical decision logic
(argument handling, sandbox, config rewrite, ccmp judge, exit mapping, success-line checks); removed per-run work that
does not depend on the input: (1) the sha256 checks of the pinned binaries (start and end of run), (2) the file-by-file
verification of the official 4.36 toolchain, (3) the concurrent self-test. The campaign runs the unmodified check-sound.sh
--preflight once before it starts (pins + toolchain + self-test), and every FAIL candidate is re-run with the unmodified
script. Each substitution must apply exactly once (else this tool fails)."""
import sys, re
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
subs = [
  # (1a) pin check loop at start: keep paths, skip sha256
  ('  got=$(sha256sum "$p" | cut -d\' \' -f1)\n  [ "$got" = "${PIN_SHA[$name]}" ] || decline "sha256 mismatch for $p (got $got, pinned ${PIN_SHA[$name]})"\n  BJ=',
   '  got=${PIN_SHA[$name]}   # bulk: sha256 verified once by --preflight before the campaign\n  BJ='),
  # (2) toolchain verification
  ('/usr/bin/python3 -I "$PKGROOT/lib/toolchain.py" verify "$TC36" leanprover/lean4:v4.36.0 > /dev/null 2>&1 \\\n  || decline "the official Lean 4.36 toolchain at $TC36 does not verify against fastverify/toolchains"\n',
   ': # bulk: toolchain verified once by --preflight before the campaign\n'),
  # (3) self-test: not started, not awaited
  ('selftest & ST_PID=$!\n', ': # bulk: self-test run once by --preflight before the campaign\n'),
  ('wait "$ST_PID"; selftest_ok\n', ': # bulk: no per-run self-test\n'),
  # (1b) end-of-run pin re-check
  ('  [ "$(sha256sum "${PIN_PATH[$name]}" | cut -d\' \' -f1)" = "${PIN_SHA[$name]}" ] || decline "pinned $name changed during the run"\n',
   '  : # bulk: no end-of-run re-hash\n'),
  # re-exec must run THIS file (it does: readlink -f "$0")
]
for a, b in subs:
    n = s.count(a)
    if n != 1:
        sys.exit(f'mkbulk: substitution applies {n} times, expected 1:\n{a[:120]}')
    s = s.replace(a, b)
s = s.replace('SELF=checkSound\n', 'SELF=checkSoundBulk\n', 1)
# the bulk script may live outside the package: point HERE at the real check/sound directory (pins.env, hints, PKGROOT)
import os
here_line = 'HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)\n'
if s.count(here_line) != 1:
    sys.exit('mkbulk: HERE line not found exactly once')
s = s.replace(here_line, 'HERE=%s   # bulk: the real check/sound directory\n' % os.path.dirname(os.path.realpath(src)))
open(dst, 'w').write(s)
