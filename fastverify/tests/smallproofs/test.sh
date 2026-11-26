#!/bin/bash
# heavy
# test smallproofs (kind generality/e2e): the small-proof corpus (bench/smallproofs) through the official flow
#   (--preset reference) and --preset sound with the official challenge export pinned: core-only one-theorem cases in
#   several proof styles (omega, decide +kernel, rfl on GMP literals, kernel-scaling decide, grind, induction) + the
#   negatives xk01/xk02/xk04 (false `decide +kernel` claims: the UNTRUSTED sound build accepts them under skip-kernel-tc,
#   the TRUSTED check must reject them); + nn01 / xk03 (import Mathlib) when the Mathlib workspace exists. ~10 min.
# finding: none (generality + soundness regression of the sound mode on small proofs)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/smallproofs.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" smallproofs "$W" "${FV_ROOT:-$(dirname "$0")/../..}/bench/smallproofs/test/sound-smallproofs.sh" "$W.work"
