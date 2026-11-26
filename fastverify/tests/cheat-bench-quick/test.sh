#!/bin/bash
# heavy
# test cheat-bench-quick (kind soundness/e2e): the proof-cheating benchmark (tests/cheat-bench, quick set: 21 cases x
#   --preset reference (official flow) and --preset sound): sorry/axiom/native_decide variants, environment hacks
#   (addDeclCore doCheck:=false, run_tac proof body), the kernel-skip option + decide +kernel (lakefile and one-line body),
#   statement tricks (notation, OfNat instance, macro_rules on the theorem command), a prelude module with its own Iff +
#   propext, an olean swap after the targeted-overlap snapshot, controls, and T21 (sound-only accept of a valid proof:
#   allowed only if the unmodified official lake comparator accepts the very export the sound run checked). ~10-25 min on a loaded host.
#   Full benchmark (62 cases x 4 presets): tests/cheat-bench/test.sh WORKDIR full.
# finding: none (soundness regression: no fast preset may accept what the official flow rejects)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/cheat-bench-quick.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" cheat-bench-quick "$W" "$(dirname "$0")/../cheat-bench/test.sh" "$W.work"
