#!/bin/bash
# test build-zygote (kind component/stage: build/test/zygote.sh - B3 'zygote', 'zygote-prefix', 'j1-saturated' (sound preset
#   only): toy project zygote (Toy.A imports Lean + simp lemma + instance, Toy.B uses them, Toy.C is a prelude module = not a
#   continuation of the prefix, Toy.D reaches Lean through Toy.A); with the official lean the items fall back to plain lean
#   (artifacts = B1); where the pinned zygote toolchain starts (the AMD server) the zygote serves every child, exactly one
#   prefix miss (Toy.C -> plain lean) and the .olean files equal those built without the zygote)
# finding: build-zygote: the zygote items can only change how the untrusted build loads imports, never a verdict (sound-mode build transform, not tied to a numbered test)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-zygote.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" build-zygote "$W" "${FV_ROOT:-$(dirname "$0")/../..}/build/test/zygote.sh" "$W.work"
