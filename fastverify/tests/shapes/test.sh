#!/bin/bash
# heavy
# test shapes (kind generality/e2e + soundness): the synthetic-shape benchmark (bench/shapes) through the official
#   flow (--preset reference; the shared challenge built officially, then pinned) and --preset sound: wide / deep (merged
#   chain) / layered / kernel-heavy (`decide +kernel`) / inductive cases (verdict = official; export byte-identical to the
#   official one whenever no module was merged) + negatives: `sorry` deep in a chain, and a FALSE `decide +kernel` theorem
#   inside a MERGED chain (the official build fails in the kernel; the untrusted sound build passes under skip-kernel-tc and
#   the trusted CS check must reject). FAIL CRITICAL iff sound accepts an officially rejected case. ~6 min at 8 threads.
#   Env: EVAL_THREADS, SHAPES_CASES, FASTVERIFY, PACKAGES_WS (on hosts with an NFS home prefer a node-local install:
#   bench/shapes/mklocal.sh).
# finding: none (generality + soundness regression of the sound mode on project shapes)
export FV_COMPONENT_ALL=1
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/shapes.XXXXXX")}
exec "$(dirname "$0")/../lib/component.sh" shapes "$W" "${FV_ROOT:-$(dirname "$0")/../..}/bench/shapes/test/shapes-test.sh" "$W.work"
