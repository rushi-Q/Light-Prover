#!/bin/sh
# Finding: fast check B (kcompare + gruszka [+ nano-lean]) has no nanoda leg; the OFFICIAL comparator runs nanoda, which
# panics ("Attempted to insert duplicate Expr") on an export containing two structurally identical expression nodes.
# solution-dupexpr.export = solution.export (official Lean 4.33.1 + official lean4export v4.33.0 of Main.lean) + ONE
# appended line: a duplicate of expression node 0 ({"ie":14478,"sort":1}), referenced by nothing.
# Official leanchecker accepts it, official nanoda panics -> official lake comparator exit 1; fast A (pchk's nanoda) exit 1;
# fast check B dual / single exit 0.
# Needs: the krun sandbox; a portable pleanchecker-k (fast A) and a portable gruszka (fast B) because the deployed
# binaries do not run on the Intel hosts (finding 001; glibc 2.38).
H=$(dirname "$(readlink -f "$0")")
echo "== control: the honest solution"; sh $H/flows.sh $H/challenge.export $H/solution.export
echo "== one duplicate expr node appended"; FV=1 sh $H/flows.sh $H/challenge.export $H/solution-dupexpr.export
