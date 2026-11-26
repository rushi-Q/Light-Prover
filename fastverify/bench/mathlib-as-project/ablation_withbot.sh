#!/bin/bash
# ablation of the sound build items on the withbot slice (147 modules): which item makes Mathlib's own build fail?
T=${RUNML:?set RUNML to the runml.sh driver this ablation used (not in the repository; runml3.sh next to this script is its successor)}
TC="toolchain-T1=lean4-7586a50cec-nopgo"
ALL="$TC,skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
NOTC="skip-kernel-tc,linter-off,retries,premise-off,fast-exact,zygote,zygote-prefix,j1-saturated,sound-fast-path,cost-hints,native-pkg,merge,check-tail"
$T withbot sound 32 -all --no-build-fallback --unsafe "$ALL"
$T withbot sound 32 -tconly --no-build-fallback --unsafe "$TC"
$T withbot sound 32 -notc --no-build-fallback --unsafe "$NOTC"
for x in skip-kernel-tc linter-off premise-off fast-exact native-pkg; do
  $T withbot sound 32 -only-$x --no-build-fallback --unsafe "$x"
done
