#!/bin/sh
# Harness glue (kind kernel-src): sh {src}/c07/run.sh {src} {export} {threads} [nanoda_bin]
# Runs nanoda with the config the official 4.36 comparator generates for nanoda (Lake/CLI/Check.lean runExternalKernel:
# permitted_axioms = the challenge's, unpermitted_axiom_hard_error false, nat/string extensions on), num_threads = THREADS.
# Exit status = nanoda's (0 accept, 1 error/reject, 2 declined, 101 panic).
S=$1; E=$2; T=${3:-32}; B=${4:-$S/target/release/nanoda_bin}
C=$(mktemp /tmp/nanoda-cfg.XXXXXX) || exit 3
printf '{"use_stdin":false,"export_file_path":"%s","permitted_axioms":["propext","Quot.sound","Classical.choice"],"unpermitted_axiom_hard_error":false,"num_threads":%s,"nat_extension":true,"string_extension":true}' "$E" "$T" > "$C"
"$B" "$C"
