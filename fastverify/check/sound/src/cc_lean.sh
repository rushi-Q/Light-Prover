#!/bin/bash
# cc_lean.sh SRC.c OUT.o : compile a Lean-generated C file exactly as Lake 4.36 does for a lean_exe object (.c.o.export)
TC=$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0
exec $TC/bin/clang -c -o "$2" "$1" -I $TC/include -fstack-clash-protection -ffp-contract=off -fdata-sections -ffunction-sections \
  -fPIC -fvisibility=hidden -Wno-unused-command-line-argument --sysroot $TC -nostdinc -isystem $TC/include/clang -O3 -DNDEBUG -DLEAN_EXPORTING
