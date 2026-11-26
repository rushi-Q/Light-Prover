#!/bin/bash
# deployed-export.sh OLEANDIR OUT ARGS... : run the DEPLOYED native exporter (needs glibc 2.38) in an ubuntu:24.04 container
D=$1; OUT=$2; shift 2
L=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1
docker run --rm -i --network none -u "$(id -u):$(id -g)" \
  -v /scratch/fastverify:/scratch/fastverify:ro -v $(cd "$(dirname "$0")" && pwd)/hostlib:/hostlib:ro -v /lib/x86_64-linux-gnu/libgmp.so.10:/hostlib2/libgmp.so.10:ro -e LD_LIBRARY_PATH=/hostlib:/hostlib2 -v "$L:$L:ro" -v "$D:$D:ro" -v "$(dirname "$OUT"):$(dirname "$OUT")" \
  -w "$D" -e LEAN_PATH="$D:$L/lib/lean" -e PATH="$L/bin:/usr/bin:/bin" -e LEAN4EXPORT_VERBOSE=0 ubuntu:24.04 \
  bash -c 'exe=/scratch/fastverify/exporter/lean4export; out=$1; shift; "$exe" "$@" > "$out"; echo "deployed native lean4export rc=$?"' _ "$OUT" "$@"
