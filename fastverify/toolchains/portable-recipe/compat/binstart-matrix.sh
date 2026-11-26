#!/bin/bash
# binstart-matrix.sh OUT.tsv NAME=BINARY... : does each (statically or dynamically linked) binary LOAD in each distro image?
# Runs `BINARY --help` (stdin /dev/null, --network none, read-only bind of the binary's directory) and classifies the result:
#   loads    = the dynamic loader resolved everything (any exit code except the loader's 127, no loader message);
#   NO-LOAD  = 'error while loading shared libraries' / 'version `GLIBC_...' not found' / exit 127.
set -u
OUT=$1; shift
IMAGES=${IMAGES:-"centos:7 amazonlinux:2 ubuntu:18.04 debian:10 rockylinux:8 ubuntu:20.04 debian:11 ubuntu:22.04 rockylinux:9 amazonlinux:2023 debian:12 opensuse/leap:15 ubuntu:24.04 fedora:41 archlinux:latest"}
printf 'image\tglibc\tbinary\tresult\tnote\n' > "$OUT"
for img in $IMAGES; do
  for nb in "$@"; do
    n=${nb%%=*}; b=${nb#*=}; d=$(dirname "$b"); f=$(basename "$b")
    r=$(docker run --rm --network none --user "$(id -u):$(id -g)" -v "$d":/b:ro "$img" sh -c \
      'g=$( (getconf GNU_LIBC_VERSION 2>/dev/null || ldd --version 2>&1 | head -1) | grep -o "[0-9]\.[0-9]*" | head -1); o=$(timeout 20 /b/'"$f"' --help < /dev/null 2>&1); e=$?
       if [ $e = 127 ] || echo "$o" | grep -q -E "error while loading shared libraries|version .GLIBC|version .GLIBCXX|cannot open shared object"; then r=NO-LOAD; else r=loads; fi
       printf "%s\t%s\t%s\n" "$g" "$r" "$(echo "$o" | grep -m1 -E "error while loading|version .GLIBC|not found" | cut -c1-120)"' 2>&1 | tail -1)
    printf '%s\t%s\n' "$img" "$(echo "$r" | sed "s/^\([^\t]*\)\t/\1\t$n\t/")" >> "$OUT"
  done
done
column -t -s $'\t' "$OUT" | cut -c1-150
