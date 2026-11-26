#!/bin/bash
# compat-matrix.sh OUT.tsv NAME=TREE... : start + elaborate test of Lean toolchain trees in clean distro containers
# (docker, --network none, toolchain bind-mounted read-only, run as the calling uid). Per (image, tree):
#   start = `bin/lean --version` exits 0;  elab = `lean -o X.olean T.lean` (imports Lean's .oleans, GMP bignums, interpreter,
#   kernel) exits 0 with the expected messages;  olean = sha256 of the produced .olean (must be equal across all hosts/trees of
#   one lineage). Images: the distro / CI-runner families whose glibc spans 2.17 .. 2.40 (+ musl for the record).
set -u
OUT=$1; shift
H=$(cd "$(dirname "$0")" && pwd)
IMAGES=${IMAGES:-"centos:7 amazonlinux:2 ubuntu:18.04 debian:10 rockylinux:8 ubuntu:20.04 debian:11 ubuntu:22.04 rockylinux:9 amazonlinux:2023 debian:12 opensuse/leap:15 ubuntu:24.04 fedora:41 archlinux:latest alpine:3.20"}
printf 'image\tglibc\ttree\tstart\telab\tolean_sha256\tnote\n' > "$OUT"
for img in $IMAGES; do
  for nt in "$@"; do
    n=${nt%%=*}; t=${nt#*=}
    r=$(docker run --rm --network none --user "$(id -u):$(id -g)" -e HOME=/tmp -v "$t":/tc:ro -v "$H/T.lean":/t/T.lean:ro "$img" \
        sh -c 'g=$( (getconf GNU_LIBC_VERSION 2>/dev/null || ldd --version 2>&1 | head -1) | grep -o "[0-9]\.[0-9]*" | head -1); [ -z "$g" ] && g=musl
               v=$(/tc/bin/lean --version 2>&1); s=$?; [ $s = 0 ] && st=ok || st=FAIL
               if [ $s = 0 ]; then cd /tmp && cp /t/T.lean /tmp/T.lean && o=$(/tc/bin/lean -o /tmp/T.olean T.lean 2>&1); e=$?
                 if [ $e = 0 ] && echo "$o" | grep -q "hello 1267650600228229401496703205376" && echo "$o" | grep -q "^[0-9]"; then el=ok; sh=$(sha256sum /tmp/T.olean | cut -c1-16); else el=FAIL; sh=-; v="$o"; fi
               else el=-; sh=-; fi
               printf "%s\t%s\t%s\t%s\t%s\n" "$g" "$st" "$el" "$sh" "$(echo "$v" | head -1 | tr "\t" " " | cut -c1-140)"' 2>&1)
    printf '%s\t%s\n' "$img" "$(echo "$r" | tail -1 | sed "s/^\([^\t]*\)\t/\1\t$n\t/")" >> "$OUT"
  done
done
column -t -s $'\t' "$OUT"
