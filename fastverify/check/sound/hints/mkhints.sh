#!/bin/bash
# mkhints.sh PCHK_LOG [MIN_MS] > HINTS : names of the declarations whose kernel job took >= MIN_MS (default 5000) in a
# pleanchecker run with -v and PCHK_SLOW_MS set ([pchk-slow] lines), RANKED longest first (first occurrence kept).
# Scheduling hints only (order/placement, never the verdict).
MIN=${2:-5000}
grep '^\[pchk-slow\]' "$1" | awk -v m="$MIN" '$2+0 >= m { n = $NF; if (n == "[prio]" || n == "[top]") n = $(NF-1); print $2+0 "\t" n }' \
  | sort -t$'\t' -k1,1nr | awk -F'\t' '!seen[$2]++ { print $2 }'
