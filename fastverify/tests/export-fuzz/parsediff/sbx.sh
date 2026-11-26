#!/bin/bash
# sbx.sh RO_DIR... -- CMD... : run CMD in bwrap without network: / read-only, /home hidden except the RO_DIRs (read-only),
# private /tmp, empty environment. Used to run the parser differential on crafted (untrusted) exports.
ro=()
while [ $# -gt 0 ] && [ "$1" != -- ]; do ro+=(--ro-bind "$1" "$1"); shift; done
shift
exec env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp --dev /dev --proc /proc \
  "${ro[@]}" --setenv PATH /usr/bin:/bin --setenv LANG C.UTF-8 --setenv HOME /tmp -- "$@"
