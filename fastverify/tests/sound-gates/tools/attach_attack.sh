#!/bin/bash
# attach_attack.sh PKG WORKDIR : adversarial test of the --incr-dir / --attach protocol (overlapped Lean leg).
# A process with the build sandbox's view of the file system (bwrap --ro-bind / /, no network, own pid namespace) tries to
# make check-sound.sh accept a REJECTED export (rh-mid midM1) while an --incremental server runs in DIR:
#   A1 create a forged answer file DIR/res-<nonce> (must fail: read-only mount)
#   A2 inject 'final <honest export> <nonce>' lines into the FIFO before the check (the server judges the honest export
#      and answers for that nonce; the client must ignore answers that do not name ITS file with ITS stamp)
#   A3 flood the FIFO with garbage / unknown commands
# then runs check-sound.sh --incr-dir DIR on midM1: the verdict must be REJECTED.
set -u
. "$(dirname "$(readlink -f "$0")")/common.sh"
PKG=${1:?pkg}; WD=${2:?workdir}
CS=$PKG/check/sound/check-sound.sh
PLC=$(awk '$1=="PIN" && $2=="pleanchecker_incr"{print $4}' "$PKG/check/sound/pins.env")
H=/scratch/bench-inputs/rh-mid/ref/solution.export; CH=/scratch/bench-inputs/rh-mid/challenge
MUT=${MUT:-$W/midmut/midM1.export}
rm -rf "$WD"; mkdir -p "$WD/incr"; D=$WD/incr
"$PKG/overlap/incr-server.sh" "$D" "$PLC" 16 > /dev/null 2>&1 & SRV=$!
for i in $(seq 50); do [ -p "$D/cmd" ] && [ -s "$D/server.log" -o $i -gt 10 ] && break; sleep 0.5; done
ATT=(env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session --ro-bind / / --tmpfs /home --tmpfs /tmp
     --dev /dev --proc /proc --chdir / --)
echo "== A1 forged answer file"
"${ATT[@]}" /bin/sh -c "echo '0 1 2 3 /x' > $D/res-0123456789abcdef0123456789abcdef" 2>&1 | head -2
[ -e "$D/res-0123456789abcdef0123456789abcdef" ] && echo "A1 FAIL: forged file exists" || echo "A1 ok: could not create a file in DIR"
echo "== A2 injected final lines for the honest export"
"${ATT[@]}" /bin/sh -c "for n in 0123456789abcdef0123456789abcdef ffffffffffffffffffffffffffffffff; do echo \"final $H \$n\" > $D/cmd; done" 2>&1 | head -2
echo "== A3 garbage commands${A3_EMPTY_LINE:+ (incl. an empty line)}"
"${ATT[@]}" /bin/sh -c "printf 'snap /nonexistent\nhello\nfinal\n${A3_EMPTY_LINE:+\n}' > $D/cmd" 2>&1 | head -2
sleep 2
echo "== the check of the REJECTED export with --incr-dir"
"$CS" "$MUT" "$CH/challenge.export" "$CH/comparator.json" --threads 16 --incr-dir "$D" --json "$WD/check.json" > "$WD/check.log" 2>&1
rc=$?
kill "$SRV" 2>/dev/null; wait "$SRV" 2>/dev/null
echo "check-sound rc=$rc ($(python3 -c 'import json,sys; j=json.load(open(sys.argv[1])); print(j["verdict"], "-", j["reason"][:120])' "$WD/check.json"))"
grep -E "answered|unknown command|snapshot" "$D/server.log" | cut -c1-200
[ "$rc" = 1 ] && echo "ATTACK TEST PASS (REJECTED)" || echo "ATTACK TEST FAIL (rc $rc)"
