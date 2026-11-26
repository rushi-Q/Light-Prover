# tests/notary/stage.sh -- sourced by run.sh / controls.sh: staged copies of check-notary.sh whose pinned binaries
# can be wrapped (the wrapper runs the real pinned binary, then tampers with its evidence), never touching check/notary/.
# Needs: FV (package root under test), NOTARY, CN, W (scratch dir).
pin_path() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$NOTARY/pins.env"; }
SG=$(pin_path selftest_good); SB=$(pin_path selftest_bad); SC=$(pin_path selftest_challenge); SCFG=$(pin_path selftest_comparator)
# mk_stage DIR [ccmp|plc|gruszka ...]: DIR/check/notary/check-notary.sh + pins.env; each named component is copied to
# DIR/check/notary/bin/<name>.real and DIR/check/notary/bin/<name> is a wrapper the caller writes (stage_wrap)
mk_stage() {
  local base=$1; shift; local s="$base/check/notary" c
  mkdir -p "$s/bin" "$base/check"
  for c in config lib toolchains; do ln -s "$FV/$c" "$base/$c"; done
  for c in sound xversion; do ln -s "$FV/check/$c" "$base/check/$c"; done
  cp "$CN" "$s/check-notary.sh"; chmod 755 "$s/check-notary.sh"
  local cc pp gg; cc=$(pin_path ccmp_notary); pp=$(pin_path pleanchecker_notary); gg=$(pin_path gruszka_r7)
  for c in "$@"; do
    case "$c" in
      ccmp) cp "$cc" "$s/bin/ccmp.real"; cc=$s/bin/ccmp;;
      plc) cp "$pp" "$s/bin/plc.real"; pp=$s/bin/plc;;
      gruszka) cp "$gg" "$s/bin/gruszka.real"; gg=$s/bin/gruszka;;
    esac
  done
  STAGE_PINS_CC=$cc; STAGE_PINS_PP=$pp; STAGE_PINS_GG=$gg; STAGE_DIR=$s
}
# write_pins: after the wrappers exist
write_pins() {
  local s=$STAGE_DIR
  chmod 755 "$s"/bin/* 2>/dev/null || true
  { grep -E '^(NOTARY_VERSION|TC36)=' "$NOTARY/pins.env"
    echo "PIN ccmp_notary $(sha256sum "$STAGE_PINS_CC" | cut -d' ' -f1) $STAGE_PINS_CC"
    echo "PIN pleanchecker_notary $(sha256sum "$STAGE_PINS_PP" | cut -d' ' -f1) $STAGE_PINS_PP"
    echo "PIN gruszka_r7 $(sha256sum "$STAGE_PINS_GG" | cut -d' ' -f1) $STAGE_PINS_GG"
    grep -E '^PIN selftest_' "$NOTARY/pins.env"; } > "$s/pins.env"
}
