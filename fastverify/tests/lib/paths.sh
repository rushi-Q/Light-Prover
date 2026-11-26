#!/bin/bash
# paths.sh (sourced by run_all.sh): the OFFICIAL tools and trusted inputs the tests compare against, taken from the package's
# own configuration (config/components.json, regenerated per machine by tools/configure.py) instead of absolute paths:
#   FV_T33  official Lean 4.33.1 toolchain prefix        FV_T36  official Lean 4.36.0 toolchain prefix (lake comparator)
#   FV_OFFICIAL_EXPORTER  official lean4export binary    FV_PACKAGES  trusted Lake workspace with materialized dependencies
# Values already set in the environment win. Every lib/ script and every x/officialflow*.sh snapshot reads these variables
# (with this installation's paths as fallback).
_fvroot=${FV_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}
eval "$(python3 -I - "$_fvroot/config/components.json" <<'PY'
import json, shlex, sys
try:
    c = json.load(open(sys.argv[1]))
except Exception:
    sys.exit(0)
out = {}
lt = c.get('lean_toolchains', {}).get('leanprover/lean4:v4.33.1', {})
if lt.get('prefix'): out['FV_T33'] = lt['prefix']
if (lt.get('official_lean4export') or {}).get('path'): out['FV_OFFICIAL_EXPORTER'] = lt['official_lean4export']['path']
if (c.get('comparator') or {}).get('prefix'): out['FV_T36'] = c['comparator']['prefix']
for k, v in out.items():
    print(f'[ -n "${{{k}:-}}" ] || export {k}={shlex.quote(v)}')
PY
)"
# trusted dependency workspace (pinned Mathlib cache): the RH challenge workspace of this installation unless given
# (<repository root>/verify/challenge when LIGHT_LEAN is not set; tests that need it SKIP when it is absent)
[ -n "${FV_PACKAGES:-}" ] || export FV_PACKAGES=${LIGHT_LEAN:-$(dirname "$_fvroot")}/verify/challenge
unset _fvroot
