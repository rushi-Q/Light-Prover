#!/usr/bin/python3 -I
"""tools/ci/mktargets.py COMPARATOR_JSON > TARGETS : the export target list exactly as bin/fastverify (and the 4.36 Lake
compareIt) derives it: builtin Quot targets (if Quot.sound is permitted) ++ theorem_names ++ permitted_axioms ++ the
comparator's primitive targets ++ definition_names; one name per line (tools/ci/official-incr.sh --targets)."""
import importlib.util, json, os, sys

spec = importlib.util.spec_from_file_location("fv", os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..",
                                                                 "lib", "fastverify.py"))
fv = importlib.util.module_from_spec(spec); spec.loader.exec_module(fv)
cc = json.load(open(sys.argv[1]))
axs = list(cc["permitted_axioms"])
builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axs else []
print("\n".join(builtin + list(cc["theorem_names"]) + axs + fv.PRIMITIVES + list(cc.get("definition_names") or [])))
