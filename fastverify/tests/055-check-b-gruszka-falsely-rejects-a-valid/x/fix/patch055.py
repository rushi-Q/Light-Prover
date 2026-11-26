#!/usr/bin/env python3
"""patch055.py SRC/src/induct.rs : the proposed fix for test 055 (gruszka scan_nested_go misses BVAR-headed
applications in auxiliary constructors, e.g. `t α` with t := Box in BaseFoo's constructor)."""
import sys
p = sys.argv[1]
s = open(p).read()
# 1) split nested_found: the part after the parameter arguments are values becomes nested_found_vals
old_tail_start = "        let jllr = self.lsub_ll(f, ls);\n        // an equal occurrence already has its auxiliary type\n"
assert s.count(old_tail_start) == 1
s = s.replace(old_tail_start,
    "        let jllr = self.lsub_ll(f, ls);\n"
    "        self.nested_found_vals(ind, ds, jllr, jrow, jall)\n"
    "    }\n\n"
    "    /// 055 fix: the part of nested_found after the parameter arguments are values\n"
    "    fn nested_found_vals(&mut self, ind: &mut Ind, ds: Vec<V>, jllr: u32, jrow: u32, jall: &[u32]) -> R<()> {\n"
    "        // an equal occurrence already has its auxiliary type\n")
# 2) BVAR-headed application in scan_nested_go
anchor = "        if !args.is_empty() && self.tk(f) == CONST {\n            let jrow = self.env.row(self.ta(f));"
assert s.count(anchor) == 1
new = """        // 055 fix: a parameter of an auxiliary type applied to arguments (`t α` with t := Box in BaseFoo's
        // constructor): Lean instantiates the parameters first and sees the constant-headed `Box Foo3`
        if !args.is_empty() && self.tk(f) == BVAR && self.tp(f) >= depth {
            let mut v = self.env_get(env, self.tp(f) - depth)?;
            // (row, level list, head argument values) of the parameter's argument, if it is a constant application
            let mut head: Option<(u32, u32, Vec<V>)> = None;
            loop {
                match self.val(v) {
                    Val::Thunk { term, env: he, ls: hl } => {
                        if self.tk(term) == BVAR {
                            v = self.env_get(he, self.tp(term))?;
                            continue;
                        }
                        let mut hargs = Vec::new();
                        let mut hf = term;
                        while self.tk(hf) == APP {
                            hargs.push(self.tb(hf));
                            hf = self.ta(hf);
                        }
                        hargs.reverse();
                        if self.tk(hf) == CONST {
                            let r = self.env.row(self.ta(hf));
                            if r != NONE {
                                let mut hv = Vec::new();
                                for &a in &hargs {
                                    hv.push(self.thunk(a, he, hl)?);
                                }
                                let l = self.lsub_ll(hf, hl);
                                head = Some((r, l, hv));
                            }
                        }
                    }
                    Val::Neu { head: Head::Const(r, l), spine } => {
                        if let Some(xs) = self.app_args(spine) {
                            head = Some((r, l, xs.to_vec()));
                        }
                    }
                    _ => {}
                }
                break;
            }
            if let Some((jrow, jllr, hv)) = head {
                if self.visible(jrow) && !ind.canon.contains(&self.canon_of_row(jrow)) {
                    if let CKind::Induct { nparams: jnp, all: jall, .. } = &self.env.consts[jrow as usize].kind {
                        let jnp = *jnp as usize;
                        let jall = jall.clone();
                        let nh = hv.len().min(jnp);
                        let na = jnp - nh;
                        if args.len() >= na {
                            let mut nested = false;
                            for &x in &hv[..nh] {
                                if self.occ_val(x, &ind.canon)? {
                                    nested = true;
                                }
                            }
                            for &a in &args[..na] {
                                if self.occ_term(a, env, depth, &ind.canon)? {
                                    nested = true;
                                }
                            }
                            if nested {
                                for &a in &args[..na] {
                                    for d in 0..depth {
                                        if self.uses_var(a, d) {
                                            return reject(format!(
                                                "invalid nested inductive datatype '{}', nested inductive datatypes parameters cannot contain local variables",
                                                self.env.name_str(self.env.consts[jrow as usize].name)
                                            ));
                                        }
                                    }
                                }
                                let mut e = env;
                                for _ in 0..depth {
                                    e = self.push_env(dummy, e);
                                }
                                let mut ds: Vec<V> = hv[..nh].to_vec();
                                for &a in &args[..na] {
                                    ds.push(self.thunk(a, e, ls)?);
                                }
                                self.nested_found_vals(ind, ds, jllr, jrow, &jall)?;
                                // the remaining arguments (indices) are scanned like any subterm
                                for &a in &args[na..] {
                                    self.scan_nested(ind, a, env, ls, depth, dummy)?;
                                }
                                return Ok(());
                            }
                        }
                    }
                }
            }
        }
"""
s = s.replace(anchor, new + anchor)
open(p, "w").write(s)
print("patched")
# 3) BVAR case: a parameter bound to a closure value (a Pi/lambda argument such as `Nat → List T`) is scanned too
s = open(p).read()
old = """                    if let Val::Thunk { term, env: e2, ls: l2 } = self.val(v) {
                        return self.scan_nested(ind, term, e2, l2, 0, dummy);
                    }
"""
new = old + """                    // 055(b) fix: Pi-typed arguments are closures (Val::Clo), not thunks; Lean's instantiated
                    // constructor type contains them literally and replace_all_nested looks inside
                    if let Val::Clo { term, env: e2, ls: l2 } = self.val(v) {
                        return self.scan_nested(ind, term, e2, l2, 0, dummy);
                    }
"""
assert s.count(old) == 1
s = s.replace(old, new)
open(p, "w").write(s)
print("patched (b)")
