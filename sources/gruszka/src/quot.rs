//! The quotient package. Lean's kernel builds Quot, Quot.mk, Quot.lift and
//! Quot.ind itself once Eq has the expected shape. Each quotient
//! declaration of the file is compared, structurally (binder names and
//! infos aside), with the type Lean builds, as Pestka does.

use crate::env::*;
use crate::level::ZERO;
use crate::tc::*;

/// Expected term shapes, de Bruijn indices.
enum P {
    Sort(Lp),
    Const(&'static [&'static str], &'static [Lp]),
    App(Box<P>, Box<P>),
    Pi(Box<P>, Box<P>),
    B(u32),
}
#[derive(Clone, Copy)]
enum Lp {
    Zero,
    Param(usize),
}

fn app(f: P, a: P) -> P {
    P::App(Box::new(f), Box::new(a))
}
fn apps(f: P, args: Vec<P>) -> P {
    args.into_iter().fold(f, app)
}
fn pi(d: P, b: P) -> P {
    P::Pi(Box::new(d), Box::new(b))
}
fn b(i: u32) -> P {
    P::B(i)
}
const U: &[Lp] = &[Lp::Param(0)];
const V_: &[Lp] = &[Lp::Param(1)];
fn prop() -> P {
    P::Sort(Lp::Zero)
}
/// `α → α → Prop` with α at `#a`.
fn rel(a: u32) -> P {
    pi(b(a), pi(b(a + 1), prop()))
}

impl Worker {
    pub fn find_name(&self, path: &[&str]) -> u32 {
        let mut c = susz::canon::ANON;
        for s in path {
            match self.env.st.canon.find(self.env.bytes, c, susz::canon::Part::Str(s.as_bytes())) {
                Some(x) => c = x,
                None => return NONE,
            }
        }
        c
    }

    fn lp_level(&mut self, lp: Lp, params: &[u32]) -> Option<u32> {
        match lp {
            Lp::Zero => Some(ZERO),
            Lp::Param(i) => params.get(i).map(|&n| self.lv.param(n)),
        }
    }

    fn matches(&mut self, t: u32, p: &P, params: &[u32]) -> bool {
        let k = self.tk(t);
        match p {
            P::B(i) => k == BVAR && self.tp(t) == *i,
            P::Sort(l) => k == SORT && self.lp_level(*l, params) == Some(self.tp(t)),
            P::Const(path, ls) => {
                if k != CONST || self.env.canon(self.ta(t)) != self.find_name(path) {
                    return false;
                }
                let row = self.env.row(self.ta(t));
                if row == NONE || !self.visible(row) {
                    return false;
                }
                // milestone 24s: the constant must be the one the package
                // means, not a definition or axiom under its name (Quot as
                // `fun α r => PUnit` made `Quot.ind` prove 0 = 1)
                let kind_ok = match (path.len(), path.first().copied(), path.get(1).copied()) {
                    (1, Some("Quot"), _) => matches!(self.env.consts[row as usize].kind, CKind::Quot { kind: 0 }),
                    (2, Some("Quot"), Some("mk")) => matches!(self.env.consts[row as usize].kind, CKind::Quot { kind: 1 }),
                    (1, Some("Eq"), _) => matches!(self.env.consts[row as usize].kind, CKind::Induct { .. }),
                    _ => false,
                };
                if !kind_ok {
                    return false;
                }
                let have = self.ll_get(t).to_vec();
                have.len() == ls.len() && ls.iter().zip(have.iter()).all(|(l, &h)| self.lp_level(*l, params) == Some(h))
            }
            P::App(f, a) => k == APP && self.matches(self.ta(t), f, params) && self.matches(self.tb(t), a, params),
            P::Pi(d, bd) => is_pi(k) && self.matches(self.ta(t), d, params) && self.matches(self.tb(t), bd, params),
        }
    }

    pub fn check_quot(&mut self, row: u32) -> R<()> {
        let env = self.env;
        let c = &env.consts[row as usize];
        let CKind::Quot { kind } = c.kind else { unreachable!() };
        self.setup_decl(row, 0);
        let params: Vec<u32> = c.lparams.iter().map(|&n| env.canon(n)).collect();
        // Eq: one universe, `{α : Sort u} → α → α → Prop`, one constructor
        // `Eq.refl : {α : Sort u} (a : α), Eq a a`
        let eq = env.known_row(env.known.eq);
        if eq == NONE || !self.visible(eq) {
            return reject("quotient: Eq is not declared before");
        }
        let eqc = &env.consts[eq as usize];
        let CKind::Induct { ctors, .. } = &eqc.kind else { return reject("quotient: Eq is not an inductive type") };
        if eqc.lparams.len() != 1 || ctors.len() != 1 {
            return reject("quotient: Eq has an unexpected shape");
        }
        let eq_params = [env.canon(eqc.lparams[0])];
        let eq_ty = pi(P::Sort(Lp::Param(0)), pi(b(0), pi(b(1), prop())));
        if !self.matches(eqc.ty, &eq_ty, &eq_params) {
            return reject("quotient: Eq has an unexpected type");
        }
        let refl = env.row(ctors[0]);
        if refl == NONE || env.consts[refl as usize].lparams.len() != 1 {
            return reject("quotient: Eq.refl has an unexpected shape");
        }
        let refl_params = [env.canon(env.consts[refl as usize].lparams[0])];
        let refl_ty = pi(P::Sort(Lp::Param(0)), pi(b(0), apps(P::Const(&["Eq"], U), vec![b(1), b(0), b(0)])));
        if !self.matches(env.consts[refl as usize].ty, &refl_ty, &refl_params) {
            return reject("quotient: Eq.refl has an unexpected type");
        }
        let quot = || P::Const(&["Quot"], U);
        let (name, nparams, ty): (&[&str], usize, P) = match kind {
            0 => (&["Quot"], 1, pi(P::Sort(Lp::Param(0)), pi(rel(0), P::Sort(Lp::Param(0))))),
            1 => (&["Quot", "mk"], 1, pi(P::Sort(Lp::Param(0)), pi(rel(0), pi(b(1), apps(quot(), vec![b(2), b(1)]))))),
            2 => {
                // {α : Sort u} {r} {β : Sort v} (f : α → β)
                // (h : ∀ a b, r a b → f a = f b) (q : Quot r) : β
                let h = pi(
                    b(3),
                    pi(
                        b(4),
                        pi(
                            apps(b(4), vec![b(1), b(0)]),
                            apps(P::Const(&["Eq"], V_), vec![b(4), app(b(3), b(2)), app(b(3), b(1))]),
                        ),
                    ),
                );
                let ty = pi(
                    P::Sort(Lp::Param(0)),
                    pi(
                        rel(0),
                        pi(
                            P::Sort(Lp::Param(1)),
                            pi(pi(b(2), b(1)), pi(h, pi(apps(quot(), vec![b(4), b(3)]), b(3)))),
                        ),
                    ),
                );
                (&["Quot", "lift"], 2, ty)
            }
            _ => {
                // {α : Sort u} {r} {β : Quot r → Prop}
                // (mk : ∀ a, β (Quot.mk r a)) (q : Quot r) : β q
                let mk = pi(b(2), app(b(1), apps(P::Const(&["Quot", "mk"], U), vec![b(3), b(2), b(0)])));
                let ty = pi(
                    P::Sort(Lp::Param(0)),
                    pi(
                        rel(0),
                        pi(pi(apps(quot(), vec![b(1), b(0)]), prop()), pi(mk, pi(apps(quot(), vec![b(3), b(2)]), app(b(2), b(0))))),
                    ),
                );
                (&["Quot", "ind"], 1, ty)
            }
        };
        if env.canon(c.name) != self.find_name(name) {
            return reject("quotient declaration with an unexpected name");
        }
        if params.len() != nparams {
            return reject("quotient declaration with the wrong number of universe parameters");
        }
        // K06: Lean 4.36.0's leanchecker compares each quotient record with
        // the kernel's (QuotVal ==), whose universe parameters are named
        // `u` (and `v` for Quot.lift): another name is a mismatch there.
        let want: &[&str] = if kind == 2 { &["u", "v"] } else { &["u"] };
        if params.iter().zip(want.iter()).any(|(&p, w)| p != self.find_name(&[w])) {
            return reject("quotient declaration with universe parameters not named as Lean's kernel names them");
        }
        if !self.matches(c.ty, &ty, &params) {
            return reject("quotient declaration with an unexpected type");
        }
        Ok(())
    }
}
