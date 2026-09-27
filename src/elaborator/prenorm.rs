//! Normalizing a hole's goal with the procedures behind four of Carcara's
//! own rules, before the egglog engine sees it.
//!
//! The normalizer is the bottom-up composition of exactly the procedures
//! that check `evaluate`, `poly_simp` (with `poly_simp_rel` for relations),
//! `aci_simp`, `distinct_elim` and `la_rw_eq`: a ground term is evaluated, an arithmetic
//! term is printed as its canonical polynomial, a relation is put in the
//! form `(op P c)` with `P` the scaled difference of its sides, an `and`/`or`
//! (and the associative bit-vector operators) is flattened, freed of its
//! identity element, deduplicated when idempotent and sorted, a
//! `distinct` is expanded to its pairwise disequalities, and a pair of
//! opposite bounds between the same two terms, `(and (<= t u) (<= u t))`
//! or with either bound written as a `>=`, is the equality `(= t u)`
//! (`la_rw_eq`, read on the flat conjunction after `aci_simp`, so that the
//! pair is found however the producer nested it; a bound that is not
//! spelled as the rule states it is turned round by `la_generic`,
//! `equiv_neg1`, `equiv_neg2` and `resolution`, so the certificate stays
//! within Alethe without a `*_simplify` rule).  Nothing else: what these
//! five do not reach is left to the RARE rules in egglog.
//!
//! Because each step is one of those rules applied to one subterm, the
//! derivation of a normal form is a certificate of `cong`, `trans` and rule
//! steps that the checker verifies, so the same normalization serves the
//! checking pass (a hole whose sides have the same normal form is closed)
//! and the elaboration pass (the certificate replaces the hole, or bridges
//! the hole's sides to the normal forms egglog proves equal).
//!
//! The polynomial is the checker's own (`checker::rules::polynomial`), so a
//! `poly_simp` step the normalizer emits is one the checker accepts by
//! construction.
use crate::ast::{Operator, Rc, Sort, Term, Value, pool::TermPool};
use crate::checker::rules::polynomial::{Monomial, Polynomial};
use indexmap::IndexSet;
use rug::{Integer, Rational};
use std::collections::HashMap;

/// A premise a top step's certificate needs: the `poly_simp` equality a
/// `poly_simp_rel` step is stated on.
#[derive(Clone)]
enum Premise {
    PolySimp(Rc<Term>, Rc<Term>),
}

/// One rule application at the top of a term: `(= from to)` by `rule`, with
/// the premises its certificate needs.  A `flipped` step is one whose rule
/// concludes `(= to from)` (`la_rw_eq` states the equality as the pair of
/// bounds); its certificate adds a `symm`.
#[derive(Clone)]
struct TopStep {
    rule: &'static str,
    from: Rc<Term>,
    to: Rc<Term>,
    premises: Vec<Premise>,
    flipped: bool,
    /// Set on a `la_rw_eq` fold of two bounds of a conjunction (see
    /// `la_rw_eq_fold`), whose certificate is a small chain of its own.
    fold: Option<Fold>,
    /// Set on an integer tightening (see `relation_step`), certified by a
    /// pair of `la_generic` steps rather than by `poly_simp_rel`.
    tighten: Option<Tighten>,
}

/// An integer tightening: the relation's difference scaled by `scale` has
/// integral coefficients, and its bound is not an integer (or the relation
/// is strict), so the relation is rounded or decided.  `helper` is the
/// bound `(>= P k)` a decided equality is refuted through.
#[derive(Clone)]
struct Tighten {
    scale: Rational,
    helper: Option<Rc<Term>>,
}

/// The pieces of a `la_rw_eq` fold: the two bounds of the conjunction as
/// they stand, the pair as the rule states it (`(<= t u)`, `(<= u t)`), the
/// equality `(= t u)`, and the other conjuncts.
#[derive(Clone)]
struct Fold {
    first: Rc<Term>,
    second: Rc<Term>,
    lower: Rc<Term>,
    upper: Rc<Term>,
    equality: Rc<Term>,
    rest: Vec<Rc<Term>>,
}

/// How a term's normal form is derived: the arguments' normal forms under
/// `cong`, then rule applications at the top, then the derivation of the
/// last top step's result (whose own arguments may need normalizing again).
#[derive(Clone)]
struct Derivation {
    /// The term with its arguments replaced by their normal forms, when any
    /// changed.
    cong: Option<Rc<Term>>,
    tops: Vec<TopStep>,
    /// The term the top steps end at, when it is not yet normal.
    tail: Option<Rc<Term>>,
    result: Rc<Term>,
}

pub struct Normalizer {
    derivations: HashMap<Rc<Term>, Derivation>,
    /// How many subterms changed under normalization.
    pub rewritten: usize,
}

impl Default for Normalizer {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArithSort {
    Int,
    Real,
}

fn arith_sort(pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<ArithSort> {
    match pool.sort(term).as_ref() {
        Sort::Int => Some(ArithSort::Int),
        Sort::Real => Some(ArithSort::Real),
        _ => None,
    }
}

/// Whether every argument of `op` may be dropped when repeated.
fn is_idempotent(op: Operator) -> bool {
    matches!(
        op,
        Operator::And | Operator::Or | Operator::BvAnd | Operator::BvOr
    )
}

/// The operators the `aci_simp` component handles: associative and
/// commutative, with an identity element.  `+` and `*` go through
/// `poly_simp` instead.
fn is_aci(op: Operator) -> bool {
    matches!(
        op,
        Operator::And
            | Operator::Or
            | Operator::BvAnd
            | Operator::BvOr
            | Operator::BvXor
            | Operator::BvAdd
            | Operator::BvMul
    )
}

fn identity_of(pool: &mut dyn TermPool, op: Operator, sample: &Rc<Term>) -> Option<Rc<Term>> {
    let term = match op {
        Operator::And => Term::new_bool(true),
        Operator::Or => Term::new_bool(false),
        Operator::BvAdd | Operator::BvOr | Operator::BvXor | Operator::BvMul | Operator::BvAnd => {
            let &Sort::BitVec(width) = pool.sort(sample).as_ref() else {
                return None;
            };
            match op {
                Operator::BvMul => Term::new_bv(Integer::from(1), width),
                Operator::BvAnd => Term::new_bv((Integer::from(1) << width) - 1, width),
                _ => Term::new_bv(Integer::from(0), width),
            }
        }
        _ => return None,
    };
    Some(pool.add(term))
}

impl Normalizer {
    pub fn new() -> Self {
        Self {
            derivations: HashMap::new(),
            rewritten: 0,
        }
    }

    /// `term` in normal form.
    pub fn normalize(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        if let Some(known) = self.derivations.get(term) {
            return known.result.clone();
        }
        let derivation = self.derive(pool, term);
        if derivation.result != *term {
            self.rewritten += 1;
        }
        let result = derivation.result.clone();
        self.derivations.insert(term.clone(), derivation);
        result
    }

    fn derive(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Derivation {
        let same = |t: &Rc<Term>| Derivation {
            cong: None,
            tops: Vec::new(),
            tail: None,
            result: t.clone(),
        };
        // 1. The arguments, under `cong`.
        let current = match term.as_ref() {
            Term::Op(op, args) => {
                let normal: Vec<Rc<Term>> = args.iter().map(|a| self.normalize(pool, a)).collect();
                if normal == *args {
                    term.clone()
                } else {
                    pool.add(Term::Op(*op, normal))
                }
            }
            Term::App(function, args) => {
                let normal: Vec<Rc<Term>> = args.iter().map(|a| self.normalize(pool, a)).collect();
                if normal == *args {
                    term.clone()
                } else {
                    pool.add(Term::App(function.clone(), normal))
                }
            }
            _ => return same(term),
        };
        let cong = (current != *term).then(|| current.clone());
        // 2. Rule applications at the top, each on the previous one's result.
        let mut tops = Vec::new();
        let mut at = current;
        while let Some(step) = self.top_step(pool, &at) {
            at = step.to.clone();
            tops.push(step);
            if tops.len() > 16 {
                break;
            }
        }
        // 3. The result of a top step may have arguments that are not normal
        //    (a `distinct` expands to equalities), so it is normalized again.
        let (tail, result) = if tops.is_empty() {
            (None, at)
        } else {
            let normal = self.normalize(pool, &at);
            if normal == at {
                (None, at)
            } else {
                (Some(at), normal)
            }
        };
        Derivation { cong, tops, tail, result }
    }

    /// `la_rw_eq` read backwards, on the flat conjunction: two bounds among
    /// the conjuncts that are each other's reverse -- `(<= P c)` with
    /// `(>= P c)`, or `(<= P c)` with `(<= -P -c)`, the shapes the normal
    /// forms leave a mirrored pair in -- are the equality `(= t u)` the rule
    /// states them from.  This runs *after* `aci_simp`, so that a pair meets
    /// whether the producer wrote it as its own `and` or spread it over a
    /// larger one: cvc5 flattens `(and (and (<= x 2) (>= x 2)) p)` to
    /// `(and p (<= x 2) (>= x 2))`, and read before flattening the pair
    /// folded on one side only, which sent 176 closable holes of one
    /// QF_LRA proof to egglog as `(= (and equalities) (and bounds))` goals.
    /// The certificate regroups the pair by `aci_simp`, turns each bound
    /// into the rule's spelling by `la_generic` where needed, applies
    /// `la_rw_eq` under `cong`, and the equality is then normalized like any
    /// other.
    fn la_rw_eq_fold(
        &mut self,
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        args: &[Rc<Term>],
    ) -> Option<TopStep> {
        // A non-strict bound as its two sides and whether it is a `>=`.
        fn bound(term: &Rc<Term>) -> Option<(&Rc<Term>, &Rc<Term>, bool)> {
            match term.as_ref() {
                Term::Op(Operator::LessEq, args) if args.len() == 2 => {
                    Some((&args[0], &args[1], false))
                }
                Term::Op(Operator::GreaterEq, args) if args.len() == 2 => {
                    Some((&args[0], &args[1], true))
                }
                _ => None,
            }
        }
        // The bound as `Q <= 0`.
        let at_most_zero = |lhs: &Rc<Term>, rhs: &Rc<Term>, geq: bool| {
            if geq {
                Polynomial::from_term(rhs).sub(Polynomial::from_term(lhs))
            } else {
                Polynomial::from_term(lhs).sub(Polynomial::from_term(rhs))
            }
        };
        for i in 0..args.len() {
            let Some((lhs_i, rhs_i, geq_i)) = bound(&args[i]) else {
                continue;
            };
            if arith_sort(pool, lhs_i).is_none() {
                continue;
            }
            let q_i = at_most_zero(lhs_i, rhs_i, geq_i);
            for j in (i + 1)..args.len() {
                let Some((lhs_j, rhs_j, geq_j)) = bound(&args[j]) else {
                    continue;
                };
                // The second bound reversed, as `R <= 0`: the pair is an
                // equality exactly when `R` is `Q`.
                let r_j = at_most_zero(lhs_j, rhs_j, !geq_j);
                if !q_i.clone().sub(r_j).is_zero() {
                    continue;
                }
                let (t, u) = if geq_i {
                    (rhs_i.clone(), lhs_i.clone())
                } else {
                    (lhs_i.clone(), rhs_i.clone())
                };
                let lower = pool.add(Term::Op(Operator::LessEq, vec![t.clone(), u.clone()]));
                let upper = pool.add(Term::Op(Operator::LessEq, vec![u.clone(), t.clone()]));
                let equality = pool.add(Term::Op(Operator::Equals, vec![t, u]));
                let rest: Vec<Rc<Term>> = args
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| *k != i && *k != j)
                    .map(|(_, a)| a.clone())
                    .collect();
                let to = if rest.is_empty() {
                    equality.clone()
                } else {
                    let mut conjuncts = Vec::with_capacity(rest.len() + 1);
                    conjuncts.push(equality.clone());
                    conjuncts.extend(rest.iter().cloned());
                    pool.add(Term::Op(Operator::And, conjuncts))
                };
                return Some(TopStep {
                    rule: "la_rw_eq",
                    from: term.clone(),
                    to,
                    premises: Vec::new(),
                    flipped: false,
                    fold: Some(Fold {
                        first: args[i].clone(),
                        second: args[j].clone(),
                        lower,
                        upper,
                        equality,
                        rest,
                    }),
                    tighten: None,
                });
            }
        }
        None
    }

    /// One rule applied at the top of `term`, whose arguments are normal.
    fn top_step(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<TopStep> {
        use Operator::*;
        let Term::Op(op, args) = term.as_ref() else {
            return None;
        };
        let step = |rule, to: Rc<Term>| {
            (to != *term).then(|| TopStep {
                rule,
                from: term.clone(),
                to,
                premises: Vec::new(),
                flipped: false,
                fold: None,
                tighten: None,
            })
        };
        // `evaluate`: a ground term is its value.
        if args.iter().all(|a| Value::from_term(a).is_some()) {
            let value = term.evaluate(pool);
            if value != *term {
                return step("evaluate", value);
            }
        }
        match op {
            Add | Sub | Mult | RealDiv | ToReal => {
                let sort = arith_sort(pool, term)?;
                let poly = Polynomial::from_term(term);
                let canonical = self.term_of_polynomial(pool, &poly, sort);
                step("poly_simp", canonical)
            }
            LessThan | LessEq | GreaterThan | GreaterEq | Equals if args.len() == 2 => {
                let sort = match (arith_sort(pool, &args[0])?, arith_sort(pool, &args[1])?) {
                    (ArithSort::Int, ArithSort::Int) => ArithSort::Int,
                    _ => ArithSort::Real,
                };
                self.relation_step(pool, term, *op, &args[0], &args[1], sort)
            }
            Distinct => step("distinct_elim", self.distinct_expansion(pool, args)),
            _ if is_aci(*op) => {
                let canonical = self.aci_canonical(pool, *op, args);
                match step("aci_simp", canonical) {
                    Some(step) => Some(step),
                    // On the flat, canonical conjunction: a mirrored pair
                    // of bounds is an equality.
                    None if *op == And => self.la_rw_eq_fold(pool, term, args),
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// `(op x1 x2)` as `(op P c)`: the difference of the sides scaled by a
    /// positive factor (integral coefficients of gcd 1 for Int, leading
    /// coefficient of absolute value 1 for Real), its constant moved to the
    /// right.  The `poly_simp` premise `(= (* s (- x1 x2)) (* 1 (- P c)))`
    /// is what `poly_simp_rel` needs.
    fn relation_step(
        &mut self,
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        op: Operator,
        x1: &Rc<Term>,
        x2: &Rc<Term>,
        sort: ArithSort,
    ) -> Option<TopStep> {
        let difference = Polynomial::from_term(x1).sub(Polynomial::from_term(x2));
        // Orientation: `<=` and `<` are the `>=` and `>` of the negated
        // difference, so that a bound and its mirror image (cvc5's
        // `(<= s t)` against `(>= (- t s) 0)`) reach one normal form.  A
        // mirrored relation is certified by a `la_generic` pair, as a
        // tightening is; `poly_simp_rel` keeps the relation symbol.
        let (op, difference, mirrored) = match op {
            Operator::LessEq | Operator::LessThan => {
                let mut negated = difference;
                for c in negated.0.values_mut() {
                    *c = Rational::from(-c.clone());
                }
                negated.1 = Rational::from(-negated.1);
                let op = if op == Operator::LessEq {
                    Operator::GreaterEq
                } else {
                    Operator::GreaterThan
                };
                (op, negated, true)
            }
            _ => (op, difference, false),
        };
        let constant = difference.1.clone();
        let mut poly = difference;
        poly.1 = Rational::new();
        let scale = if poly.0.is_empty() {
            Rational::from(1)
        } else {
            match sort {
                ArithSort::Int => {
                    let mut lcm = Integer::from(1);
                    for c in poly.0.values() {
                        lcm.lcm_mut(c.denom());
                    }
                    let mut gcd = Integer::from(0);
                    for c in poly.0.values() {
                        let scaled = Rational::from(c.clone() * Rational::from(&lcm));
                        gcd.gcd_mut(scaled.numer());
                    }
                    Rational::from((lcm, gcd))
                }
                ArithSort::Real => {
                    let (_, leading) = Self::sorted_monomials(&poly)[0];
                    Rational::from(1) / leading.clone().abs()
                }
            }
        };
        // An equality may be scaled by a negative factor (`poly_simp_rel`
        // allows it for `=` only), which fixes its orientation: a positive
        // leading coefficient.
        let scale = if op == Operator::Equals
            && !poly.0.is_empty()
            && *Self::sorted_monomials(&poly)[0].1 < 0
        {
            -scale
        } else {
            scale
        };
        for c in poly.0.values_mut() {
            *c *= &scale;
        }
        let y1 = self.term_of_polynomial(pool, &poly, sort);
        let bound = Rational::from(-constant * &scale);
        // Integer tightening: over Int, a relation whose scaled bound is not
        // an integer is rounded (`>=` up, `<=` down) or decided (`=` is
        // `false`), and a strict relation becomes the non-strict one of the
        // adjacent integer.  Certified by `la_generic`, whose integer
        // strengthening does the rounding, so it stays a core-rule step.
        if sort == ArithSort::Int && !poly.0.is_empty() {
            let integral = bound.is_integer();
            let floor = || Integer::from(bound.floor_ref());
            let ceil = || Integer::from(bound.ceil_ref());
            let relation = |pool: &mut dyn TermPool, op, k: Integer| {
                let k = pool.add(Term::new_int(k));
                pool.add(Term::Op(op, vec![y1.clone(), k]))
            };
            let (to, helper) = match op {
                Operator::Equals if !integral => {
                    let helper = relation(pool, Operator::GreaterEq, ceil());
                    (Some(pool.bool_false()), Some(helper))
                }
                Operator::GreaterEq if !integral => {
                    (Some(relation(pool, Operator::GreaterEq, ceil())), None)
                }
                Operator::LessEq if !integral => {
                    (Some(relation(pool, Operator::LessEq, floor())), None)
                }
                Operator::GreaterThan => {
                    (Some(relation(pool, Operator::GreaterEq, floor() + 1)), None)
                }
                Operator::LessThan => {
                    (Some(relation(pool, Operator::LessEq, ceil() - 1)), None)
                }
                _ => (None, None),
            };
            if let Some(to) = to {
                return Some(TopStep {
                    rule: "la_generic",
                    from: term.clone(),
                    to,
                    premises: Vec::new(),
                    flipped: false,
                    fold: None,
                    tighten: Some(Tighten { scale, helper }),
                });
            }
        }
        let y2 = self.constant_term(pool, &bound, sort);
        if mirrored {
            let to = pool.add(Term::Op(op, vec![y1, y2]));
            return Some(TopStep {
                rule: "la_generic",
                from: term.clone(),
                to,
                premises: Vec::new(),
                flipped: false,
                fold: None,
                tighten: Some(Tighten { scale, helper: None }),
            });
        }
        if y1 == *x1 && y2 == *x2 {
            return None;
        }
        let to = pool.add(Term::Op(op, vec![y1.clone(), y2.clone()]));
        // the premise's sides, `(* s (- x1 x2))` and `(* 1 (- y1 y2))`
        let s = self.constant_term(pool, &scale, sort);
        let one = self.constant_term(pool, &Rational::from(1), sort);
        let left = pool.add(Term::Op(Operator::Sub, vec![x1.clone(), x2.clone()]));
        let left = pool.add(Term::Op(Operator::Mult, vec![s, left]));
        let right = pool.add(Term::Op(Operator::Sub, vec![y1, y2]));
        let right = pool.add(Term::Op(Operator::Mult, vec![one, right]));
        Some(TopStep {
            rule: "poly_simp_rel",
            from: term.clone(),
            to,
            premises: vec![Premise::PolySimp(left, right)],
            flipped: false,
            fold: None,
            tighten: None,
        })
    }

    /// `distinct_elim`'s expansion: the disequality of two arguments, the
    /// conjunction of the pairwise disequalities of more (`false` for more
    /// than two Booleans).
    fn distinct_expansion(&mut self, pool: &mut dyn TermPool, args: &[Rc<Term>]) -> Rc<Term> {
        let disequality = |pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>| {
            let equality = pool.add(Term::Op(Operator::Equals, vec![a.clone(), b.clone()]));
            pool.add(Term::Op(Operator::Not, vec![equality]))
        };
        match args {
            [a, b] => disequality(pool, a, b),
            _ if pool.sort(&args[0]).as_ref() == &Sort::Bool => pool.add(Term::new_bool(false)),
            _ => {
                let mut conjuncts = Vec::with_capacity(args.len() * (args.len() - 1) / 2);
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        conjuncts.push(disequality(pool, &args[i], &args[j]));
                    }
                }
                pool.add(Term::Op(Operator::And, conjuncts))
            }
        }
    }

    /// `aci_simp`'s canonical form: flattened, without the identity element,
    /// deduplicated when the operator is idempotent, in pointer order.
    fn aci_canonical(
        &mut self,
        pool: &mut dyn TermPool,
        op: Operator,
        args: &[Rc<Term>],
    ) -> Rc<Term> {
        let identity = identity_of(pool, op, &args[0]);
        let mut flat: Vec<Rc<Term>> = Vec::new();
        for arg in args {
            match arg.as_ref() {
                Term::Op(inner, inner_args) if *inner == op => {
                    flat.extend(inner_args.iter().cloned())
                }
                _ => flat.push(arg.clone()),
            }
        }
        if let Some(identity) = &identity {
            flat.retain(|a| a != identity);
        }
        if is_idempotent(op) {
            let set: IndexSet<Rc<Term>> = flat.into_iter().collect();
            flat = set.into_iter().collect();
        }
        flat.sort_by_key(Rc::as_ptr);
        match flat.len() {
            0 => identity.unwrap_or_else(|| pool.add(Term::Op(op, Vec::new()))),
            1 => flat.pop().unwrap(),
            _ => pool.add(Term::Op(op, flat)),
        }
    }

    /// The monomials in canonical order: fewer atoms first, then by the
    /// atoms' pointers.
    fn sorted_monomials(poly: &Polynomial) -> Vec<(&Monomial, &Rational)> {
        let mut entries: Vec<_> = poly.0.iter().collect();
        entries.sort_by(|(a, _), (b, _)| {
            a.0.len()
                .cmp(&b.0.len())
                .then_with(|| a.0.iter().map(Rc::as_ptr).cmp(b.0.iter().map(Rc::as_ptr)))
        });
        entries
    }

    fn constant_term(
        &self,
        pool: &mut dyn TermPool,
        value: &Rational,
        sort: ArithSort,
    ) -> Rc<Term> {
        match sort {
            ArithSort::Int if value.is_integer() => pool.add(Term::new_int(value.numer().clone())),
            _ => pool.add(Term::new_real(value.clone())),
        }
    }

    /// The canonical term of a polynomial: the monomials in order, each an
    /// atom or a product `(* c a1 ... an)`, summed, the constant last.  In a
    /// Real polynomial an Int atom is wrapped in `to_real`, which the
    /// checker's polynomial sees through.
    fn term_of_polynomial(
        &self,
        pool: &mut dyn TermPool,
        poly: &Polynomial,
        sort: ArithSort,
    ) -> Rc<Term> {
        let mut terms: Vec<Rc<Term>> = Vec::new();
        for (monomial, coefficient) in Self::sorted_monomials(poly) {
            let mut factors: Vec<Rc<Term>> = Vec::new();
            if *coefficient != 1 {
                factors.push(self.constant_term(pool, coefficient, sort));
            }
            for atom in &monomial.0 {
                let atom =
                    if sort == ArithSort::Real && arith_sort(pool, atom) == Some(ArithSort::Int) {
                        pool.add(Term::Op(Operator::ToReal, vec![atom.clone()]))
                    } else {
                        atom.clone()
                    };
                factors.push(atom);
            }
            terms.push(if factors.len() == 1 {
                factors.pop().unwrap()
            } else {
                pool.add(Term::Op(Operator::Mult, factors))
            });
        }
        if poly.1 != 0 || terms.is_empty() {
            terms.push(self.constant_term(pool, &poly.1, sort));
        }
        match terms.len() {
            1 => terms.pop().unwrap(),
            _ => pool.add(Term::Op(Operator::Add, terms)),
        }
    }

    /// The certificate of `(= lhs rhs)` for a hole whose sides have the same
    /// normal form: Alethe steps numbered `{id}.1`, `{id}.2`, ... whose last
    /// step concludes the equality.  `None` when the sides differ.
    pub fn certificate(
        &mut self,
        pool: &mut dyn TermPool,
        id: &str,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
    ) -> Option<Vec<String>> {
        let left = self.normalize(pool, lhs);
        let right = self.normalize(pool, rhs);
        if left != right {
            return None;
        }
        let mut emitter = Emitter {
            prefix: id.to_owned(),
            names: crate::ast::printer::SharedNames::new(format!("@{}.b", id)),
            steps: Vec::new(),
            memo: HashMap::new(),
        };
        let left_step = self.emit(pool, &mut emitter, lhs);
        let right_step = self.emit(pool, &mut emitter, rhs);
        match (left_step, right_step) {
            (None, None) => {
                emitter.emit(pool, lhs, rhs, "refl", &[]);
            }
            (Some(_), None) => {}
            (None, Some(r)) => {
                emitter.emit(pool, lhs, rhs, "symm", &[r]);
            }
            (Some(l), Some(r)) => {
                let flipped = emitter.emit(pool, &left, rhs, "symm", &[r]);
                emitter.emit(pool, lhs, rhs, "trans", &[l, flipped]);
            }
        }
        Some(emitter.steps)
    }

    /// The steps bridging `lhs` and `rhs` to their normal forms and egglog's
    /// proof of the normal forms' equality (`inner`, steps concluding
    /// `(= left right)` numbered from `{id}.1`): the combined certificate,
    /// concluding `(= lhs rhs)`.
    pub fn bridge(
        &mut self,
        pool: &mut dyn TermPool,
        id: &str,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        inner: Vec<String>,
    ) -> Vec<String> {
        let left = self.normalize(pool, lhs);
        let right = self.normalize(pool, rhs);
        let inner_last = super::rare_hole::last_step_id(&inner, id);
        let mut emitter = Emitter {
            prefix: id.to_owned(),
            names: crate::ast::printer::SharedNames::new(format!("@{}.b", id)),
            steps: inner,
            memo: HashMap::new(),
        };
        let mut chain: Vec<String> = Vec::new();
        if let Some(l) = self.emit(pool, &mut emitter, lhs) {
            chain.push(l);
        }
        chain.push(inner_last);
        if let Some(r) = self.emit(pool, &mut emitter, rhs) {
            chain.push(emitter.emit(pool, &right, rhs, "symm", &[r]));
        }
        if chain.len() > 1 {
            emitter.emit(pool, lhs, rhs, "trans", &chain);
        }
        let _ = left;
        emitter.steps
    }

    /// Emits the derivation of `term`'s normal form and returns the id of
    /// the step concluding `(= term normal)`, or `None` when it is normal.
    fn emit(
        &mut self,
        pool: &mut dyn TermPool,
        emitter: &mut Emitter,
        term: &Rc<Term>,
    ) -> Option<String> {
        if let Some(known) = emitter.memo.get(term) {
            return known.clone();
        }
        let derivation = match self.derivations.get(term) {
            Some(d) => d.clone(),
            None => {
                self.normalize(pool, term);
                self.derivations[term].clone()
            }
        };
        let result = derivation.result.clone();
        let step = if result == *term {
            None
        } else {
            let mut chain: Vec<String> = Vec::new();
            let mut at = term.clone();
            if let Some(congruent) = &derivation.cong {
                let (Term::Op(_, args) | Term::App(_, args)) = term.as_ref() else {
                    unreachable!("a cong derivation is over an application")
                };
                let (Term::Op(_, normal) | Term::App(_, normal)) = congruent.as_ref() else {
                    unreachable!()
                };
                let mut premises = Vec::new();
                for (arg, its_normal) in args.iter().zip(normal.iter()) {
                    if arg != its_normal {
                        premises.push(
                            self.emit(pool, emitter, arg)
                                .expect("a changed argument has a derivation"),
                        );
                    }
                }
                chain.push(emitter.emit(pool, term, congruent, "cong", &premises));
                at = congruent.clone();
            }
            for top in &derivation.tops {
                if let Some(fold) = &top.fold {
                    chain.push(emitter.emit_fold(pool, &top.from, &top.to, fold));
                    at = top.to.clone();
                    continue;
                }
                if let Some(tighten) = &top.tighten {
                    chain.push(emitter.emit_tighten(pool, &top.from, &top.to, tighten));
                    at = top.to.clone();
                    continue;
                }
                let premises: Vec<String> = top
                    .premises
                    .iter()
                    .map(|premise| match premise {
                        Premise::PolySimp(left, right) => {
                            emitter.emit(pool, left, right, "poly_simp", &[])
                        }
                    })
                    .collect();
                let id = if top.flipped {
                    let stated = emitter.emit(pool, &top.to, &top.from, top.rule, &premises);
                    emitter.emit(pool, &top.from, &top.to, "symm", &[stated])
                } else {
                    emitter.emit(pool, &top.from, &top.to, top.rule, &premises)
                };
                chain.push(id);
                at = top.to.clone();
            }
            if let Some(tail) = &derivation.tail {
                if let Some(id) = self.emit(pool, emitter, tail) {
                    chain.push(id);
                }
            }
            let _ = at;
            Some(if chain.len() == 1 {
                chain.pop().unwrap()
            } else {
                emitter.emit(pool, term, &result, "trans", &chain)
            })
        };
        emitter.memo.insert(term.clone(), step.clone());
        step
    }
}

/// Numbered Alethe steps under a hole's id.
struct Emitter {
    prefix: String,
    steps: Vec<String>,
    memo: HashMap<Rc<Term>, Option<String>>,
    /// The steps' terms are printed with sharing: no term as a tree.
    names: crate::ast::printer::SharedNames,
}

impl Emitter {
    fn emit(
        &mut self,
        _pool: &mut dyn TermPool,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
        rule: &str,
        premises: &[String],
    ) -> String {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        let (left, right) = (self.names.print(lhs), self.names.print(rhs));
        self.steps.push(format!(
            "(step {id} (cl (= {left} {right})) :rule {rule}{premises})"
        ));
        id
    }

    fn emit_clause(
        &mut self,
        literals: &str,
        rule: &str,
        premises: &[String],
        args: &str,
    ) -> String {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        let args = if args.is_empty() {
            String::new()
        } else {
            format!(" :args ({args})")
        };
        self.steps.push(format!(
            "(step {id} (cl {literals}) :rule {rule}{premises}{args})"
        ));
        id
    }

    /// `(= a b)` for a bound `a` and its mirror image `b` (`(>= x y)` and
    /// `(<= y x)`, or the reverse): each implies the other by `la_generic`,
    /// and the two implications make the equivalence through the
    /// `equiv_neg` tautologies and resolution.  Returns the last step's id.
    /// The certificate of a `la_rw_eq` fold, concluding `(= from to)`: the
    /// flat conjunction regrouped so the pair is its own `and` (`aci_simp`),
    /// each bound of the pair turned into the rule's spelling where it
    /// differs (`la_generic`, under `cong`), `la_rw_eq` reversed by `symm`,
    /// and the pair replaced by the equality under `cong`.
    fn emit_fold(
        &mut self,
        pool: &mut dyn TermPool,
        from: &Rc<Term>,
        to: &Rc<Term>,
        fold: &Fold,
    ) -> String {
        let pair = pool.add(Term::Op(
            Operator::And,
            vec![fold.first.clone(), fold.second.clone()],
        ));
        let stated = pool.add(Term::Op(
            Operator::And,
            vec![fold.lower.clone(), fold.upper.clone()],
        ));
        let grouped = (!fold.rest.is_empty()).then(|| {
            let mut conjuncts = Vec::with_capacity(fold.rest.len() + 1);
            conjuncts.push(pair.clone());
            conjuncts.extend(fold.rest.iter().cloned());
            pool.add(Term::Op(Operator::And, conjuncts))
        });
        // pair = equality
        let mut pair_chain = Vec::new();
        if pair != stated {
            let mut premises = Vec::new();
            if fold.first != fold.lower {
                premises.push(self.emit_bound_flip(pool, &fold.first, &fold.lower));
            }
            if fold.second != fold.upper {
                premises.push(self.emit_bound_flip(pool, &fold.second, &fold.upper));
            }
            pair_chain.push(self.emit(pool, &pair, &stated, "cong", &premises));
        }
        let rule = self.emit(pool, &fold.equality, &stated, "la_rw_eq", &[]);
        pair_chain.push(self.emit(pool, &stated, &fold.equality, "symm", &[rule]));
        let pair_step = if pair_chain.len() == 1 {
            pair_chain.pop().unwrap()
        } else {
            self.emit(pool, &pair, &fold.equality, "trans", &pair_chain)
        };
        match grouped {
            None => pair_step,
            Some(grouped) => {
                let regrouped = self.emit(pool, from, &grouped, "aci_simp", &[]);
                let replaced = self.emit(pool, &grouped, to, "cong", &[pair_step]);
                self.emit(pool, from, to, "trans", &[regrouped, replaced])
            }
        }
    }

    fn emit_bound_flip(&mut self, pool: &mut dyn TermPool, a: &Rc<Term>, b: &Rc<Term>) -> String {
        self.emit_equivalence(pool, a, b, "1.0 1.0", "1.0 1.0")
    }

    /// The certificate of an integer tightening `(= from to)`: the two
    /// relations imply each other by `la_generic` (the stated relation with
    /// the scale as its coefficient, the tightened one with 1), or, for an
    /// equality decided `false`, the stated equality refutes the helper
    /// bound both ways, and `(= from false)` follows from `(not from)` by
    /// `equiv_simplify` and `equiv2`.
    fn emit_tighten(
        &mut self,
        pool: &mut dyn TermPool,
        from: &Rc<Term>,
        to: &Rc<Term>,
        tighten: &Tighten,
    ) -> String {
        let scale = tighten.scale.to_string();
        let Some(helper) = &tighten.helper else {
            return self.emit_equivalence(
                pool,
                from,
                to,
                &format!("{scale} 1"),
                &format!("1 {scale}"),
            );
        };
        let negated_scale = Rational::from(-tighten.scale.clone()).to_string();
        // Each mention printed afresh: the first defines the shared names,
        // the later ones use them.
        let text = format!("(not {}) {}", self.names.print(from), self.names.print(helper));
        let above = self.emit_clause(&text, "la_generic", &[], &format!("{scale} 1"));
        let text = format!("(not {}) (not {})", self.names.print(from), self.names.print(helper));
        let below = self.emit_clause(&text, "la_generic", &[], &format!("{negated_scale} 1"));
        let text = format!("(not {})", self.names.print(from));
        let refuted = self.emit_clause(&text, "resolution", &[above, below], "");
        let text = format!("(= (= {} false) (not {}))", self.names.print(from), self.names.print(from));
        let simplified = self.emit_clause(&text, "equiv_simplify", &[], "");
        let text = format!("(= {} false) (not (not {}))", self.names.print(from), self.names.print(from));
        let split = self.emit_clause(&text, "equiv2", &[simplified], "");
        self.emit(pool, from, to, "resolution", &[split, refuted])
    }

    /// `(= a b)` from `(cl (not a) b)` and `(cl (not b) a)`, each by
    /// `la_generic` with the given coefficients, through the `equiv_neg`
    /// tautologies and resolution.  Returns the last step's id.
    fn emit_equivalence(
        &mut self,
        pool: &mut dyn TermPool,
        a: &Rc<Term>,
        b: &Rc<Term>,
        args_a_b: &str,
        args_b_a: &str,
    ) -> String {
        // Each mention printed afresh: the first defines the shared names,
        // the later ones use them.
        let text = format!("(not {}) {}", self.names.print(a), self.names.print(b));
        let a_implies_b = self.emit_clause(&text, "la_generic", &[], args_a_b);
        let text = format!("(not {}) {}", self.names.print(b), self.names.print(a));
        let b_implies_a = self.emit_clause(&text, "la_generic", &[], args_b_a);
        let (x, y) = (self.names.print(a), self.names.print(b));
        let (x2, y2) = (self.names.print(a), self.names.print(b));
        let text = format!("(= {x} {y}) {x2} {y2}");
        let neg2 = self.emit_clause(&text, "equiv_neg2", &[], "");
        let (x, y) = (self.names.print(a), self.names.print(b));
        let y2 = self.names.print(b);
        let text = format!("(= {x} {y}) {y2}");
        let with_b = self.emit_clause(&text, "resolution", &[neg2, a_implies_b], "");
        let (x, y) = (self.names.print(a), self.names.print(b));
        let (x2, y2) = (self.names.print(a), self.names.print(b));
        let text = format!("(= {x} {y}) (not {x2}) (not {y2})");
        let neg1 = self.emit_clause(&text, "equiv_neg1", &[], "");
        let (x, y) = (self.names.print(a), self.names.print(b));
        let y2 = self.names.print(b);
        let text = format!("(= {x} {y}) (not {y2})");
        let with_not_b = self.emit_clause(&text, "resolution", &[neg1, b_implies_a], "");
        let _ = pool;
        self.emit(pool, a, b, "resolution", &[with_b, with_not_b])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    const INTS: &str = "(declare-const x Int) (declare-const y Int) (declare-const z Int) (declare-const p Bool) (declare-const q Bool) (declare-fun f (Int) Int)";
    const REALS: &str = "(declare-const a Real) (declare-const b Real) (declare-const x Int)";

    fn parse(
        problem: &str,
        lhs: &str,
        rhs: &str,
    ) -> (
        crate::ast::Problem,
        Rc<Term>,
        Rc<Term>,
        crate::ast::pool::PrimitivePool,
    ) {
        let problem_text = format!("{problem}\n(assert (= {lhs} {rhs}))\n");
        let proof = format!("(assume h0 (= {lhs} {rhs}))\n");
        let (problem, proof, _, pool) = parser::parse_instance(
            parser::Source::new(std::path::Path::new("<p>"), &problem_text),
            parser::Source::new(std::path::Path::new("<a>"), &proof),
            None,
            parser::Config::new().allow_int_real_subtyping(true),
        )
        .expect("parses");
        let crate::ast::ProofCommand::Assume { term, .. } = &proof.commands[0] else {
            panic!("expected an assume");
        };
        let (_, l, r) = crate::rare::util::get_equational_terms(term).expect("equality");
        (problem, l.clone(), r.clone(), pool)
    }

    /// Normalizes `lhs` and `rhs` parsed against `problem`, returning
    /// whether they coincide and their printed normal forms.
    fn same(problem: &str, lhs: &str, rhs: &str) -> (bool, String, String) {
        let (_, l, r, mut pool) = parse(problem, lhs, rhs);
        let mut normalizer = Normalizer::new();
        let nl = normalizer.normalize(&mut pool, &l);
        let nr = normalizer.normalize(&mut pool, &r);
        (nl == nr, format!("{nl:#}"), format!("{nr:#}"))
    }

    /// The certificate of `(= lhs rhs)`, checked by the checker.
    fn certified(problem: &str, lhs: &str, rhs: &str) -> Result<usize, String> {
        let (problem_ast, l, r, mut pool) = parse(problem, lhs, rhs);
        let mut normalizer = Normalizer::new();
        let steps = normalizer
            .certificate(&mut pool, "t1", &l, &r)
            .ok_or_else(|| "sides differ".to_owned())?;
        let negated = format!("(not (= {lhs} {rhs}))");
        let proof = format!(
            "(assume t1.h {negated})\n{}\n(step t1.{} (cl) :rule resolution :premises (t1.{} t1.h))\n",
            steps.join("\n"),
            steps.len() + 1,
            steps.len()
        );
        let problem_text = format!("{problem}\n(assert {negated})\n");
        let (problem_parsed, proof_parsed, _) = parser::parse_instance_with_pool(
            parser::Source::new(std::path::Path::new("<p>"), &problem_text),
            parser::Source::new(std::path::Path::new("<c>"), &proof),
            None,
            parser::Config::new().allow_int_real_subtyping(true),
            &mut pool,
        )
        .map_err(|e| format!("certificate does not parse: {e}\n{proof}"))?;
        let _ = problem_ast;
        let rules = crate::ast::rare_rules::Rules::default();
        let mut checker =
            crate::checker::ProofChecker::new(&mut pool, &rules, crate::checker::Config::new());
        match checker.check(&problem_parsed, &proof_parsed) {
            Ok(_) => Ok(steps.len()),
            Err(e) => Err(format!("certificate rejected: {e}\n{proof}")),
        }
    }

    #[test]
    fn equivalent_sides_coincide() {
        for (problem, lhs, rhs) in [
            (INTS, "(* 4 256)", "1024"),
            (INTS, "(+ 0 1536 -1024 -1024 -512 -512 512 512 512)", "0"),
            (INTS, "(+ x y x)", "(+ (* 2 x) y)"),
            (INTS, "(- x y)", "(+ x (* (- 1) y))"),
            (INTS, "(* (+ x 1) (+ x 1))", "(+ (* x x) (* 2 x) 1)"),
            (INTS, "(< x y)", "(< (- x y) 0)"),
            (INTS, "(> (* 2 x) 3)", "(> (* 2 x) 3)"),
            (
                INTS,
                "(>= (* -2 x) (* -4 y))",
                "(>= (+ (* -1 x) (* 2 y)) 0)",
            ),
            (INTS, "(= x y)", "(= (- y x) 0)"),
            (INTS, "(and p true q p)", "(and q p)"),
            (INTS, "(or p (or q p) false)", "(or q p)"),
            (INTS, "(and (and p q) (and q p))", "(and p q)"),
            (INTS, "(distinct x y)", "(not (= x y))"),
            (
                INTS,
                "(distinct x y z)",
                "(and (not (= y x)) (not (= z x)) (not (= z y)))",
            ),
            (INTS, "(f (+ x 0))", "(f x)"),
            (INTS, "(<= 2 3)", "true"),
            (INTS, "(and p (<= x x))", "p"),
            (REALS, "(>= 0.0 (/ (- 1) 1024))", "true"),
            (
                REALS,
                "(* (/ 1 2) (to_real (+ x (* 2 x))))",
                "(* (/ 3 2) (to_real x))",
            ),
            (REALS, "(< (* 2.0 a) b)", "(< (+ a (* (- 0.5) b)) 0.0)"),
            (REALS, "(= (- 1.0) (- 1))", "true"),
            (REALS, "(<= 1 a)", "(<= (- a) (- 1.0))"),
            // veriT's `la_rw_eq` shapes
            (INTS, "(and (<= x y) (<= y x))", "(= x y)"),
            (INTS, "(and (<= y x) (<= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (<= 0 x) (<= x 0)))"),
            (INTS, "(not (= x y))", "(not (and (<= x y) (<= y x)))"),
            (
                INTS,
                "(ite p (= 1 x) (= 0 x))",
                "(ite p (and (<= 1 x) (<= x 1)) (and (<= 0 x) (<= x 0)))",
            ),
            (
                INTS,
                "(and p q (= 0 (+ x (* (- 2) y))))",
                "(and p q (and (<= 0 (+ x (* (- 2) y))) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (<= a b) (<= b a))", "(= (- a b) 0.0)"),
            // cvc5's `arith-eq-elim` shape, and the other ways round
            (INTS, "(and (>= x y) (<= x y))", "(= x y)"),
            // the pair nested by the producer against the pair flattened
            (INTS, "(and (and (<= x 2) (>= x 2)) p)", "(and p (<= x 2) (>= x 2))"),
            (INTS, "(and (and (<= x 2) (>= x 2)) p)", "(and p (= x 2))"),
            (INTS, "(and p (<= x 2) q (>= x 2))", "(and (= x 2) q p)"),
            (REALS, "(and (and (<= a b) (>= a b)) (= x 1))", "(and (= x 1) (= (- a b) 0.0))"),
            (INTS, "(and (<= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= y x) (>= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (>= x 0) (<= x 0)))"),
            (REALS, "(and (>= a b) (<= a b))", "(= (- a b) 0.0)"),
        ] {
            let (equal, nl, nr) = same(problem, lhs, rhs);
            assert!(equal, "{lhs} and {rhs} normalize to {nl} and {nr}");
        }
    }

    #[test]
    fn different_sides_stay_apart() {
        for (problem, lhs, rhs) in [
            (INTS, "(>= x 1)", "(>= x 2)"),
            (INTS, "(+ x y)", "(+ x z)"),
            (INTS, "(and p q)", "(or p q)"),
            (INTS, "(* x y)", "(* x x)"),
            (INTS, "(and p (not p))", "false"),
            (INTS, "(=> p q)", "(or (not p) q)"),
            (INTS, "(not (not p))", "p"),
            (INTS, "(= p true)", "p"),
            (INTS, "(not (<= x 3))", "(>= x 4)"),
            (INTS, "(and (<= x y) (<= y z))", "(= x y)"),
            (INTS, "(and (<= x y) (< y x))", "(= x y)"),
            (INTS, "(and (>= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= x y) (<= y x))", "(= x y)"),
            (REALS, "(>= a 1.0)", "(> a 1.0)"),
        ] {
            let (equal, nl, nr) = same(problem, lhs, rhs);
            assert!(!equal, "{lhs} and {rhs} both normalize to {nl}, {nr}");
        }
    }

    #[test]
    fn certificates_check() {
        for (problem, lhs, rhs) in [
            (INTS, "(* 4 256)", "1024"),
            (INTS, "(+ x y x)", "(+ (* 2 x) y)"),
            (INTS, "(< x y)", "(< (- x y) 0)"),
            (
                INTS,
                "(>= (* -2 x) (* -4 y))",
                "(>= (+ (* -1 x) (* 2 y)) 0)",
            ),
            (INTS, "(= x y)", "(= (- y x) 0)"),
            (INTS, "(and p true q p)", "(and q p)"),
            (INTS, "(and (and p q) (and q p))", "(and p q)"),
            (
                INTS,
                "(distinct x y z)",
                "(and (not (= y x)) (not (= z x)) (not (= z y)))",
            ),
            (INTS, "(f (+ x 0))", "(f x)"),
            (INTS, "(and p (<= x x))", "p"),
            (
                INTS,
                "(or (distinct x (+ y 0)) (= (f (* 1 x)) 0))",
                "(or (not (= x y)) (= (f x) 0))",
            ),
            (INTS, "x", "x"),
            (
                REALS,
                "(* (/ 1 2) (to_real (+ x (* 2 x))))",
                "(* (/ 3 2) (to_real x))",
            ),
            (REALS, "(< (* 2.0 a) b)", "(< (+ a (* (- 0.5) b)) 0.0)"),
            (REALS, "(<= 1 a)", "(<= (- a) (- 1.0))"),
            (INTS, "(and (<= x y) (<= y x))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (<= 0 x) (<= x 0)))"),
            (INTS, "(not (= x y))", "(not (and (<= x y) (<= y x)))"),
            (
                INTS,
                "(ite p (= 1 x) (= 0 x))",
                "(ite p (and (<= 1 x) (<= x 1)) (and (<= 0 x) (<= x 0)))",
            ),
            (
                INTS,
                "(and p q (= 0 (+ x (* (- 2) y))))",
                "(and p q (and (<= 0 (+ x (* (- 2) y))) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (<= a b) (<= b a))", "(= (- a b) 0.0)"),
            (INTS, "(and (>= x y) (<= x y))", "(= x y)"),
            (INTS, "(and (<= x y) (>= x y))", "(= x y)"),
            (INTS, "(and (>= y x) (>= x y))", "(= x y)"),
            (INTS, "(and p (= 0 x))", "(and p (and (>= x 0) (<= x 0)))"),
            (INTS, "(and (and (<= x 2) (>= x 2)) p)", "(and p (<= x 2) (>= x 2))"),
            (INTS, "(and p (<= x 2) q (>= x 2))", "(and (= x 2) q p)"),
            (REALS, "(and (and (<= a b) (>= a b)) (= x 1))", "(and (= x 1) (= (- a b) 0.0))"),
            (
                INTS,
                "(not (= 0 (+ x (* (- 2) y))))",
                "(not (and (>= (+ x (* (- 2) y)) 0) (<= (+ x (* (- 2) y)) 0)))",
            ),
            (REALS, "(and (>= a b) (<= a b))", "(= (- a b) 0.0)"),
            // integer tightening
            (INTS, "(= (+ (* 3 x) (* 3 y)) 1)", "false"),
            (INTS, "(= (* 2 x) 5)", "false"),
            (INTS, "(= 5 (* (- 2) x))", "false"),
            (INTS, "(>= (* 2 x) 3)", "(>= x 2)"),
            (INTS, "(<= (* 2 x) 3)", "(<= x 1)"),
            (INTS, "(>= (* (- 2) x) 3)", "(>= (- x) 2)"),
            (INTS, "(> x 2)", "(>= x 3)"),
            (INTS, "(> (* 2 x) 3)", "(>= x 2)"),
            (INTS, "(< x y)", "(<= (- x y) (- 1))"),
            (INTS, "(< (* 3 x) (- 2))", "(<= x (- 1))"),
            (INTS, "(< (* 3 x) 2)", "(<= x 0)"),
            (INTS, "(and (> x 2) (< x 4))", "(= x 3)"),
            (INTS, "(not (>= (* 2 x) 1))", "(not (>= x 1))"),
            (REALS, "(> a 2.0)", "(> (- a 2.0) 0.0)"),
            // orientation
            (REALS, "(<= a b)", "(>= (- b a) 0.0)"),
            (REALS, "(<= (+ a (* (- 1.0) b)) 0.0)", "(>= (+ (* (- 1.0) a) b) 0.0)"),
            (REALS, "(< (* 2.0 a) b)", "(> (+ (* 0.5 b) (- a)) 0.0)"),
            (INTS, "(<= x y)", "(>= (- y x) 0)"),
            (INTS, "(< x y)", "(>= (- y x) 1)"),
            (INTS, "(<= (* 2 x) 3)", "(>= (- x) (- 1))"),
            (INTS, "(and (<= x 3) (<= 3 x))", "(= x 3)"),
        ] {
            match certified(problem, lhs, rhs) {
                Ok(_) => {}
                Err(e) => panic!("{lhs} = {rhs}: {e}"),
            }
        }
    }
}
