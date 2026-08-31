use super::{RuleArgs, RuleResult, assert_clause_len, assert_eq};
use crate::{
    ast::{Operator, Rc, Sort, Term, match_term, match_term_err},
    checker::{
        error::PolynomialError,
        rules::{assert_num_premises, get_premise_term},
    },
};
use indexmap::{IndexMap, map::Entry};
use rug::{Integer, Rational, ops::NegAssign};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Monomial(Vec<Rc<Term>>);

impl Monomial {
    fn mul(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self.0.sort_unstable_by_key(Rc::as_ptr);
        self
    }
}

#[derive(Debug, Clone)]
struct Polynomial(pub(crate) IndexMap<Monomial, Rational>, pub(crate) Rational);

impl Polynomial {
    fn new() -> Self {
        Self(IndexMap::new(), Rational::new())
    }

    /// Builds a polynomial from a term. Takes a term with nested additions, subtractions and
    /// multiplications, and flattens it to polynomial, calculating the coefficient of each
    /// monomial.
    fn from_term(term: &Rc<Term>) -> Self {
        let mut memo = IndexMap::new();
        Self::of_term(term, &mut memo)
    }

    /// Returns the polynomial of `term`, memoizing each subterm's polynomial so the term is
    /// traversed as a DAG. The traversal used to thread the occurrence's coefficient through the
    /// recursion, which made memoization impossible and the flattening exponential on terms with
    /// heavy sharing (a single `poly_simp` step over a shared bit-blasted term took seconds);
    /// instead, each subterm's polynomial is computed once, and an occurrence scales a clone of
    /// the memoized value by its coefficient.
    fn of_term(term: &Rc<Term>, memo: &mut IndexMap<Rc<Term>, Polynomial>) -> Self {
        if let Some(p) = memo.get(term) {
            return p.clone();
        }
        let result = match term.as_ref() {
            Term::Op(Operator::Add | Operator::BvAdd, args) => args
                .iter()
                .map(|a| Self::of_term(a, memo))
                .reduce(Self::add)
                .unwrap_or_else(Self::new),
            Term::Op(Operator::Sub | Operator::BvNeg, args) if args.len() == 1 => {
                let mut p = Self::of_term(&args[0], memo);
                p.neg();
                p
            }
            Term::Op(Operator::Sub | Operator::BvSub, args) => {
                let first = Self::of_term(&args[0], memo);
                args[1..]
                    .iter()
                    .fold(first, |acc, a| acc.sub(Self::of_term(a, memo)))
            }
            Term::Op(Operator::Mult | Operator::BvMul, args) => args
                .iter()
                .map(|a| Self::of_term(a, memo))
                .reduce(Self::mul)
                .unwrap(),
            Term::Op(Operator::RealDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| !r.is_zero()) =>
            {
                let r = args[1].as_fraction().unwrap();
                let mut p = Self::of_term(&args[0], memo);
                p.scale(&(Rational::from(1) / r));
                p
            }
            Term::Op(Operator::ToReal, args) => Self::of_term(&args[0], memo),
            // We check for division by zero separately because `.as_fraction` panics if the
            // denominator is zero. In this case, we consider the term an atom.
            Term::Op(Operator::RealDiv | Operator::IntDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| r.is_zero()) =>
            {
                Self::atom(term.clone())
            }
            _ => {
                if let Some(r) = term.as_fraction() {
                    Self(IndexMap::new(), r)
                } else if let Some((value, _)) = term.as_bitvector() {
                    // The width is irrelevant for the normalization, overflow will be dealt with
                    // later, using the `modulo` method
                    Self(IndexMap::new(), Rational::from(value))
                } else {
                    Self::atom(term.clone())
                }
            }
        };
        memo.insert(term.clone(), result.clone());
        result
    }

    /// The polynomial consisting of just `term` as a monomial, with coefficient one.
    fn atom(term: Rc<Term>) -> Self {
        let mut p = Self::new();
        p.insert(Monomial(vec![term]), Rational::from(1));
        p
    }

    /// Multiplies every coefficient (and the constant) by `c`.
    fn scale(&mut self, c: &Rational) {
        if c.is_zero() {
            *self = Self::new();
            return;
        }
        for coeff in self.0.values_mut() {
            *coeff *= c;
        }
        self.1 *= c;
    }

    fn mul(self, other: Self) -> Self {
        let mut result = Self::new();
        for (x_1, c_1) in self.0 {
            for (x_2, c_2) in &other.0 {
                result.insert(x_1.clone().mul(x_2.clone()), c_1.clone() * c_2);
            }
            result.insert(x_1, c_1 * &other.1);
        }
        for (x_2, c_2) in other.0 {
            result.insert(x_2, c_2 * &self.1);
        }
        result.1 += self.1 * other.1;
        result
    }

    fn insert(&mut self, key: Monomial, value: Rational) {
        if value == 0 {
            return;
        }
        match self.0.entry(key) {
            Entry::Occupied(mut e) => {
                *e.get_mut() += value;
                if *e.get() == 0 {
                    e.swap_remove();
                }
            }
            Entry::Vacant(e) => {
                e.insert(value);
            }
        }
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty() && self.1.is_zero()
    }

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff);
        }
        self.1 += other.1;
        self
    }

    fn neg(&mut self) {
        for coeff in self.0.values_mut() {
            coeff.neg_assign();
        }
        self.1.neg_assign();
    }

    fn sub(self, mut other: Self) -> Self {
        other.neg();
        self.add(other)
    }

    fn modulo(mut self, n: &Integer) -> Option<Self> {
        for (_, coeff) in &mut self.0 {
            if !coeff.is_integer() {
                return None;
            }
            *coeff = coeff.numer().clone().modulo(n).into();
        }
        // A coefficient may have been reduced to zero (e.g. `1 + (2^w - 1)`), and zero-coefficient
        // entries would make the final `is_zero` check fail
        self.0.retain(|_, coeff| !coeff.is_zero());
        if self.1.is_integer() {
            self.1 = self.1.numer().clone().modulo(n).into();
            Some(self)
        } else {
            None
        }
    }
}

/// The body of the `poly_simp` check, exposed so that elaboration passes can verify that a
/// candidate `poly_simp` step would be accepted before emitting it.
pub fn poly_simp_equal(
    pool: &mut dyn crate::ast::TermPool,
    t: &Rc<Term>,
    s: &Rc<Term>,
) -> RuleResult {
    let (mut t_norm, mut s_norm) = (Polynomial::from_term(t), Polynomial::from_term(s));
    if let Sort::BitVec(width) = pool.sort(t).as_ref() {
        let max = Integer::from(1) << width;
        t_norm = t_norm.modulo(&max).unwrap();
        s_norm = s_norm.modulo(&max).unwrap();
    }
    if !t_norm.sub(s_norm).is_zero() {
        Err(PolynomialError::PolynomialsNotEqual(t.clone(), s.clone()).into())
    } else {
        Ok(())
    }
}

pub fn poly_simp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (t, s) = match_term_err!((= t s) = &conclusion[0])?;
    let (mut t_norm, mut s_norm) = (Polynomial::from_term(t), Polynomial::from_term(s));

    // If the sort is a bitvector sort, we must take the modulo
    if let Sort::BitVec(width) = pool.sort(t).as_ref() {
        let max = Integer::from(1) << width;
        t_norm = t_norm.modulo(&max).unwrap();
        s_norm = s_norm.modulo(&max).unwrap();
    }

    if !t_norm.sub(s_norm).is_zero() {
        Err(PolynomialError::PolynomialsNotEqual(t.clone(), s.clone()).into())
    } else {
        Ok(())
    }
}

pub fn poly_simp_rel(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    use Operator::*;

    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    let prem = get_premise_term(&premises[0])?;

    // Bitvector case: (= (bvmul c1 (bvsub x1 x2)) (bvmul c2 (bvsub y1 y2)))
    let bitvector_case = match_term!(
        (= (bvmul c1 (bvsub x1 x2)) (bvmul c2 (bvsub y1 y2)))
        = get_premise_term(&premises[0])?);
    if let Some((c1, x1, x2, c2, y1, y2)) = bitvector_case {
        let sort = pool.sort(c1);
        let Sort::BitVec(_) = sort.as_ref() else {
            unreachable!()
        };
        for c in [c1, c2] {
            let (c, _) = c.as_bitvector_err()?;
            rassert!(c.is_odd(), PolynomialError::CoeffEven(c));
        }

        let (l1, l2, r1, r2) = match_term_err!((= (= x1 x2) (= y1 y2)) = &conclusion[0])?;

        assert_eq(l1, x1)?;
        assert_eq(l2, x2)?;
        assert_eq(r1, y1)?;
        assert_eq(r2, y2)?;
        return Ok(());
    }

    let (c1, xs, c2, ys) = match_term_err!((= (* c1 xs) (* c2 ys)) = prem)?;
    let (x1, x2) =
        match_term_err!((to_real (- x1 x2)) = xs).or_else(|_| match_term_err!((- x1 x2) = xs))?;
    let (y1, y2) =
        match_term_err!((to_real (- y1 y2)) = ys).or_else(|_| match_term_err!((- y1 y2) = ys))?;

    let (c1, c2) = (c1.as_fraction_err()?, c2.as_fraction_err()?);
    for c in [&c1, &c2] {
        rassert!(!c.is_zero(), PolynomialError::CoeffIsZero(c.clone()));
    }

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    match (left.as_op_err()?, right.as_op_err()?) {
        (
            (op @ (LessThan | LessEq | Equals | GreaterEq | GreaterThan), [l1, l2]),
            (op2, [r1, r2]),
        ) if op2 == op => {
            rassert!(
                op == Equals || c1.is_positive() == c2.is_positive(),
                PolynomialError::CoeffDifferentSignums(c1.clone(), c2.clone()),
            );

            assert_eq(l1, x1)?;
            assert_eq(l2, x2)?;
            assert_eq(r1, y1)?;
            assert_eq(r2, y2)?;
            Ok(())
        }
        ((op1, _), (op2, _)) => Err(PolynomialError::InvalidOperators(op1, op2).into()),
    }
}
