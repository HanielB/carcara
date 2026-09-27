//! Abstraction of the subterms a hole's two sides share.
//!
//! A theory-rewrite hole `(= s t)` often rewrites at the top of terms that
//! share a large subterm: `(= (= A false) (not A))` with `A` a formula of a
//! million characters.  The rewrite never looks inside `A`, but egglog has to
//! hold all of it, and that is what fills the e-graph or the per-hole time on
//! the largest proofs.  Before egglog runs, every maximal subterm that occurs
//! on both sides (and is large enough, and binds nothing) is replaced by a
//! fresh constant of its sort; the abstract goal is proved, and its
//! certificate is instantiated back by putting the subterm's text where the
//! constant's name is.  This is sound -- a rewrite proved for a constant
//! holds for any term of the sort -- but not complete: a proof that has to
//! rewrite *inside* the shared subterm to relate it to something outside it
//! (`(= (and (not (not p)) p) (not (not p)))`, whose `p` is inside the shared
//! `(not (not p))`) is lost on the abstract goal, so a hole whose abstract
//! goal fails is retried as it stands.

use crate::ast::{pool::TermPool, Operator, Rc, Substitution, Term};
use rapidhash::RapidHashMap;
use std::collections::{HashMap, HashSet};

/// The abstract goal and, for each fresh constant, its name and the subterm
/// it stands for.
pub struct Abstraction {
    pub goal: Rc<Term>,
    pub bindings: Vec<(String, Rc<Term>)>,
}

/// The prefix of the fresh constants' names; unique to a hole's child, where
/// the goal is declared, and never in a printed proof, since every step is
/// instantiated before it is inserted.
const PREFIX: &str = "@abs_";

/// The node count of a term, or `None` for one with a binder or `let`
/// inside (the substitution and the child's declarations are for closed
/// first-order terms).  A variable or constant counts as one node; that it
/// is never abstracted by itself is the caller's rule, not a size, so the
/// memo keeps sizes only: it used to keep a leaf as `None`, and a second
/// occurrence of any variable or constant then made every term above it
/// non-abstractable.
fn abstractable_size(term: &Rc<Term>, memo: &mut HashMap<Rc<Term>, Option<usize>>) -> Option<usize> {
    if let Some(known) = memo.get(term) {
        return *known;
    }
    let size = match term.as_ref() {
        Term::Op(_, args) => {
            let mut total = 1;
            let mut closed = true;
            for arg in args {
                match abstractable_size(arg, memo) {
                    Some(size) => total += size,
                    None => closed = false,
                }
            }
            closed.then_some(total)
        }
        Term::App(function, args) => {
            let mut total = 1 + abstractable_size(function, memo).unwrap_or(1);
            let mut closed = true;
            for arg in args {
                match abstractable_size(arg, memo) {
                    Some(size) => total += size,
                    None => closed = false,
                }
            }
            closed.then_some(total)
        }
        Term::Var(..) | Term::Const(_) => Some(1),
        _ => None,
    };
    memo.insert(term.clone(), size);
    size
}

/// The maximal subterms of `side` that also occur in `other`, top-down, each
/// of at least `min_nodes` nodes and abstractable.
fn shared_subterms(
    side: &Rc<Term>,
    other: &HashSet<Rc<Term>>,
    min_nodes: usize,
    memo: &mut HashMap<Rc<Term>, Option<usize>>,
    found: &mut Vec<Rc<Term>>,
) {
    if other.contains(side) {
        match side.as_ref() {
            Term::Var(..) | Term::Const(_) => return,
            _ => {
                if abstractable_size(side, memo).is_some_and(|size| size >= min_nodes) {
                    if !found.contains(side) {
                        found.push(side.clone());
                    }
                    return;
                }
            }
        }
    }
    match side.as_ref() {
        Term::Op(_, args) => {
            for arg in args {
                shared_subterms(arg, other, min_nodes, memo, found);
            }
        }
        Term::App(function, args) => {
            shared_subterms(function, other, min_nodes, memo, found);
            for arg in args {
                shared_subterms(arg, other, min_nodes, memo, found);
            }
        }
        _ => {}
    }
}

/// The abstraction of the goal `(= s t)`, or `None` when the sides share no
/// abstractable subterm of `min_nodes` nodes or more (or are equal, or the
/// goal is not an equality).
pub fn abstract_shared(
    pool: &mut dyn TermPool,
    goal: &Rc<Term>,
    min_nodes: usize,
) -> Option<Abstraction> {
    let Term::Op(Operator::Equals, args) = goal.as_ref() else {
        return None;
    };
    let [lhs, rhs] = args.as_slice() else {
        return None;
    };
    if lhs == rhs {
        return None;
    }
    let in_rhs: HashSet<Rc<Term>> = crate::rare::util::collect_subterms(rhs).into_iter().collect();
    let mut memo = HashMap::new();
    let mut shared = Vec::new();
    shared_subterms(lhs, &in_rhs, min_nodes.max(2), &mut memo, &mut shared);
    if shared.is_empty() {
        return None;
    }
    let mut map = RapidHashMap::default();
    let mut bindings = Vec::with_capacity(shared.len());
    for (index, subterm) in shared.into_iter().enumerate() {
        let name = format!("{PREFIX}{index}");
        let sort = pool.sort(&subterm);
        let constant = pool.add(Term::Var(name.clone(), sort));
        map.insert(subterm.clone(), constant);
        bindings.push((name, subterm));
    }
    let mut substitution = Substitution::new(pool, map).ok()?;
    let lhs = substitution.apply(pool, lhs);
    let rhs = substitution.apply(pool, rhs);
    let goal = pool.add(Term::Op(Operator::Equals, vec![lhs, rhs]));
    Some(Abstraction { goal, bindings })
}

/// Whether `c` can be part of an SMT-LIB simple symbol.
fn is_symbol_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || "+-/*=%?!.$_~&^<>@".contains(c)
}

/// `line` with every occurrence of the symbol `name` (as a whole token)
/// replaced by `replacement`.
#[cfg(test)]
fn replace_symbol(line: &str, name: &str, replacement: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(position) = rest.find(name) {
        let before_ok = position == 0
            || !rest[..position].chars().next_back().is_some_and(is_symbol_char);
        let after = &rest[position + name.len()..];
        let after_ok = !after.chars().next().is_some_and(is_symbol_char);
        out.push_str(&rest[..position]);
        if before_ok && after_ok {
            out.push_str(replacement);
        } else {
            out.push_str(name);
        }
        rest = after;
    }
    out.push_str(rest);
    out
}

/// The certificate's steps speaking of the original goal: the first
/// occurrence of each fresh constant becomes `(! t :named <constant>)`, t
/// the subterm it stands for, and every later occurrence, already that
/// symbol, refers to it -- the subterm's text appears once, not at every
/// occurrence.
pub fn instantiate_steps(steps: Vec<String>, bindings: &[(String, Rc<Term>)]) -> Vec<String> {
    if bindings.is_empty() {
        return steps;
    }
    let mut names = crate::ast::printer::SharedNames::new("@abs.");
    let mut pending: Vec<(&str, &Rc<Term>)> =
        bindings.iter().map(|(name, term)| (name.as_str(), term)).collect();
    let mut out = Vec::with_capacity(steps.len());
    for line in steps {
        let mut line = line;
        let mut index = 0;
        while index < pending.len() {
            let (name, term) = pending[index];
            if let Some(position) = first_symbol(&line, name) {
                let definition = format!("(! {} :named {name})", names.print(term));
                line.replace_range(position..position + name.len(), &definition);
                pending.remove(index);
            } else {
                index += 1;
            }
        }
        out.push(line);
    }
    out
}

/// The position of the first occurrence of the symbol `name` in `line`.
fn first_symbol(line: &str, name: &str) -> Option<usize> {
    let mut from = 0;
    while let Some(offset) = line[from..].find(name) {
        let position = from + offset;
        let before_ok = position == 0
            || !line[..position].chars().next_back().is_some_and(is_symbol_char);
        let after_ok = !line[position + name.len()..]
            .chars()
            .next()
            .is_some_and(is_symbol_char);
        if before_ok && after_ok {
            return Some(position);
        }
        from = position + name.len();
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{pool::PrimitivePool, Sort};

    fn bool_var(pool: &mut PrimitivePool, name: &str) -> Rc<Term> {
        let sort = pool.add_sort(Sort::Bool);
        pool.add(Term::Var(name.to_owned(), sort))
    }

    #[test]
    fn abstracts_the_shared_conjunction_and_instantiates_back() {
        let mut pool = PrimitivePool::new();
        let (p, q) = (bool_var(&mut pool, "p"), bool_var(&mut pool, "q"));
        let conj = pool.add(Term::Op(Operator::And, vec![p, q]));
        let falsity = pool.add(Term::Op(Operator::False, vec![]));
        let lhs = pool.add(Term::Op(Operator::Equals, vec![conj.clone(), falsity]));
        let rhs = pool.add(Term::Op(Operator::Not, vec![conj]));
        let goal = pool.add(Term::Op(Operator::Equals, vec![lhs, rhs]));
        let abstraction = abstract_shared(&mut pool, &goal, 2).expect("the conjunction is shared");
        assert_eq!(format!("{:#}", abstraction.goal), "(= (= @abs_0 false) (not @abs_0))");
        assert_eq!(abstraction.bindings.len(), 1);
        let steps = instantiate_steps(
            vec!["(step t1.1 (cl (= (= @abs_0 false) (not @abs_0))) :rule rare_rewrite :args (\"bool-eq-false\" @abs_0))".to_owned()],
            &abstraction.bindings,
        );
        assert_eq!(
            steps[0],
            "(step t1.1 (cl (= (= (! (and p q) :named @abs_0) false) (not @abs_0))) :rule rare_rewrite :args (\"bool-eq-false\" @abs_0))"
        );
    }

    #[test]
    fn small_or_unshared_goals_are_left_alone() {
        let mut pool = PrimitivePool::new();
        let (p, q) = (bool_var(&mut pool, "p"), bool_var(&mut pool, "q"));
        let conj = pool.add(Term::Op(Operator::And, vec![p.clone(), q.clone()]));
        let swapped = pool.add(Term::Op(Operator::And, vec![q, p.clone()]));
        // Only variables are shared: nothing to abstract.
        let goal = pool.add(Term::Op(Operator::Equals, vec![conj.clone(), swapped]));
        assert!(abstract_shared(&mut pool, &goal, 2).is_none());
        // The shared conjunction is below the size threshold.
        let not_conj = pool.add(Term::Op(Operator::Not, vec![conj.clone()]));
        let not_not = pool.add(Term::Op(Operator::Not, vec![not_conj]));
        let goal = pool.add(Term::Op(Operator::Equals, vec![not_not, conj]));
        assert!(abstract_shared(&mut pool, &goal, 10).is_none());
        assert!(abstract_shared(&mut pool, &goal, 3).is_some());
    }

    /// A shared subterm in which a variable occurs twice is abstracted like
    /// any other: `(ite (and (>= x 1) (<= x 2)) 4.0 6.0)` on both sides of
    /// `(= (< t 4.0) (not (>= t 4.0)))` becomes one constant.
    #[test]
    fn a_shared_subterm_with_a_repeated_variable_is_abstracted_whole() {
        let mut pool = PrimitivePool::new();
        let real = pool.add_sort(Sort::Real);
        let x = pool.add(Term::Var("x".to_owned(), real));
        let one = pool.add(Term::new_real(rug::Rational::from(1)));
        let two = pool.add(Term::new_real(rug::Rational::from(2)));
        let four = pool.add(Term::new_real(rug::Rational::from(4)));
        let six = pool.add(Term::new_real(rug::Rational::from(6)));
        let lower = pool.add(Term::Op(Operator::GreaterEq, vec![x.clone(), one]));
        let upper = pool.add(Term::Op(Operator::LessEq, vec![x, two]));
        let condition = pool.add(Term::Op(Operator::And, vec![lower, upper]));
        let ite = pool.add(Term::Op(Operator::Ite, vec![condition, four.clone(), six]));
        let less = pool.add(Term::Op(Operator::LessThan, vec![ite.clone(), four.clone()]));
        let geq = pool.add(Term::Op(Operator::GreaterEq, vec![ite, four]));
        let not_geq = pool.add(Term::Op(Operator::Not, vec![geq]));
        let goal = pool.add(Term::Op(Operator::Equals, vec![less, not_geq]));
        let abstraction = abstract_shared(&mut pool, &goal, 4).expect("the ite is shared");
        assert_eq!(abstraction.bindings.len(), 1, "{:#}", abstraction.goal);
        assert_eq!(format!("{:#}", abstraction.goal), "(= (< @abs_0 4.0) (not (>= @abs_0 4.0)))");
    }

    #[test]
    fn a_name_that_prefixes_another_is_not_confused() {
        let line = "(cl (= @abs_1 @abs_10))";
        assert_eq!(replace_symbol(line, "@abs_1", "x"), "(cl (= x @abs_10))");
        assert_eq!(replace_symbol(line, "@abs_10", "y"), "(cl (= @abs_1 y))");
    }
}
