//! Collapsing lemma scopes into the clausal steps they are equivalent to.
//!
//! A solver that proves a lemma by *scoping* assumes the lemma's hypotheses, derives its conclusion
//! under them, and discharges the whole block into one clause. cvc5 does this everywhere: 190 375
//! of the subproofs in the evaluation corpus come from it, against 3 149 from veriT.
//!
//! ```text
//! (anchor :step t7)
//! (assume t7.a0 (= a b))
//! (assume t7.a1 (= b c))
//! (step t7.t0 (cl (= a c)) :rule trans :premises (t7.a0 t7.a1))
//! (step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof :discharge (t7.a0 t7.a1))
//! ```
//!
//! The hypotheses are re-introduced inside the scope only so that a *context-sensitive* rule —
//! `trans` here — can consume them as premises. But they are already spelled out, negated, in the
//! clause the scope discharges, and Alethe has a *clausal* rule that concludes exactly that clause
//! from nothing: `eq_transitive`. Four commands become one:
//!
//! ```text
//! (step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
//! ```
//!
//! So this pass never looks at what a scope contains. It takes the clause the scope discharges and
//! offers it to a battery of premise-free rules; if one accepts, the whole subproof is replaced by
//! a single step with that rule. The checker itself decides, which is what makes the replacement
//! sound whatever the scope was doing internally: the emitted step is accepted by the same function
//! that will check it, with no premises, no context and no discharge, so it proves its clause
//! outright.
//!
//! Two rules take arguments that the clause determines, and are tried with those arguments
//! synthesized: `and_pos` and `or_neg` need the index of the conjunct or disjunct, and `la_generic`
//! needs a Farkas coefficient per literal — which the checker can *infer* from the clause for every
//! literal but the first (this is what the `bounded_farkas` elaboration does).
//!
//! The battery is filtered by `--allowed-rules` for the same reason [`super::hoist`] filters its
//! candidates: a rule the checker was told to accept as a hole must not become the justification of
//! something that had a real derivation.

use crate::ast::*;
use crate::checker::{check_premise_free_rule, la_generic_partial};

/// The premise-free rules a discharged clause is offered to, in the order they are tried.
///
/// The order is by how often each fires on the corpus, so the common cases are decided in one or
/// two calls. Every rule here reads only its conclusion: no premises, no arguments, no context. A
/// rule that needs any of those cannot be validated this way and is handled separately, below.
const CLAUSAL_RULES: &[&str] = &[
    // Congruence-closure lemmas, which are what almost every small cvc5 scope proves
    "eq_transitive",
    "eq_congruent",
    "eq_congruent_pred",
    // CNF-shaped lemmas
    "equiv_pos1",
    "equiv_pos2",
    "equiv_neg1",
    "equiv_neg2",
    "implies_pos",
    "implies_neg1",
    "implies_neg2",
    "and_neg",
    "or_pos",
    "not_not",
    "xor_pos1",
    "xor_pos2",
    "xor_neg1",
    "xor_neg2",
    "ite_pos1",
    "ite_pos2",
    "ite_neg1",
    "ite_neg2",
    // Unit lemmas: a scope with no assumptions, or one whose assumptions are all unused
    "la_disequality",
    "la_totality",
    "la_tautology",
    "la_rw_eq",
    "eq_reflexive",
    "distinct_elim",
    "connective_def",
    "nary_elim",
    "aci_simp",
    "poly_simp",
    "evaluate",
];

/// The replacement a scope's discharged clause was found to have.
pub(super) struct Collapse {
    pub rule: String,
    pub args: Vec<Rc<Term>>,
}

/// Returns the single clausal step that proves what this subproof discharges, if there is one.
///
/// `is_hole` tells whether the checker would treat a rule as a hole, so that a scope with a real
/// derivation is never replaced by one.
pub(super) fn collapse(
    pool: &mut PrimitivePool,
    subproof: &SubproofNode,
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    // An anchor with arguments changes the context, so its last step is a `bind`, `onepoint`,
    // `sko_ex`, `sko_forall` or `let` — a rule about the substitution the anchor carries, not a
    // lemma with dischargeable hypotheses
    if !subproof.args.is_empty() {
        return None;
    }
    let last = subproof.last_step.as_step()?;
    if last.rule != "subproof" {
        return None;
    }
    let clause = &last.clause;

    for rule in CLAUSAL_RULES {
        if is_hole(rule) {
            continue;
        }
        if check_premise_free_rule(pool, rule, clause, &[]).is_ok() {
            return Some(Collapse { rule: (*rule).to_owned(), args: Vec::new() });
        }
    }
    index_rule(pool, clause, is_hole).or_else(|| farkas(pool, clause, is_hole))
}

/// Tries `and_pos` and `or_neg`, whose single argument is the position of the literal in the
/// conjunction or disjunction, and is therefore determined by the clause.
///
/// The index is *searched for* rather than read off, and the rule is then run with it, so a clause
/// that happens to match the shape but not the rule is still rejected by the checker.
fn index_rule(
    pool: &mut PrimitivePool,
    clause: &[Rc<Term>],
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    if clause.len() != 2 {
        return None;
    }
    let (rule, contents) = match (
        match_term!((not (and ...)) = &clause[0]),
        match_term!((or ...) = &clause[0]),
    ) {
        (Some(args), _) => ("and_pos", args),
        (None, Some(args)) => ("or_neg", args),
        _ => return None,
    };
    if is_hole(rule) {
        return None;
    }
    // The literal the rule selects, whose position is the argument
    let selected = match rule {
        "and_pos" => clause[1].clone(),
        _ => clause[1].remove_negation()?.clone(),
    };
    let index = contents.iter().position(|t| *t == selected)?;
    let args = vec![pool.add(Term::new_int(index))];
    check_premise_free_rule(pool, rule, clause, &args)
        .is_ok()
        .then(|| Collapse { rule: rule.to_owned(), args })
}

/// Tries `la_generic`, whose arguments are one Farkas coefficient per literal.
///
/// The coefficients are not searched for: the checker derives all but the first from the clause, by
/// requiring each literal's linear combination to cancel against the accumulated one. Only the
/// leading coefficient has to be chosen, and for a clause the solver derived by scaling and adding
/// its hypotheses it is 1 — the same assumption the `bounded_farkas` elaboration makes.
fn farkas(
    pool: &mut PrimitivePool,
    clause: &[Rc<Term>],
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    if clause.len() < 2 || is_hole("la_generic") {
        return None;
    }
    let one = pool.add(Term::new_real(1));
    let given = [one.clone()];
    let mut trace = Some(Vec::new());
    la_generic_partial(pool, clause, &given, &mut trace).ok()?;
    let inferred = trace.unwrap();
    if inferred.len() + 1 != clause.len() {
        return None;
    }
    let args: Vec<_> = std::iter::once(one)
        .chain(inferred.into_iter().map(|a| pool.add(Term::new_real(a))))
        .collect();
    check_premise_free_rule(pool, "la_generic", clause, &args)
        .is_ok()
        .then(|| Collapse { rule: "la_generic".to_owned(), args })
}
