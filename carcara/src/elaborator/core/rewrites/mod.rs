//! Reductions of the rewrite vocabulary: the `*_simplify` rules, `evaluate`, and `rare_rewrite`.
//!
//! Two regimes are implemented, selected by [`RewriteReduction`]:
//!
//! - **`ToRare`** reduces the `*_simplify` rules to chains of single-rewrite lemmas, where each
//!   lemma is a `rare_rewrite` step (or an `evaluate` step, for the constant-folding rewrites),
//!   glued by `trans`. `evaluate` and `rare_rewrite` themselves are kept: they are the
//!   computational vocabulary this regime deliberately retains. The rewrite rules used are those
//!   of the RARE file given to the checker — which must therefore include the rules of the
//!   extended file (`rewrites-simplify.eo`) for the rewrites that `rewrites.eo` does not declare.
//! - **`ToCore`** additionally reduces every lemma — and every `evaluate` and `rare_rewrite`
//!   step of the input — to a derivation over the core fragment, using the recipes of
//!   [`recipes`] and [`ground`]. The term-level `ite` selection axioms (`ite_then_intro`,
//!   `ite_else_intro`) are the one extension of the core this requires.
//!
//! The chains replay the *checker's* rewrite sequence: the `*_simplify` step functions in
//! `checker::rules::simplification` return, along with each rewrite's result, the name of the
//! rewrite applied ([`RewriteLabel`]), and the trace producers in [`trace`] iterate them exactly
//! as `generic_simplify_rule` does (including trying the flipped orientation). The `and_simplify`
//! and `or_simplify` checkers are not rewrite fixpoints, so [`trace`] mirrors their three phases
//! (constant removal, duplicate removal, short-circuit detection) as an explicit rewrite
//! sequence.

pub mod ground;
pub mod recipes;
pub mod trace;

use super::Builder;
use crate::{
    ast::rare_rules::Rules,
    ast::*,
    checker::error::CheckerError,
    checker::RewriteLabel,
    elaborator::error::ElaborationError,
    rare::{get_rules, meta_shapes, rewrite_meta_terms},
};

/// How the rewrite vocabulary is reduced by the `core` pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RewriteReduction {
    /// The rewrite vocabulary is left alone (the plain `core` pass).
    Keep,
    /// `*_simplify` steps become chains of `rare_rewrite`/`evaluate` lemmas.
    ToRare,
    /// `*_simplify`, `evaluate` and `rare_rewrite` steps all reduce to the core (plus the
    /// term-`ite` selection axioms).
    ToCore,
}

/// Is this a rule the rewrite reduction handles?
pub fn is_rewrite_rule(rule: &str) -> bool {
    matches!(
        rule,
        "ite_simplify"
            | "eq_simplify"
            | "not_simplify"
            | "implies_simplify"
            | "equiv_simplify"
            | "bool_simplify"
            | "comp_simplify"
            | "and_simplify"
            | "or_simplify"
            | "prod_simplify"
            | "sum_simplify"
            | "minus_simplify"
            | "unary_minus_simplify"
            | "div_simplify"
            | "evaluate"
            | "rare_rewrite"
    )
}

/// One rewrite of a replayed chain: `before` rewrites to `after` by the rewrite rule `label`. If
/// `arg_pos` is set, the rewrite happened under argument `arg_pos` of the root operator (`inner`
/// holds that argument's own before/after), and the lemma is lifted by `cong`.
pub struct Link {
    pub before: Rc<Term>,
    pub after: Rc<Term>,
    pub label: RewriteLabel,
    pub inner: Option<(Rc<Term>, Rc<Term>)>,
}

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

/// The recipes ultimately emit `refl` steps and excluded-middle instances over subterms of the
/// conclusion, which are checked (at elaborated granularity) by applying the context substitution
/// to their left-hand side. That is only the identity if no anchor in scope *assigns* a free
/// variable of the conclusion (anchors that merely declare a variable leave the substitution
/// alone), so a step that does not satisfy this is skipped (kept unreduced).
fn context_is_safe(
    pool: &mut PrimitivePool,
    context: &ContextStack,
    conclusion: &[Rc<Term>],
) -> bool {
    if context.assigns_nothing() {
        return true;
    }
    conclusion.iter().all(|term| {
        pool.free_vars(term).iter().all(|var| {
            let Some(name) = var.as_var() else {
                return true;
            };
            !context.assigns(name)
        })
    })
}

/// Reduces a `*_simplify` step to a chain of single-rewrite lemmas.
pub fn elaborate_simplify(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
    reduction: RewriteReduction,
    rules: Option<&Rules>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(explanation("conclusion is not a unit clause"));
    };
    if !context_is_safe(pool, context, &step.clause) {
        return Err(explanation("an anchor binds a variable of the conclusion"));
    }
    let (lhs, rhs) = match_term_err!((= l r) = conclusion)?;
    let (lhs, rhs) = (lhs.clone(), rhs.clone());

    // The arithmetic bundles `prod`/`sum`/`minus`/`unary_minus`/`div_simplify` conclude ring
    // identities: they are *renames* of the `poly_simp` computational primitive, in both regimes.
    // The one exception is integer `div`/`mod`, which the ring normalization cannot express.
    if matches!(
        step.rule.as_str(),
        "prod_simplify"
            | "sum_simplify"
            | "minus_simplify"
            | "unary_minus_simplify"
            | "div_simplify"
    ) {
        crate::checker::poly_simp_equal(pool, &lhs, &rhs)?;
        return Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "poly_simp".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            ..step.clone()
        })));
    }

    let (links, flipped) = trace::simplify_trace(pool, &step.rule, &lhs, &rhs)?;
    if links.is_empty() {
        return Err(explanation(
            "no rewrite needed: conclusion relates a term to itself",
        ));
    }

    let mut b = Builder::new(pool, step);
    let mut nodes = Vec::with_capacity(links.len());
    for link in &links {
        nodes.push(lemma(&mut b, link, reduction, rules)?);
    }
    let chained = glue(&mut b, nodes);
    let node = if flipped { b.symm(&chained) } else { chained };
    debug_assert_eq!(node.clause(), step.clause.as_slice());
    Ok(b.relabel(step, node))
}

/// Reduces an `evaluate` step to a core derivation (the `ToCore` regime).
pub fn elaborate_evaluate(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(explanation("conclusion is not a unit clause"));
    };
    if !context_is_safe(pool, context, &step.clause) {
        return Err(explanation("an anchor binds a variable of the conclusion"));
    }
    let (term, value) = match_term_err!((= t v) = conclusion)?;
    let (term, value) = (term.clone(), value.clone());
    let mut b = Builder::new(pool, step);
    let node = ground::evaluation(&mut b, &term, &value)?;
    Ok(b.relabel(step, node))
}

/// Reduces a `rare_rewrite` step to a core derivation (the `ToCore` regime).
pub fn elaborate_rare_rewrite(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(explanation("conclusion is not a unit clause"));
    };
    if !context_is_safe(pool, context, &step.clause) {
        return Err(explanation("an anchor binds a variable of the conclusion"));
    }
    if !step.premises.is_empty() {
        return Err(explanation("premise-carrying RARE rules have no recipe"));
    }
    let Some(name) = step.args.first() else {
        return Err(explanation("`rare_rewrite` step without a rule name"));
    };
    let Term::Const(Constant::String(name)) = &**name else {
        return Err(explanation("`rare_rewrite` step without a rule name"));
    };
    let name = name.clone();
    let (lhs, rhs) = match_term_err!((= l r) = conclusion)?;
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let mut b = Builder::new(pool, step);
    let node = recipes::rewrite_lemma(&mut b, &name, &lhs, &rhs)?;
    Ok(b.relabel(step, node))
}

/// Produces the lemma node concluding `(cl (= before after))` for one link of a chain.
fn lemma(
    b: &mut Builder,
    link: &Link,
    reduction: RewriteReduction,
    rules: Option<&Rules>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let inner = match &link.inner {
        None => match reduction {
            RewriteReduction::ToRare => {
                rare_or_evaluate(b, link.label, &link.before, &link.after, rules)?
            }
            RewriteReduction::ToCore => core_lemma(b, link.label, &link.before, &link.after)?,
            RewriteReduction::Keep => unreachable!(),
        },
        Some((inner_before, inner_after)) => {
            let base = match reduction {
                RewriteReduction::ToRare => {
                    rare_or_evaluate(b, link.label, inner_before, inner_after, rules)?
                }
                RewriteReduction::ToCore => core_lemma(b, link.label, inner_before, inner_after)?,
                RewriteReduction::Keep => unreachable!(),
            };
            // Lift the inner rewrite to the root by congruence. The `cong` checker skips
            // syntactically equal argument pairs, so the single premise suffices.
            let clause = vec![build_term!(
                b.pool,
                (= {link.before.clone()} {link.after.clone()})
            )];
            b.step(clause, "cong", vec![base], Vec::new())
        }
    };
    Ok(inner)
}

fn core_lemma(
    b: &mut Builder,
    label: RewriteLabel,
    before: &Rc<Term>,
    after: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if label == "evaluate" {
        ground::evaluation(b, before, after)
    } else {
        let label = recipes::resolve_label(label, before);
        recipes::rewrite_lemma(b, label, before, after)
    }
}

/// Glues the links of a chain with a single `trans` step (or returns the single link).
fn glue(b: &mut Builder, nodes: Vec<Rc<ProofNode>>) -> Rc<ProofNode> {
    if nodes.len() == 1 {
        return nodes.into_iter().next().unwrap();
    }
    let (first, _) = match_term!((= a b) = nodes.first().unwrap().clause()[0]).unwrap();
    let (_, last) = match_term!((= a b) = nodes.last().unwrap().clause()[0]).unwrap();
    let clause = vec![build_term!(b.pool, (= {first.clone()} {last.clone()}))];
    b.step(clause, "trans", nodes, Vec::new())
}

/// Emits the single-step lemma of the `ToRare` regime: an `evaluate` step for the
/// constant-folding rewrites, and a `rare_rewrite` step otherwise. Both are validated by the
/// corresponding checker computation before being emitted.
fn rare_or_evaluate(
    b: &mut Builder,
    label: RewriteLabel,
    before: &Rc<Term>,
    after: &Rc<Term>,
    rules: Option<&Rules>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let clause = vec![build_term!(b.pool, (= {before.clone()} {after.clone()}))];
    if label == "evaluate" {
        if before.evaluate(b.pool) != *after {
            return Err(explanation("constant fold does not re-evaluate"));
        }
        return Ok(b.step(clause, "evaluate", Vec::new(), Vec::new()));
    }
    if label == "and-flatten" || label == "or-flatten" {
        // The singleton unwrap cannot be a RARE rule: the list semantics of the meta-rewriting
        // normalize the rule's own left-hand-side instance away. Its core recipe (one
        // `and_pos`/`and_neg` or `or_pos`/`or_neg` pair) is emitted in both regimes.
        return recipes::rewrite_lemma(b, label, before, after);
    }

    // A rule the file does not declare, or whose instantiation cannot be reconstructed, falls
    // back to the core recipe: core rules are in this regime's vocabulary too, so the chain
    // stays valid — the lemma is just bigger than one step
    let label = recipes::resolve_label(label, before);
    let Some(rule) = rules.and_then(|r| r.rules.get(label)) else {
        return core_lemma(b, label, before, after);
    };
    if !rule.premises.is_empty() {
        return core_lemma(b, label, before, after);
    }
    let Some(values) = recipes::extract_rare_args(b.pool, label, before, after) else {
        return core_lemma(b, label, before, after);
    };
    if values.len() != rule.arguments.len() {
        return core_lemma(b, label, before, after);
    }

    // Mirror `check_rare`: instantiate the rule's conclusion and normalize the meta-constructs
    // away, then require the result to be exactly the link's equality.
    let mut map = indexmap::IndexMap::new();
    for (arg_name, value) in rule.arguments.iter().zip(&values) {
        let variable = rule.parameters.get(arg_name).unwrap().variable.clone();
        map.insert(variable, value.clone());
    }
    let needs_meta_rewriting =
        rule.has_meta_construct || meta_shapes().any_contains_redex(map.values());
    let mut subst = Substitution::new(b.pool, map).map_err(|e| explanation(format!("{e:?}")))?;
    let got = subst.apply(b.pool, &rule.conclusion);
    let got = if needs_meta_rewriting {
        rewrite_meta_terms(b.pool, got, get_rules())
    } else {
        got
    };
    if got != clause[0] {
        // The meta-level list semantics can make an instantiation differ from the term as the
        // proof writes it (e.g. a singleton `(or x)` collapses to `x`). The core recipe proves
        // the equality exactly as written, and core rules are in this regime's vocabulary too.
        return core_lemma(b, label, before, after);
    }

    let mut args = Vec::with_capacity(values.len() + 1);
    args.push(b.pool.add(Term::Const(Constant::String(label.to_owned()))));
    args.extend(values);
    Ok(b.step(clause, "rare_rewrite", Vec::new(), args))
}

/// Builds the value for a `:list` parameter: a `rare-list` application (possibly empty or
/// singleton).
pub fn rare_list(pool: &mut PrimitivePool, elements: Vec<Rc<Term>>) -> Rc<Term> {
    pool.add(Term::Op(Operator::RareList, elements))
}
