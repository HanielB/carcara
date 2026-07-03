use super::{add_refl_step, add_symm_step, add_trans_step, IdHelper};
use crate::{
    ast::*,
    cc::{CongruenceClosure, EqProof, EqProofRule},
    checker::error::CheckerError,
};
use std::collections::HashMap;

/// Elaborates a `g_eunif` step into a proof using only the `trans`, `cong`, `symm` and `refl`
/// rules, whose leaves are the original premise equalities.
pub fn g_eunif(
    pool: &mut PrimitivePool,
    cc: &mut Option<CongruenceClosure>,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);
    let (t, u) = match_term_err!((= t u) = &step.clause[0])?;

    // As in the checker, the congruence closure's term index is initialized once and shared by
    // all `g_eunif` steps; only the premise equalities are fresh in each invocation
    let cc = cc.get_or_insert_with(|| CongruenceClosure::new(pool.stored_terms()));
    cc.reset();
    for (i, premise) in step.premises.iter().enumerate() {
        assert_eq!(premise.clause().len(), 1);
        let (a, b) = match_term_err!((= a b) = &premise.clause()[0])?;
        cc.add_equality(a, b, i);
    }
    let proof = cc
        .explain(t, u)
        .ok_or_else(|| CheckerError::TermsNotCongruent(t.clone(), u.clone()))?;

    let mut converter = Converter {
        pool,
        premises: &step.premises,
        depth: step.depth,
        ids: IdHelper::new(&step.id),
        cache: HashMap::new(),
    };
    Ok(converter.convert_root(&proof, step))
}

struct Converter<'a> {
    pool: &'a mut PrimitivePool,
    premises: &'a [Rc<ProofNode>],
    depth: usize,
    ids: IdHelper,
    /// Explanations are DAGs, so we cache converted sub-proofs (keyed by their conclusion, which
    /// determines them) to share the corresponding steps
    cache: HashMap<(Rc<Term>, Rc<Term>), Rc<ProofNode>>,
}

impl<'a> Converter<'a> {
    /// Converts the root of the explanation, which must keep the original step's id and clause.
    fn convert_root(&mut self, proof: &EqProof, step: &StepNode) -> Rc<ProofNode> {
        let (rule, premises) = match &proof.rule {
            // If the conclusion is proved directly by a premise, we wrap it in a single-premise
            // `trans` step, so that the elaborated step still exists and keeps the original id
            EqProofRule::Premise(i) => ("trans", vec![self.premises[*i].clone()]),
            EqProofRule::Symm(inner) => ("symm", vec![self.convert(inner)]),
            EqProofRule::Refl => ("refl", Vec::new()),
            EqProofRule::Trans(links) => ("trans", links.iter().map(|l| self.convert(l)).collect()),
            EqProofRule::Cong(args) => ("cong", self.convert_cong_premises(args)),
        };
        Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: rule.to_owned(),
            premises,
            ..StepNode::default()
        }))
    }

    fn convert(&mut self, proof: &EqProof) -> Rc<ProofNode> {
        let (lhs, rhs) = proof.conclusion.clone();
        if let Some(node) = self.cache.get(&(lhs.clone(), rhs.clone())) {
            return node.clone();
        }
        let node = match &proof.rule {
            EqProofRule::Premise(i) => self.premises[*i].clone(),
            EqProofRule::Symm(inner) => {
                let inner = self.convert(inner);
                add_symm_step(self.pool, &inner, self.ids.next_id())
            }
            EqProofRule::Refl => add_refl_step(
                self.pool,
                lhs.clone(),
                rhs.clone(),
                self.ids.next_id(),
                self.depth,
            ),
            EqProofRule::Trans(links) => {
                let links: Vec<_> = links.iter().map(|l| self.convert(l)).collect();
                add_trans_step(self.pool, links, self.ids.next_id())
            }
            EqProofRule::Cong(args) => {
                let premises = self.convert_cong_premises(args);
                let clause = vec![build_term!(self.pool, (= {lhs.clone()} {rhs.clone()}))];
                Rc::new(ProofNode::Step(StepNode {
                    id: self.ids.next_id(),
                    depth: self.depth,
                    clause,
                    rule: "cong".to_owned(),
                    premises,
                    ..StepNode::default()
                }))
            }
        };
        self.cache.insert((lhs, rhs), node.clone());
        node
    }

    /// Converts the argument sub-proofs of a congruence. Syntactically equal argument pairs
    /// (`None`) need no premise, since the `cong` rule skips them.
    fn convert_cong_premises(
        &mut self,
        args: &[Option<crate::cc::EqProofRc>],
    ) -> Vec<Rc<ProofNode>> {
        args.iter().flatten().map(|arg| self.convert(arg)).collect()
    }
}
