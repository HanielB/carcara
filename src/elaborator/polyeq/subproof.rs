use super::*;
use crate::ast::*;

pub fn subproof(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let unchanged = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let previous_step = &step.previous_step.as_ref().unwrap().as_step().unwrap();

    let [previous] = previous_step.clause.as_slice() else {
        return unchanged();
    };
    let last_term = step.clause.last().unwrap();
    if last_term == previous {
        return unchanged();
    }

    let mut ids = IdHelper::new(&step.id);
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        previous.clone(),
        last_term.clone(),
    );
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![
            build_term!(pool, (not {previous.clone()})),
            last_term.clone(),
        ],
        rule: "equiv1".to_owned(),
        premises: vec![polyeq_step],
        ..StepNode::default()
    }));
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![last_term.clone()],
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, step.previous_step.clone().unwrap()],
        args: vec![previous.clone(), pool.bool_false()],
        ..StepNode::default()
    }));
    let mut new_step = step.clone();
    new_step.previous_step = Some(resolution_step);
    Ok(Rc::new(ProofNode::Step(new_step)))
}

/// A `bind` subproof whose conclusion `(= (Q xs φ) (Q ys ψ))` has alpha-equivalent sides — a pure
/// renaming of the bound variables, or the identity substitution veriT uses to enter a binder —
/// is replaced by one `refl` step at the subproof's depth, which holds modulo renaming of bound
/// variables. The equality is checked strictly (not modulo the reordering of equalities), so that
/// the `refl` is closed by syntactic alpha-equivalence alone. Anything else, including the
/// generalized (clausal) form of `bind`, is returned unchanged.
pub fn alpha_bind_to_refl(node: &Rc<ProofNode>) -> Rc<ProofNode> {
    let ProofNode::Subproof(subproof) = node.as_ref() else {
        return node.clone();
    };
    let Some(last) = subproof.last_step.as_step() else {
        return node.clone();
    };
    if last.rule != "bind" || last.clause.len() != 1 {
        return node.clone();
    }
    let Some((left, right)) = match_term!((= l r) = &last.clause[0]) else {
        return node.clone();
    };
    if left.as_binder().is_none() || right.as_binder().is_none() {
        return node.clone();
    }
    if !Polyeq::new().alpha_equiv(true).eq(left, right) {
        return node.clone();
    }
    Rc::new(ProofNode::Step(StepNode {
        id: last.id.clone(),
        depth: node.depth(),
        clause: last.clause.clone(),
        rule: "refl".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}
