use crate::{
    ast::*,
    elaborator::{error::ElaborationError, IdHelper},
};

/// Elaborates an `eq_mp` step into a `resolution` step taking the
/// original premises and a new `equiv_pos2` step.
///
/// That is, a step of the form
/// ```text
/// (step t3 (cl F2) :rule eq_mp :premises (t1 t2))
/// ```
/// where `t1` concludes `F1` and `t2` concludes `(= F1 F2)`, becomes
/// ```text
/// (step t3.t1 (cl (not (= F1 F2)) (not F1) F2) :rule equiv_pos2)
/// (step t3 (cl F2) :rule resolution :premises (t3.t1 t2 t1) :args ((= F1 F2) false F1 false))
/// ```
pub fn eq_mp(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    assert_eq!(step.clause.len(), 1);
    assert_eq!(step.premises.len(), 2);
    let (phi_1_step, equiv_step) = (&step.premises[0], &step.premises[1]);
    assert_eq!(equiv_step.clause().len(), 1);

    let equivalence = equiv_step.clause()[0].clone();
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &equivalence)?;
    let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());

    // If `phi_2` is exactly the negation of `phi_1`, the last two literals introduced by
    // `equiv_pos2` are the same, and the resolution below would derive the empty clause instead of
    // the step's conclusion. That can only happen if the premises are contradictory, in which case
    // we simply leave the step as it is.
    if match_term!((not phi) = &phi_2) == Some(&phi_1) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let equiv_pos2_step = Rc::new(ProofNode::Step(StepNode {
        id: IdHelper::new(&step.id).next_id(),
        depth: step.depth,
        clause: vec![
            build_term!(pool, (not {equivalence.clone()})),
            build_term!(pool, (not {phi_1.clone()})),
            phi_2,
        ],
        rule: "equiv_pos2".to_owned(),
        ..Default::default()
    }));

    let f = pool.bool_false();
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "resolution".to_owned(),
        premises: vec![equiv_pos2_step, equiv_step.clone(), phi_1_step.clone()],
        args: vec![equivalence, f.clone(), phi_1, f],
        ..step.clone()
    })))
}
