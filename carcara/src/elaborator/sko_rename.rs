use super::*;
use crate::ast::*;
use indexmap::IndexMap;

/// Replaces every `sko_ex_rename` / `sko_forall_rename` subproof with a `bind` subproof followed
/// by the corresponding `sko_ex` / `sko_forall` subproof, combined with a `trans` step.
pub fn elaborate_sko_rename(pool: &mut PrimitivePool, root: &Rc<ProofNode>) -> Rc<ProofNode> {
    let mut cache: HashMap<Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
    walk(pool, root, &mut cache)
}

fn walk(
    pool: &mut PrimitivePool,
    node: &Rc<ProofNode>,
    cache: &mut HashMap<Rc<ProofNode>, Rc<ProofNode>>,
) -> Rc<ProofNode> {
    if let Some(cached) = cache.get(node) {
        return cached.clone();
    }

    let result = match node.as_ref() {
        ProofNode::Assume { .. } => node.clone(),
        ProofNode::Step(s) => {
            let premises: Vec<_> = s.premises.iter().map(|p| walk(pool, p, cache)).collect();
            let discharge: Vec<_> = s.discharge.iter().map(|p| walk(pool, p, cache)).collect();
            let previous_step = s.previous_step.as_ref().map(|p| walk(pool, p, cache));
            Rc::new(ProofNode::Step(StepNode {
                premises,
                discharge,
                previous_step,
                ..s.clone()
            }))
        }
        ProofNode::Subproof(s) => {
            let new_last = walk(pool, &s.last_step, cache);
            if let ProofNode::Step(step) = new_last.as_ref() {
                if step.rule == "sko_ex_rename" || step.rule == "sko_forall_rename" {
                    let outbound: Vec<_> = s
                        .outbound_premises
                        .iter()
                        .map(|p| walk(pool, p, cache))
                        .collect();
                    let result = rewrite_sko_rename(pool, &s.args, step, outbound);
                    cache.insert(node.clone(), result.clone());
                    return result;
                }
            }
            let outbound_premises: Vec<_> = s
                .outbound_premises
                .iter()
                .map(|p| walk(pool, p, cache))
                .collect();
            Rc::new(ProofNode::Subproof(SubproofNode {
                last_step: new_last,
                args: s.args.clone(),
                outbound_premises,
            }))
        }
    };

    cache.insert(node.clone(), result.clone());
    result
}

fn rewrite_sko_rename(
    pool: &mut PrimitivePool,
    args: &[AnchorArg],
    step: &StepNode,
    outbound_premises: Vec<Rc<ProofNode>>,
) -> Rc<ProofNode> {
    let outer_depth = step.depth - 1;
    let inner_depth = step.depth;

    let (left, psi) = match_term!((= l r) = &step.clause[0]).unwrap();
    let (binder, bindings, phi) = left.as_quant().unwrap();
    let is_exists = binder == Binder::Exists;

    // Get the assignments from the anchor (in order) — the i-th one corresponds to the i-th
    // existential/universal binding.
    let assignments: Vec<(String, Rc<Term>)> = args
        .iter()
        .filter_map(|a| a.as_assign().map(|(n, v)| (n.clone(), v.clone())))
        .collect();

    // Build the renamed bindings (anchor variable names, original sorts).
    let renamed_bindings: Vec<SortedVar> = bindings
        .iter()
        .zip(&assignments)
        .map(|((_, sort), (name, _))| (name.clone(), sort.clone()))
        .collect();

    // Build the substitution mapping each original binding variable to a fresh `Var` term using
    // the corresponding anchor variable name.
    let mut subst_map: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();
    for (orig, new) in bindings.iter().zip(&renamed_bindings) {
        let orig_term = pool.add(Term::from(orig.clone()));
        let new_term = pool.add(Term::from(new.clone()));
        subst_map.insert(orig_term, new_term);
    }
    let mut subst = Substitution::new(pool, subst_map).unwrap();
    let phi_renamed = subst.apply(pool, phi);

    let renamed_quant = pool.add(Term::Binder(
        binder,
        BindingList(renamed_bindings.clone()),
        phi_renamed.clone(),
    ));

    let mut ids = IdHelper::new(&step.id);

    // Build the bind subproof.
    let mut bind_args: Vec<AnchorArg> = Vec::new();
    for var in bindings.iter() {
        bind_args.push(AnchorArg::Variable(var.clone()));
    }
    for var in renamed_bindings.iter() {
        // Skip if the variable is already added (e.g., when bindings already match).
        if !bindings.iter().any(|b| b == var) {
            bind_args.push(AnchorArg::Variable(var.clone()));
        }
    }
    for (orig, new) in bindings.iter().zip(&renamed_bindings) {
        let new_var_term = pool.add(Term::from(new.clone()));
        bind_args.push(AnchorArg::Assign(orig.clone(), new_var_term));
    }

    let bind_inner_refl = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: inner_depth,
        clause: vec![build_term!(pool, (= {phi.clone()} {phi_renamed.clone()}))],
        rule: "refl".to_owned(),
        ..Default::default()
    }));

    let bind_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: inner_depth,
        clause: vec![build_term!(pool, (= {left.clone()} {renamed_quant.clone()}))],
        rule: "bind".to_owned(),
        previous_step: Some(bind_inner_refl),
        ..Default::default()
    }));

    let bind_subproof = Rc::new(ProofNode::Subproof(SubproofNode {
        last_step: bind_step,
        args: bind_args,
        outbound_premises: Vec::new(),
    }));

    // Build the sko_ex/sko_forall subproof. Its inner steps are exactly the inner steps of the
    // original `sko_*_rename` subproof (the `previous_step` chain).
    let original_inner = step
        .previous_step
        .as_ref()
        .expect("sko_*_rename step must have a previous step")
        .clone();

    let sko_rule = if is_exists { "sko_ex" } else { "sko_forall" };
    let sko_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: inner_depth,
        clause: vec![build_term!(pool, (= {renamed_quant.clone()} {psi.clone()}))],
        rule: sko_rule.to_owned(),
        previous_step: Some(original_inner),
        ..Default::default()
    }));

    let sko_subproof = Rc::new(ProofNode::Subproof(SubproofNode {
        last_step: sko_step,
        args: args.to_vec(),
        outbound_premises,
    }));

    Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: outer_depth,
        clause: step.clause.clone(),
        rule: "trans".to_owned(),
        premises: vec![bind_subproof, sko_subproof],
        ..Default::default()
    }))
}
