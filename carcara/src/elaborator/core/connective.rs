//! The `connective_def` reduction.
//!
//! `connective_def` states five definitional equivalences. Four are propositional and derive from
//! the CNF axioms — the rule's own family — by pure resolution: each direction of the equivalence is
//! a clause the axioms resolve to, and [`Builder::equiv_intro`] glues the two. No anchor is opened.
//!
//! ```text
//! (= (xor a b)     (or (and (not a) b) (and a (not b))))
//! (= (= a b)       (and (=> a b) (=> b a)))
//! (= (ite c x y)   (and (=> c x) (=> (not c) y)))
//! ```
//!
//! The fifth is the quantifier duality, `(= (forall X φ) (not (exists X (not φ))))` and its dual.
//! Nothing else in the core relates `∀` and `∃`, so that instance cannot be derived — it is the
//! dedicated axiom [`qnt_duality`](crate::checker) and the reduction is a rename onto it. Carving
//! the duality out is exactly what lets `connective_def` leave the core.
//!
//! Each direction below is stated as the clause `equiv_intro` wants: `right` is `(cl ¬lhs rhs)`
//! and `left` is `(cl lhs ¬rhs)`.

use super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

pub fn connective_def(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Res {
    let [conclusion] = step.clause.as_slice() else {
        return Err(explanation("conclusion is not a unit clause"));
    };
    let (lhs, rhs) = match_term_err!((= l r) = conclusion)?;
    let (lhs, rhs) = (lhs.clone(), rhs.clone());

    // The quantifier duality is the dedicated axiom: a rename
    if matches!(lhs.as_ref(), Term::Binder(Binder::Forall | Binder::Exists, ..)) {
        return Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "qnt_duality".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            ..step.clone()
        })));
    }

    let mut b = Builder::new(pool, step);
    let (right, left) = if let Some((x, y)) = match_term!((xor x y) = &lhs) {
        let (x, y) = (x.clone(), y.clone());
        xor_def(&mut b, &x, &y, &lhs, &rhs)?
    } else if let Some((x, y)) = match_term!((= x y) = &lhs) {
        let (x, y) = (x.clone(), y.clone());
        iff_def(&mut b, &x, &y, &lhs, &rhs)?
    } else if let Some((c, x, y)) = match_term!((ite c x y) = &lhs) {
        let (c, x, y) = (c.clone(), x.clone(), y.clone());
        ite_def(&mut b, &c, &x, &y, &lhs, &rhs)?
    } else {
        return Err(explanation("not a connective definition"));
    };
    let node = b.equiv_intro(lhs, rhs, right, left)?;
    Ok(b.relabel(step, node))
}

/// `(= (= a b) (and (=> a b) (=> b a)))`.
fn iff_def(
    b: &mut Builder,
    x: &Rc<Term>,
    y: &Rc<Term>,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Result<(Rc<ProofNode>, Rc<ProofNode>), ElaborationError> {
    let (p, q) = match_term_err!((and p q) = rhs)?;
    let (p, q) = (p.clone(), q.clone());
    let (nx, ny) = (b.not(x), b.not(y));
    let (nlhs, nrhs) = (b.not(lhs), b.not(rhs));
    let (np, nq) = (b.not(&p), b.not(&q));

    // ---- right: (cl ¬lhs rhs) ----
    // `(cl P ¬lhs)`: `P = a → b` holds unless `a ∧ ¬b`, which `lhs` forbids
    let pn1 = b.step(vec![p.clone(), x.clone()], "implies_neg1", Vec::new(), Vec::new());
    let pn2 = b.step(vec![p.clone(), ny.clone()], "implies_neg2", Vec::new(), Vec::new());
    let pos2 = b.step(
        vec![nlhs.clone(), nx.clone(), y.clone()],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![pn1, pos2], vec![(x.clone(), true)])?;
    let have_p = b.resolve(vec![r1, pn2], vec![(y.clone(), true)])?;
    // `(cl Q ¬lhs)`, symmetrically
    let qn1 = b.step(vec![q.clone(), y.clone()], "implies_neg1", Vec::new(), Vec::new());
    let qn2 = b.step(vec![q.clone(), nx.clone()], "implies_neg2", Vec::new(), Vec::new());
    let pos1 = b.step(
        vec![nlhs, x.clone(), ny.clone()],
        "equiv_pos1",
        Vec::new(),
        Vec::new(),
    );
    let r2 = b.resolve(vec![qn1, pos1], vec![(y.clone(), true)])?;
    let have_q = b.resolve(vec![r2, qn2], vec![(x.clone(), true)])?;
    let and_neg = b.step(
        vec![rhs.clone(), np, nq],
        "and_neg",
        Vec::new(),
        Vec::new(),
    );
    let r3 = b.resolve(vec![and_neg, have_p], vec![(p.clone(), false)])?;
    let right = b.resolve(vec![r3, have_q], vec![(q.clone(), false)])?;

    // ---- left: (cl lhs ¬rhs) ----
    let (ap0, ap1) = and_pos_pair(b, rhs, &nrhs, &p, &q);
    let (np2, nq2) = (b.not(&p), b.not(&q));
    let p_pos = b.step(
        vec![np2, nx.clone(), y.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let q_pos = b.step(
        vec![nq2, ny.clone(), x.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let l1 = b.resolve(vec![ap0, p_pos], vec![(p.clone(), true)])?;
    let l2 = b.resolve(vec![ap1, q_pos], vec![(q.clone(), true)])?;
    let neg2 = b.step(
        vec![lhs.clone(), x.clone(), y.clone()],
        "equiv_neg2",
        Vec::new(),
        Vec::new(),
    );
    let neg1 = b.step(vec![lhs.clone(), nx, ny], "equiv_neg1", Vec::new(), Vec::new());
    let l3 = b.resolve(vec![neg2, l1], vec![(x.clone(), true)])?;
    let l4 = b.resolve(vec![neg1, l2], vec![(x.clone(), false)])?;
    let left = b.resolve(vec![l3, l4], vec![(y.clone(), true)])?;
    Ok((right, left))
}

/// `(= (xor a b) (or (and (not a) b) (and a (not b))))`.
fn xor_def(
    b: &mut Builder,
    x: &Rc<Term>,
    y: &Rc<Term>,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Result<(Rc<ProofNode>, Rc<ProofNode>), ElaborationError> {
    let (ca, cb) = match_term_err!((or a b) = rhs)?;
    let (ca, cb) = (ca.clone(), cb.clone());
    let (nx, ny) = (b.not(x), b.not(y));
    let (nlhs, nrhs) = (b.not(lhs), b.not(rhs));
    let (nca, ncb) = (b.not(&ca), b.not(&cb));

    // ---- right: (cl ¬lhs rhs) ----
    // `and_neg` on a conjunct whose first argument is `¬a` carries `¬¬a`, which `not_not`
    // (`(cl ¬¬¬p p)`) turns back into `a`
    let (nnx, nny) = (b.not(&nx), b.not(&ny));
    let a_neg = b.step(
        vec![ca.clone(), nnx.clone(), ny.clone()],
        "and_neg",
        Vec::new(),
        Vec::new(),
    );
    let nn_x = not_not(b, x);
    let a_intro = b.resolve(vec![a_neg, nn_x], vec![(nnx, true)])?;
    let b_neg = b.step(
        vec![cb.clone(), nx.clone(), nny.clone()],
        "and_neg",
        Vec::new(),
        Vec::new(),
    );
    let nn_y = not_not(b, y);
    let b_intro = b.resolve(vec![b_neg, nn_y], vec![(nny, true)])?;
    let (i0, i1) = (int(b, 0), int(b, 1));
    let on0 = b.step(vec![rhs.clone(), nca.clone()], "or_neg", Vec::new(), i0);
    let on1 = b.step(vec![rhs.clone(), ncb.clone()], "or_neg", Vec::new(), i1);
    let ra = b.resolve(vec![on0, a_intro], vec![(ca.clone(), false)])?;
    let rb = b.resolve(vec![on1, b_intro], vec![(cb.clone(), false)])?;
    let xp1 = b.step(
        vec![nlhs.clone(), x.clone(), y.clone()],
        "xor_pos1",
        Vec::new(),
        Vec::new(),
    );
    let xp2 = b.step(
        vec![nlhs, nx.clone(), ny.clone()],
        "xor_pos2",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![ra, xp2], vec![(x.clone(), true)])?;
    let r2 = b.resolve(vec![rb, xp1], vec![(x.clone(), false)])?;
    let right = b.resolve(vec![r1, r2], vec![(y.clone(), false)])?;

    // ---- left: (cl lhs ¬rhs) ----
    let or_pos = b.step(
        vec![nrhs, ca.clone(), cb.clone()],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let (j0, j1, k0, k1) = (int(b, 0), int(b, 1), int(b, 0), int(b, 1));
    let ap_a0 = b.step(vec![nca.clone(), nx.clone()], "and_pos", Vec::new(), j0);
    let ap_a1 = b.step(vec![nca.clone(), y.clone()], "and_pos", Vec::new(), j1);
    let ap_b0 = b.step(vec![ncb.clone(), x.clone()], "and_pos", Vec::new(), k0);
    let ap_b1 = b.step(vec![ncb.clone(), ny.clone()], "and_pos", Vec::new(), k1);
    let xn1 = b.step(
        vec![lhs.clone(), x.clone(), ny],
        "xor_neg1",
        Vec::new(),
        Vec::new(),
    );
    let xn2 = b.step(vec![lhs.clone(), nx, y.clone()], "xor_neg2", Vec::new(), Vec::new());
    let la = b.resolve(vec![xn1, ap_a0], vec![(x.clone(), true)])?;
    let la = b.resolve(vec![la, ap_a1], vec![(y.clone(), false)])?;
    let lb = b.resolve(vec![xn2, ap_b0], vec![(x.clone(), false)])?;
    let lb = b.resolve(vec![lb, ap_b1], vec![(y.clone(), true)])?;
    let l1 = b.resolve(vec![or_pos, la], vec![(ca, true)])?;
    let left = b.resolve(vec![l1, lb], vec![(cb, true)])?;
    Ok((right, left))
}

/// `(= (ite c x y) (and (=> c x) (=> (not c) y)))`.
fn ite_def(
    b: &mut Builder,
    c: &Rc<Term>,
    x: &Rc<Term>,
    y: &Rc<Term>,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Result<(Rc<ProofNode>, Rc<ProofNode>), ElaborationError> {
    let (p, q) = match_term_err!((and p q) = rhs)?;
    let (p, q) = (p.clone(), q.clone());
    let (nc, nx, ny) = (b.not(c), b.not(x), b.not(y));
    let (nlhs, nrhs) = (b.not(lhs), b.not(rhs));
    let (np, nq) = (b.not(&p), b.not(&q));

    // ---- right: (cl ¬lhs rhs) ----
    let pn1 = b.step(vec![p.clone(), c.clone()], "implies_neg1", Vec::new(), Vec::new());
    let pn2 = b.step(vec![p.clone(), nx.clone()], "implies_neg2", Vec::new(), Vec::new());
    let ip2 = b.step(
        vec![nlhs.clone(), nc.clone(), x.clone()],
        "ite_pos2",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![pn1, ip2], vec![(c.clone(), true)])?;
    let have_p = b.resolve(vec![r1, pn2], vec![(x.clone(), true)])?;
    let qn1 = b.step(vec![q.clone(), nc.clone()], "implies_neg1", Vec::new(), Vec::new());
    let qn2 = b.step(vec![q.clone(), ny.clone()], "implies_neg2", Vec::new(), Vec::new());
    let ip1 = b.step(
        vec![nlhs, c.clone(), y.clone()],
        "ite_pos1",
        Vec::new(),
        Vec::new(),
    );
    let r2 = b.resolve(vec![qn1, ip1], vec![(c.clone(), false)])?;
    let have_q = b.resolve(vec![r2, qn2], vec![(y.clone(), true)])?;
    let and_neg = b.step(vec![rhs.clone(), np, nq], "and_neg", Vec::new(), Vec::new());
    let r3 = b.resolve(vec![and_neg, have_p], vec![(p.clone(), false)])?;
    let right = b.resolve(vec![r3, have_q], vec![(q.clone(), false)])?;

    // ---- left: (cl lhs ¬rhs) ----
    let (ap0, ap1) = and_pos_pair(b, rhs, &nrhs, &p, &q);
    let (np2, nq2, nnc) = (b.not(&p), b.not(&q), b.not(&nc));
    let p_pos = b.step(
        vec![np2, nc.clone(), x.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    // `Q`'s antecedent is `¬c`, so its `implies_pos` carries `¬¬c`
    let q_pos = b.step(
        vec![nq2, nnc.clone(), y.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let nn_c = not_not(b, c);
    let q_pos = b.resolve(vec![q_pos, nn_c], vec![(nnc, true)])?;
    let l1 = b.resolve(vec![ap0, p_pos], vec![(p.clone(), true)])?;
    let l2 = b.resolve(vec![ap1, q_pos], vec![(q.clone(), true)])?;
    let in2 = b.step(
        vec![lhs.clone(), nc.clone(), nx],
        "ite_neg2",
        Vec::new(),
        Vec::new(),
    );
    let in1 = b.step(vec![lhs.clone(), c.clone(), ny], "ite_neg1", Vec::new(), Vec::new());
    let l3 = b.resolve(vec![in2, l1], vec![(x.clone(), false)])?;
    let l4 = b.resolve(vec![in1, l2], vec![(y.clone(), false)])?;
    let left = b.resolve(vec![l3, l4], vec![(c.clone(), false)])?;
    Ok((right, left))
}

/// The `not_not` axiom `(cl ¬¬¬p p)`, which is how a `¬¬p` literal is discharged.
fn not_not(b: &mut Builder, p: &Rc<Term>) -> Rc<ProofNode> {
    let n1 = b.not(p);
    let n2 = b.not(&n1);
    let n3 = b.not(&n2);
    b.step(vec![n3, p.clone()], "not_not", Vec::new(), Vec::new())
}

/// The two `and_pos` instances of a binary conjunction.
fn and_pos_pair(
    b: &mut Builder,
    _rhs: &Rc<Term>,
    nrhs: &Rc<Term>,
    p: &Rc<Term>,
    q: &Rc<Term>,
) -> (Rc<ProofNode>, Rc<ProofNode>) {
    let (zero, one) = (int(b, 0), int(b, 1));
    let ap0 = b.step(vec![nrhs.clone(), p.clone()], "and_pos", Vec::new(), zero);
    let ap1 = b.step(vec![nrhs.clone(), q.clone()], "and_pos", Vec::new(), one);
    (ap0, ap1)
}

fn int(b: &mut Builder, i: usize) -> Vec<Rc<Term>> {
    vec![b.pool.add(Term::new_int(i))]
}
