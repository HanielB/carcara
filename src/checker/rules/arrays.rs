use super::{
    CheckerError, RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_premises,
    get_premise_term,
};
use crate::ast::{Sort, Term, match_term_err};

pub fn idx(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    match_term_err!((= (select (store a i e) i) e) = &conclusion[0])?;
    Ok(())
}

pub fn row(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ip, jp) = match_term_err!((not (= i j)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    let (_, ic, _, jc) =
        match_term_err!((= (select (store a i e) j) (select a j)) = &conclusion[0])?;
    // indices are the same in premise and conclusion
    assert_eq(ip, ic)?;
    assert_eq(jp, jc)?;
    Ok(())
}

pub fn row_contra(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (_, ip, _, jp) =
        match_term_err!((not (= (select (store a i e) j) (select a j))) = premise)?;
    assert_clause_len(conclusion, 1)?;
    let (ic, jc) = match_term_err!((= i j) = &conclusion[0])?;
    // indices are the same in conclusion and premise, but conclusion might be flipped
    if ip != ic {
        assert_eq(ip, jc)?;
        assert_eq(jp, ic)
    } else {
        assert_eq(jp, jc)
    }
}

pub fn ext(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ap, bp) = match_term_err!((not (= a b)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    // both selects must use the same index term
    let (ac, k, bc) = match_term_err!((not (= (select ac k) (select bc k))) = &conclusion[0])?;
    assert_eq(ap, ac)?;
    assert_eq(bp, bc)?;

    // the index must be (choice ((x I)) (or (= a b) (not (= (select a x) (select b x))))),
    // where I is the index sort of a and x is the bound variable
    let (bindings, a1, b1, a2, x, b2) = match_term_err!(
        (choice ... (or (= a1 b1) (not (= (select a2 x) (select b2 x))))) = k
    )?;
    assert_eq(ap, a1)?;
    assert_eq(ap, a2)?;
    assert_eq(bp, b1)?;
    assert_eq(bp, b2)?;

    rassert!(
        bindings.len() == 1,
        CheckerError::Explanation(format!(
            "Expected a single bound variable in the index term, got {}",
            bindings.len()
        ))
    );
    let (name, sort) = &bindings[0];
    let a_sort = pool.sort(ap);
    let Sort::Array(index_sort, _) = a_sort.as_ref() else {
        return Err(CheckerError::Explanation(format!(
            "Could not get Array sort from term {}",
            ap
        )));
    };
    rassert!(
        sort == index_sort,
        CheckerError::Explanation(format!(
            "Expected the bound variable to have the index sort {index_sort}, got {sort}"
        ))
    );
    match x.as_ref() {
        Term::Var(n, s) if n == name && s == sort => Ok(()),
        _ => Err(CheckerError::Explanation(format!(
            "Expected the bound variable {name} in the index term body, got {x}"
        ))),
    }
}
