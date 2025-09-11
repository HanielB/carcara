use super::{
    assert_clause_len, assert_eq, assert_num_premises, get_premise_term, RuleArgs, RuleResult,
};

pub fn idx(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    // match_term!((= (select (store a i1 e) i2) e) = &conclusion[0]).ok_or_else(|| {
    //     Err(CheckerError::Unspecified)
    // })

    // match_term_err!((= (select (store a i e) i) e) = &conclusion[0])

    let (((_, i1, e1), i2), e2) =
        match_term_err!((= (select (store a i1 e1) i2) e2) = &conclusion[0])?;
    // same index in read over write
    assert_eq(i1, i2)?;
    // same element in lhs and rhs of equality
    assert_eq(e1, e2)?;
    Ok(())
}

pub fn row(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (ip, jp) = match_term_err!((not (= ip jp)) = premise)?;

    assert_clause_len(conclusion, 1)?;
    let (((a1, ic, _), jc1), (a2, jc2)) =
        match_term_err!((= (select (store a1 ic e) jc1) (select a2 jc2)) = &conclusion[0])?;
    // indices are the same in premise and conclusion
    assert_eq(ip, ic)?;
    assert_eq(jp, jc1)?;
    // indices are the same in the lhs and rhs of the conclusion
    assert_eq(jc1, jc2)?;
    // arrays are the same in the lhs and rhs of the conclusion
    assert_eq(a1, a2)?;
    Ok(())
}

pub fn row_contra(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (((a1, ip, _), jp1), (a2, jp2)) =
        match_term_err!((not (= (select (store a1 ip e) jp1) (select a2 jp2))) = premise)?;
    assert_clause_len(conclusion, 1)?;
    let (ic, jc) = match_term_err!((= ic jc) = &conclusion[0])?;
    // indices are the same in the lhs and rhs of the premise
    assert_eq(jp1, jp2)?;
    // arrays are the same in the lhs and rhs of the premise
    assert_eq(a1, a2)?;
    // indices are the same in conclusion and premise
    assert_eq(ip, ic)?;
    assert_eq(jp2, jc)?;
    Ok(())
}

pub fn ext(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = get_premise_term(&premises[0])?;
    let (a, b) = match_term_err!((not (= a b)) = premise)?;

    Ok(())
}
