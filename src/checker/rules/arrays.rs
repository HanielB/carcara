use super::{
    CheckerError, RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_premises,
    get_premise_term,
};
use crate::ast::{Sort, match_term_err};

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
    // (not (= (select a k) (select b k))) where k is
    // (choice ((x i)) (or (= a b) (not (= (select a x) (select b x))))), with i the index
    // sort of a. Each binder is matched with its own binding list, so the two index terms
    // may differ in the name of the bound variable (they are alpha-equivalent); the repeated
    // sort capture forces them to bind at the same sort
    let (ac, i, bc) = match_term_err!(
        (not (= (select a (choice ((x i)) (or (= a b) (not (= (select a x) (select b x))))))
                (select b (choice ((x i)) (or (= a b) (not (= (select a x) (select b x))))))))
        = &conclusion[0]
    )?;
    assert_eq(ap, ac)?;
    assert_eq(bp, bc)?;

    let a_sort = pool.sort(ap);
    let Sort::Array(index_sort, _) = a_sort.as_ref() else {
        return Err(CheckerError::Explanation(format!(
            "Could not get Array sort from term {}",
            ap
        )));
    };
    rassert!(
        **i == **index_sort,
        CheckerError::Explanation(format!(
            "Expected the bound variable to have the index sort {index_sort}, got {i}"
        ))
    );
    Ok(())
}
