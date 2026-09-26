use crate::rare::language::{EggExpr, EggStatement};

pub fn arith_poly_norm_rel_rules() -> Vec<EggStatement> {
    let egglog_content = include_str!("arith_poly_norm_rel.egglog");
    vec![EggStatement::Raw(egglog_content.to_owned())]
}

pub fn relation_bool_goal_check_terms(
    lhs: EggExpr,
    rhs: EggExpr,
) -> (Vec<EggStatement>, EggExpr, EggExpr) {
    let setup = vec![
        EggStatement::Call(Box::new(EggExpr::Call(
            "arithRelBoolKeyOf-demand".to_owned(),
            vec![lhs.clone()],
        ))),
        EggStatement::Call(Box::new(EggExpr::Call(
            "arithRelBoolKeyOf-demand".to_owned(),
            vec![rhs.clone()],
        ))),
        EggStatement::Saturate {
            ruleset: Some("arith_poly".to_owned()),
        },
    ];

    let lhs_cmp = EggExpr::Call("arithRelBoolKeyOf".to_owned(), vec![lhs]);
    let rhs_cmp = EggExpr::Call("arithRelBoolKeyOf".to_owned(), vec![rhs]);

    (setup, lhs_cmp, rhs_cmp)
}

pub fn relation_bool_goal_guard_term(lhs: EggExpr) -> EggExpr {
    EggExpr::Call("arithRelBoolCanMatch".to_owned(), vec![lhs])
}

/// The setup of the "all relations" fallback: keys for every relation atom
/// of the e-graph (demanded by `arith_rel_all`, computed by `arith_poly`),
/// then the unions of the atoms whose keys agree (`arith_rel_merge`).  The
/// caller follows it with the main schedule, so the rules see the unions.
pub fn relation_all_setup() -> Vec<EggStatement> {
    let run = |ruleset: &str| EggStatement::Run {
        ruleset: Some(ruleset.to_owned()),
        iterations: 1,
    };
    let saturate = |ruleset: &str| EggStatement::Saturate {
        ruleset: Some(ruleset.to_owned()),
    };
    vec![
        // Keys for every relation atom and every arithmetic application.
        run("arith_rel_all"),
        run("arith_term_all"),
        run("arith_poly_guard"),
        saturate("arith_poly"),
        // The mirrors of the negatively led `>=` atoms, then their keys.
        run("arith_rel_flip"),
        run("arith_rel_all"),
        run("arith_poly_guard"),
        saturate("arith_poly"),
        run("arith_rel_merge"),
        run("arith_term_merge"),
    ]
}
