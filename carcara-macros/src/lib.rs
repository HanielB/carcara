extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Delimiter, Ident, Spacing, TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote};
use std::{collections::HashMap, process::Command};
use syn::{
    DataStruct, DeriveInput, Expr, Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
};

// Represents the full macro input: '<pattern> = <expr>'
struct Input {
    pattern: TokenTree,
    expr: Expr,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pattern: TokenTree = input.parse()?;
        input.parse::<Token![=]>()?;
        let expr: Expr = input.parse()?;
        Ok(Input { pattern, expr })
    }
}

// A counter for generating unique idents, and the names bound so far,
// used to detect repeated names.
struct ParseCtx {
    ctr: usize,
    // Maps a name written by the user to the generated ident bound by its
    // first occurrence in the pattern.
    bound: HashMap<String, Ident>,
    // Maps the name of a variable bound by an enclosing explicit binding list
    // (e.g. `x` in `(choice ((x i)) body)`) to the generated ident holding its
    // `(String, Rc<Sort>)` entry. An occurrence of the name in the body is then
    // a check that the term is that bound variable, not a capture.
    bound_vars: HashMap<String, Ident>,
}

// What a repeated name is checked against.
#[derive(Debug, Clone)]
enum SameAs {
    // The term captured by the first occurrence of the name.
    Term(Ident),
    // The variable of a binding-list entry: the term must be `Term::Var` with
    // that entry's name and sort.
    Bound(Ident),
}

// The binding list of a binder pattern.
#[derive(Debug, Clone)]
enum BindingsPat {
    // `...`: the whole BindingList is captured under the given ident.
    Any(Ident),
    // `((x i) ...)`: one entry per pattern, matched positionally. Each entry
    // binds its name for the body and matches its sort with a pattern.
    Explicit(Vec<BindingPat>),
}

#[derive(Debug, Clone)]
struct BindingPat {
    // Generated ident bound to the `&(String, Rc<Sort>)` entry.
    entry_id: Ident,
    // Pattern for the entry's sort (a capture, `_`, or a repeated name).
    sort: Pat,
}

// Internal representation of the s-expression pattern.
//
// Every free variable and binder binding list gets a unique generated Ident so
// that repeated names in the pattern (e.g. (= (= t u) (= u t))) do NOT
// shadow each other in the generated code. The user's names in the LHS of the
// outer 'let' destructuring are unaffected.
#[derive(Debug, Clone)]
enum Pat {
    True,
    False,
    EmptyString,
    // Integer literal
    Literal(u64),
    // Real/rational literal
    LiteralReal(f64),
    // Each occurrence gets a unique generated ident to avoid shadowing.
    FreeVar {
        id: Ident,
        // `Some(first)` when this name already appeared earlier in the pattern.
        // Such an occurrence doesn't capture anything: instead, the generated
        // code checks that this term is equal to the one bound by `first`, and
        // the match fails if it isn't.
        same_as: Option<SameAs>,
    },
    // Carries a generated name that will hold the captured &[Rc<Term>] slice.
    Variadic(Ident),
    Op {
        op: String,
        args: Vec<Pat>,
    },
    ParamOp {
        op: String,
        op_args: Vec<Pat>,
        args: Vec<Pat>,
    },
    // Represents (forall ... body), (exists ... body), (choice ... body).
    // 'bindings_id' is a unique generated ident for this binder's BindingList,
    // so multiple binders in one pattern don't shadow each other.
    Binder {
        binder: String,
        bindings: BindingsPat,
        inner: Box<Pat>,
    },
}

impl Pat {
    /// Collects all free variables in depth-first, left-to-right order.
    /// This order determines the flat tuple returned by the macro.
    ///
    /// Repeated occurrences of a name are not included: they are turned into
    /// equality checks instead of captures, so a name always contributes
    /// exactly one element to the tuple, no matter how many times it appears.
    fn free_vars(&self) -> Vec<Ident> {
        match self {
            Pat::FreeVar { same_as: Some(_), .. } => Vec::new(),
            Pat::FreeVar { id, same_as: None } => vec![id.clone()],
            // Variadic contributes the slice ident as one element of the tuple.
            Pat::Variadic(id) => vec![id.clone()],
            Pat::Op { args, .. } => args.iter().flat_map(|p| p.free_vars()).collect(),
            Pat::ParamOp { op_args, args, .. } => op_args
                .iter()
                .chain(args.iter())
                .flat_map(|p| p.free_vars())
                .collect(),
            // A binder yields its bindings capture first (the whole list for
            // `...`, the sort captures in order for an explicit list), then the
            // inner vars. Bound variable names never capture.
            Pat::Binder { bindings, inner, .. } => {
                let mut vars = match bindings {
                    BindingsPat::Any(id) => vec![id.clone()],
                    BindingsPat::Explicit(entries) => {
                        entries.iter().flat_map(|e| e.sort.free_vars()).collect()
                    }
                };
                vars.extend(inner.free_vars());
                vars
            }
            _ => vec![],
        }
    }
}

// Reads an operator from a token slice.
// Multi-character operators like <=, >=, => are two adjacent Punct tokens.
fn read_op(tokens: &[TokenTree]) -> (String, usize) {
    match &tokens[0] {
        TokenTree::Ident(id) => (id.to_string(), 1),
        TokenTree::Punct(p) => {
            if p.spacing() == Spacing::Joint
                && let Some(TokenTree::Punct(p2)) = tokens.get(1)
            {
                return (format!("{}{}", p.as_char(), p2.as_char()), 2);
            }
            (p.as_char().to_string(), 1)
        }
        other => panic!("expected operator, found {:?}", other),
    }
}

// Returns true if tokens[i..i+3] are three consecutive '.' Punct tokens.
fn is_three_dots(tokens: &[TokenTree], i: usize) -> bool {
    tokens[i..].len() >= 3
        && (0..3).all(|j| matches!(&tokens[i + j], TokenTree::Punct(p) if p.as_char() == '.'))
}

// Parses a slice of tokens as a list of pattern arguments, handling '...'
// variadics. Shared between regular Op and ParamOp argument parsing.
fn parse_args(tokens: &[TokenTree], ctx: &mut ParseCtx) -> Vec<Pat> {
    let mut args = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        if is_three_dots(tokens, i) {
            // Generate a unique ident for this variadic capture.
            ctx.ctr += 1;
            args.push(Pat::Variadic(format_ident!("__mt_variadic_{}", ctx.ctr)));
            i += 3;
            continue;
        }
        args.push(parse_pat(tokens[i].clone(), ctx));
        i += 1;
    }
    args
}

// Recursively parses a TokenTree into a Pat.
// 'ctx' provides the counter used to generate unique idents for all captures,
// and tracks which names have already been bound.
fn parse_pat(tt: TokenTree, ctx: &mut ParseCtx) -> Pat {
    match tt {
        TokenTree::Ident(id) => match id.to_string().as_str() {
            "true" => Pat::True,
            "false" => Pat::False,
            // Every free variable gets a unique generated ident. This prevents
            // repeated names from shadowing each other in the generated let bindings.
            name => {
                ctx.ctr += 1;
                let new_id = format_ident!("__mt_var_{}", ctx.ctr);

                // '_' is a wildcard: each occurrence matches anything, and it
                // never has to be equal to any other occurrence.
                let same_as = if name == "_" {
                    None
                } else if let Some(entry) = ctx.bound_vars.get(name) {
                    // The name is bound by an enclosing explicit binding list:
                    // this occurrence must be that bound variable.
                    Some(SameAs::Bound(entry.clone()))
                } else {
                    // If this name was already bound, this occurrence becomes an
                    // equality check against the term captured by the first one.
                    match ctx.bound.get(name) {
                        Some(first) => Some(SameAs::Term(first.clone())),
                        None => {
                            ctx.bound.insert(name.to_owned(), new_id.clone());
                            None
                        }
                    }
                };
                Pat::FreeVar { id: new_id, same_as }
            }
        },

        TokenTree::Literal(lit) => {
            let s = lit.to_string();
            if s == "\"\"" {
                Pat::EmptyString
            } else if let Ok(n) = s.parse::<u64>() {
                Pat::Literal(n)
            } else if let Ok(f) = s.parse::<f64>() {
                Pat::LiteralReal(f)
            } else {
                panic!("unsupported literal in match_term_flat!: {s}")
            }
        }

        TokenTree::Group(g) if g.delimiter() == Delimiter::Parenthesis => {
            let tokens: Vec<_> = g.stream().into_iter().collect();
            assert!(!tokens.is_empty(), "empty group in pattern");

            // Detect (forall ... body), (exists ... body), (choice ... body), or
            // the same binders with an explicit binding list:
            // (choice ((x i) (y j)) body).
            //
            // With '...', the shape is exactly 5 tokens: ident + '.' + '.' + '.'
            // + body, and the whole BindingList is captured. With an explicit
            // list, it is 3 tokens: ident + list group + body; each entry is a
            // group (name sortpat), whose name is bound for the body (occurrences
            // there must be that bound variable) and whose sort is matched by
            // sortpat (a capture, '_' or a repeated name).
            if let TokenTree::Ident(id) = &tokens[0] {
                let name = id.to_string();
                if matches!(name.as_str(), "forall" | "exists" | "choice" | "lambda") {
                    if tokens.len() == 3 {
                        let TokenTree::Group(list) = &tokens[1] else {
                            panic!("binder pattern must be ({name} ... <body>) or ({name} ((x s) ...) <body>)")
                        };
                        assert!(
                            list.delimiter() == Delimiter::Parenthesis,
                            "binder pattern: binding list must be parenthesized"
                        );
                        let mut entries = Vec::new();
                        let mut shadowed = Vec::new();
                        for entry_tt in list.stream() {
                            let TokenTree::Group(entry) = entry_tt else {
                                panic!("binder pattern: each binding must be (name sortpat)")
                            };
                            let entry_tokens: Vec<_> = entry.stream().into_iter().collect();
                            assert!(
                                entry_tokens.len() == 2,
                                "binder pattern: each binding must be (name sortpat)"
                            );
                            let TokenTree::Ident(var) = &entry_tokens[0] else {
                                panic!("binder pattern: binding name must be an identifier")
                            };
                            ctx.ctr += 1;
                            let entry_id = format_ident!("__mt_binding_{}", ctx.ctr);
                            let sort = parse_pat(entry_tokens[1].clone(), ctx);
                            let var = var.to_string();
                            if var != "_" {
                                shadowed.push((var.clone(), ctx.bound_vars.insert(var, entry_id.clone())));
                            }
                            entries.push(BindingPat { entry_id, sort });
                        }
                        let inner = parse_pat(tokens[2].clone(), ctx);
                        // the bound names are only in scope in the body
                        for (var, prev) in shadowed.into_iter().rev() {
                            match prev {
                                Some(prev) => {
                                    ctx.bound_vars.insert(var, prev);
                                }
                                None => {
                                    ctx.bound_vars.remove(&var);
                                }
                            }
                        }
                        return Pat::Binder {
                            binder: name,
                            bindings: BindingsPat::Explicit(entries),
                            inner: Box::new(inner),
                        };
                    }
                    assert!(
                        tokens.len() == 5,
                        "binder pattern must be ({name} ... <body>) or ({name} ((x s) ...) <body>), got {} tokens",
                        tokens.len()
                    );
                    assert!(
                        is_three_dots(&tokens, 1),
                        "binder pattern must be ({name} ... <body>), expected '...' after binder name"
                    );
                    let inner_tt = tokens[4].clone();
                    // Generate a unique ident for this binder's bindings so that
                    // multiple binders in one pattern don't shadow each other.
                    ctx.ctr += 1;
                    let bindings_id = format_ident!("__mt_bindings_{}", ctx.ctr);
                    return Pat::Binder {
                        binder: name,
                        bindings: BindingsPat::Any(bindings_id),
                        inner: Box::new(parse_pat(inner_tt, ctx)),
                    };
                }
            }

            // Detect ((_ op op_args...) args...) - ParamOp pattern.
            // The '_' here is an Ident token, not a Punct.
            if let TokenTree::Group(inner) = &tokens[0]
                && inner.delimiter() == Delimiter::Parenthesis
            {
                let inner_tokens: Vec<_> = inner.stream().into_iter().collect();
                if matches!(&inner_tokens[0], TokenTree::Ident(id) if *id == "_") {
                    let (op, op_len) = read_op(&inner_tokens[1..]);
                    let op_args = parse_args(&inner_tokens[1 + op_len..], ctx);
                    let args = parse_args(&tokens[1..], ctx);
                    return Pat::ParamOp { op, op_args, args };
                }
            }

            // Regular Op pattern - read operator, then parse args.
            let (op, op_len) = read_op(&tokens);
            let args = parse_args(&tokens[op_len..], ctx);
            Pat::Op { op, args }
        }

        other => panic!("unexpected token in pattern: {:?}", other),
    }
}

fn param_op_to_variant(op: &str) -> TokenStream2 {
    match op {
        "int_of" => quote! { crate::ast::ParamOperator::BvIntOf },
        "bit_of" => quote! { crate::ast::ParamOperator::BvBitOf },
        "int_to_bv" => quote! { crate::ast::ParamOperator::IntToBv },
        "extract" => quote! { crate::ast::ParamOperator::BvExtract },
        "zero_extend" => quote! { crate::ast::ParamOperator::ZeroExtend },
        "sign_extend" => quote! { crate::ast::ParamOperator::SignExtend },
        "rotate_left" => quote! { crate::ast::ParamOperator::RotateLeft },
        "rotate_right" => quote! { crate::ast::ParamOperator::RotateRight },
        "repeat" => quote! { crate::ast::ParamOperator::Repeat },
        other => panic!("unknown param operator in match_term_flat!: {other:?}"),
    }
}

fn op_to_variant(op: &str) -> TokenStream2 {
    match op {
        // Boolean / logical
        "not" => quote! { crate::ast::Operator::Not },
        "=>" => quote! { crate::ast::Operator::Implies },
        "and" => quote! { crate::ast::Operator::And },
        "or" => quote! { crate::ast::Operator::Or },
        "xor" => quote! { crate::ast::Operator::Xor },
        "=" => quote! { crate::ast::Operator::Equals },
        "distinct" => quote! { crate::ast::Operator::Distinct },
        "ite" => quote! { crate::ast::Operator::Ite },

        // Arithmetic
        "+" => quote! { crate::ast::Operator::Add },
        "-" => quote! { crate::ast::Operator::Sub },
        "*" => quote! { crate::ast::Operator::Mult },
        "div" => quote! { crate::ast::Operator::IntDiv },
        "/" => quote! { crate::ast::Operator::RealDiv },
        "mod" => quote! { crate::ast::Operator::Mod },
        "abs" => quote! { crate::ast::Operator::Abs },
        "<" => quote! { crate::ast::Operator::LessThan },
        ">" => quote! { crate::ast::Operator::GreaterThan },
        "<=" => quote! { crate::ast::Operator::LessEq },
        ">=" => quote! { crate::ast::Operator::GreaterEq },
        "to_real" => quote! { crate::ast::Operator::ToReal },
        "to_int" => quote! { crate::ast::Operator::ToInt },

        // TODO: we should support dots in operators for these cases
        "int_pow2" => quote! { crate::ast::Operator::Pow2 },
        "int_log2" => quote! { crate::ast::Operator::Log2 },

        // Clause / delete
        "cl" => quote! { crate::ast::Operator::Cl },
        "delete" => quote! { crate::ast::Operator::Delete },

        // Bitvector — basic
        "bbterm" => quote! { crate::ast::Operator::BvBbTerm },
        "pbbterm" => quote! { crate::ast::Operator::BvPBbTerm },
        "bvnot" => quote! { crate::ast::Operator::BvNot },
        "bvneg" => quote! { crate::ast::Operator::BvNeg },
        "bvand" => quote! { crate::ast::Operator::BvAnd },
        "bvor" => quote! { crate::ast::Operator::BvOr },
        "bvxor" => quote! { crate::ast::Operator::BvXor },
        "bvxnor" => quote! { crate::ast::Operator::BvXNor },
        "bvcomp" => quote! { crate::ast::Operator::BvComp },
        "bvadd" => quote! { crate::ast::Operator::BvAdd },
        "bvsub" => quote! { crate::ast::Operator::BvSub },
        "bvmul" => quote! { crate::ast::Operator::BvMul },
        "bvudiv" => quote! { crate::ast::Operator::BvUDiv },
        "bvurem" => quote! { crate::ast::Operator::BvURem },
        "bvshl" => quote! { crate::ast::Operator::BvShl },
        "bvlshr" => quote! { crate::ast::Operator::BvLShr },
        "bvashr" => quote! { crate::ast::Operator::BvAShr },
        "concat" => quote! { crate::ast::Operator::BvConcat },

        // Bitvector — comparisons
        "bvuge" => quote! { crate::ast::Operator::BvUGe },
        "bvugt" => quote! { crate::ast::Operator::BvUGt },
        "bvule" => quote! { crate::ast::Operator::BvULe },
        "bvult" => quote! { crate::ast::Operator::BvULt },
        "bvsge" => quote! { crate::ast::Operator::BvSGe },
        "bvsgt" => quote! { crate::ast::Operator::BvSGt },
        "bvsle" => quote! { crate::ast::Operator::BvSLe },
        "bvslt" => quote! { crate::ast::Operator::BvSLt },

        // Bitvector — int conversions
        "ubv_to_int" => quote! { crate::ast::Operator::UBvToInt },
        "sbv_to_int" => quote! { crate::ast::Operator::SBvToInt },

        // Strings
        "strconcat" => quote! { crate::ast::Operator::StrConcat },
        "strsubstr" => quote! { crate::ast::Operator::Substring },
        "strlen" => quote! { crate::ast::Operator::StrLen },
        "strinre" => quote! { crate::ast::Operator::StrInRe },
        "reinter" => quote! { crate::ast::Operator::ReIntersection },

        // Arrays
        "select" => quote! { crate::ast::Operator::Select },
        "store" => quote! { crate::ast::Operator::Store },

        other => panic!("unknown operator in match_term!: {other:?}"),
    }
}

// Shared helper: generates the body that binds a variadic slice ident and
// continues with 'inner'. Used by both Op and ParamOp sole-variadic cases.
fn gen_sole_variadic_body(var_id: &Ident, args_vec: &Ident, inner: TokenStream2) -> TokenStream2 {
    quote! {
        let #var_id = #args_vec.as_slice();
        #inner
    }
}

// Builds nested 'if let' matching code using continuation-passing style.
// 'inner' is the innermost code (the return value), and each recursive call
// wraps it in another layer of matching.
fn gen_match(pat: &Pat, var: &TokenStream2, inner: TokenStream2, ctr: &mut usize) -> TokenStream2 {
    match pat {
        Pat::True => quote! {
            if (#var).is_bool_true() { #inner } else { None }
        },
        Pat::False => quote! {
            if (#var).is_bool_false() { #inner } else { None }
        },
        Pat::EmptyString => quote! {
            if (#var).is_empty_string() { #inner } else { None }
        },
        Pat::Literal(n) => quote! {
            if (#var).as_number().is_some_and(|i| i == #n) { #inner } else { None }
        },
        Pat::LiteralReal(f) => quote! {
            if (#var).as_fraction().is_some_and(|r| r == #f) { #inner } else { None }
        },
        // First occurrence of a name -> capture the term.
        Pat::FreeVar { id, same_as: None } => quote! {
            { let #id = #var; #inner }
        },
        // Repeated occurrence: the term must be equal to the one captured by the
        // first occurrence, otherwise the whole match fails.
        Pat::FreeVar { same_as: Some(SameAs::Term(first)), .. } => quote! {
            if (#var) == (#first) { #inner } else { None }
        },
        // Occurrence of a variable bound by an explicit binding list: the term
        // must be that variable. Sorts are compared structurally, as a sort
        // reached through a term need not be the pool's shared instance.
        Pat::FreeVar { same_as: Some(SameAs::Bound(entry)), .. } => quote! {
            if let crate::ast::Term::Var(__mt_name, __mt_sort) = (&(#var) as &crate::ast::Term)
                && __mt_name == &(#entry).0
                && **__mt_sort == *(#entry).1
            {
                #inner
            } else {
                None
            }
        },
        // Variadic as a standalone pattern: bind the value directly.
        Pat::Variadic(id) => quote! {
            { let #id = #var; #inner }
        },
        Pat::Op { op, args } => {
            let variant = op_to_variant(op);

            // Special case: sole variadic arg — capture entire args slice directly.
            if args.len() == 1
                && let Pat::Variadic(var_id) = &args[0]
            {
                *ctr += 1;
                let args_ident = format_ident!("__mt_args_{}", ctr);
                let body = gen_sole_variadic_body(var_id, &args_ident, inner);
                return quote! {
                    if let crate::ast::Term::Op(#variant, #args_ident) = (&(#var) as &crate::ast::Term) {
                        #body
                    } else {
                        None
                    }
                };
            }

            // Normal fixed-arity case.
            let n = args.len();
            let arg_idents: Vec<Ident> = (0..n)
                .map(|_| {
                    *ctr += 1;
                    format_ident!("__mt_arg_{}", ctr)
                })
                .collect();
            *ctr += 1;
            let args_vec = format_ident!("__mt_args_{}", ctr);

            // Build the continuation right-to-left so that the leftmost
            // argument is the outermost binding (correct DFS order).
            let mut body = inner;
            for (sub_pat, arg_id) in args.iter().zip(arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }

            quote! {
                if let crate::ast::Term::Op(#variant, #args_vec) = (&(#var) as &crate::ast::Term) {
                    if let [#(#arg_idents),*] = #args_vec.as_slice() {
                        #body
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
        Pat::ParamOp { op, op_args, args } => {
            let variant = param_op_to_variant(op);
            let n_op = op_args.len();

            let op_arg_idents: Vec<Ident> = (0..n_op)
                .map(|_| {
                    *ctr += 1;
                    format_ident!("__mt_arg_{}", ctr)
                })
                .collect();
            *ctr += 1;
            let op_args_vec = format_ident!("__mt_args_{}", ctr);
            *ctr += 1;
            let args_vec = format_ident!("__mt_args_{}", ctr);

            // Special case: sole variadic in args — capture entire args slice directly.
            if args.len() == 1
                && let Pat::Variadic(var_id) = &args[0]
            {
                let slice_body = gen_sole_variadic_body(var_id, &args_vec, inner);
                let mut body = slice_body;
                for (sub_pat, arg_id) in op_args.iter().zip(op_arg_idents.iter()).rev() {
                    let v = quote! { #arg_id };
                    body = gen_match(sub_pat, &v, body, ctr);
                }
                return quote! {
                    if let crate::ast::Term::ParamOp {
                        op: #variant,
                        op_args: #op_args_vec,
                        args: #args_vec,
                    } = (&(#var) as &crate::ast::Term) {
                        if let [#(#op_arg_idents),*] = #op_args_vec.as_slice() {
                            #body
                        } else { None }
                    } else { None }
                };
            }

            let n_arg = args.len();
            let arg_idents: Vec<Ident> = (0..n_arg)
                .map(|_| {
                    *ctr += 1;
                    format_ident!("__mt_arg_{}", ctr)
                })
                .collect();

            // Build continuation right-to-left: regular args first (innermost), then op_args.
            // This ensures op_args appear before args in the final flat tuple, matching
            // the left-to-right DFS order of the pattern ((_ op i j) a b) -> (i, j, a, b).
            let mut body = inner;
            for (sub_pat, arg_id) in args.iter().zip(arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }
            for (sub_pat, arg_id) in op_args.iter().zip(op_arg_idents.iter()).rev() {
                let v = quote! { #arg_id };
                body = gen_match(sub_pat, &v, body, ctr);
            }

            quote! {
                if let crate::ast::Term::ParamOp {
                    op: #variant,
                    op_args: #op_args_vec,
                    args: #args_vec,
                } = (&(#var) as &crate::ast::Term) {
                    if let [#(#op_arg_idents),*] = #op_args_vec.as_slice() {
                        if let [#(#arg_idents),*] = #args_vec.as_slice() {
                            #body
                        } else { None }
                    } else { None }
                } else { None }
            }
        }
        // Rename destructured field to 'inner_pat' to avoid shadowing the
        // 'inner' parameter of gen_match (which is the continuation TokenStream2).
        Pat::Binder {
            binder,
            bindings,
            inner: inner_pat,
        } => {
            let binder_variant = match binder.as_str() {
                "forall" => quote! { crate::ast::Binder::Forall },
                "exists" => quote! { crate::ast::Binder::Exists },
                "choice" => quote! { crate::ast::Binder::Choice },
                "lambda" => quote! { crate::ast::Binder::Lambda },
                other => panic!("unknown binder in match_term_flat!: {other}"),
            };

            *ctr += 1;
            let inner_var = format_ident!("__mt_arg_{}", ctr);

            // Recursively generate matching for the body of the binder,
            // passing 'inner' (the continuation) as the innermost code.
            let body = gen_match(inner_pat, &quote! { #inner_var }, inner, ctr);

            match bindings {
                BindingsPat::Any(bindings_id) => quote! {
                    if let crate::ast::Term::Binder(#binder_variant, #bindings_id, #inner_var) =
                        (&(#var) as &crate::ast::Term)
                    {
                        #body
                    } else {
                        None
                    }
                },
                BindingsPat::Explicit(entries) => {
                    *ctr += 1;
                    let list_id = format_ident!("__mt_bindings_{}", ctr);
                    let entry_ids: Vec<&Ident> = entries.iter().map(|e| &e.entry_id).collect();
                    // match the sorts right-to-left so the leftmost entry is the
                    // outermost binding (DFS order of the tuple), then the body
                    let mut body = body;
                    for e in entries.iter().rev() {
                        let entry_id = &e.entry_id;
                        let v = quote! { (&(#entry_id).1) };
                        body = gen_match(&e.sort, &v, body, ctr);
                    }
                    quote! {
                        if let crate::ast::Term::Binder(#binder_variant, #list_id, #inner_var) =
                            (&(#var) as &crate::ast::Term)
                        {
                            if let [#(#entry_ids),*] = &#list_id[..] {
                                #body
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                }
            }
        }
    }
}

#[proc_macro]
pub fn match_term(input: TokenStream) -> TokenStream {
    let Input { pattern, expr } = parse_macro_input!(input as Input);

    // Single counter shared between parse_pat (for variable/variadic/binder idents)
    // and gen_match (for temporary arg idents). gen_match starts at 1000 to avoid
    // collisions with the idents generated by parse_pat.
    let mut ctx = ParseCtx { ctr: 0, bound: HashMap::new(), bound_vars: HashMap::new() };
    let pat = parse_pat(pattern, &mut ctx);
    let free_vars = pat.free_vars();

    // Innermost code: return a flat tuple of all captured variables.
    let result = match free_vars.len() {
        0 => quote! { Some(()) },
        1 => {
            let v = &free_vars[0];
            quote! { Some(#v) }
        }
        _ => quote! { Some((#(#free_vars),*)) },
    };

    let mut gen_ctr = 1000usize;
    let body = gen_match(&pat, &quote! { #expr }, result, &mut gen_ctr);

    quote! {{ #body }}.into()
}

#[proc_macro]
pub fn get_op_variant(input: TokenStream) -> TokenStream {
    let input = input.to_string();
    op_to_variant(&input).into()
}

#[proc_macro]
pub fn get_param_op_variant(input: TokenStream) -> TokenStream {
    let input = input.to_string();
    param_op_to_variant(&input).into()
}

#[proc_macro_derive(GenerateSetters, attributes(skip_setter, const_setters))]
pub fn generate_setters(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let struct_name = &ast.ident;
    let generics = &ast.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let const_modifier = if ast.attrs.iter().any(|a| a.path().is_ident("const_setters")) {
        quote! { const }
    } else {
        quote! {}
    };

    let syn::Data::Struct(DataStruct { fields, .. }) = &ast.data else {
        panic!("can only be used with a struct")
    };
    let generated_setters = fields.iter().map(|f| {
        let field_name = f.ident.clone().expect("expected the field to have a name");
        let ty = f.ty.clone();
        let doc = f.attrs.iter().filter(|v| v.meta.path().is_ident("doc"));

        if f.attrs.iter().any(|a| a.path().is_ident("skip_setter")) {
            quote! {}
        } else {
            quote! {
                #(#doc)*
                #[inline(always)]
                pub #const_modifier fn #field_name(mut self, val: #ty) -> Self {
                    self.#field_name = val;
                    self
                }
            }
        }
    });

    quote! {
        impl #impl_generics #struct_name #ty_generics #where_clause {
            #(#generated_setters)*
        }
    }
    .into()
}

/// Run `git` on the manifest directory with the given arguments, and return its output.
fn run_git(args: &[&str]) -> Option<String> {
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")?;
    let output = Command::new("git")
        .arg("-C")
        .arg(manifest_dir)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|c| c.wait_with_output())
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let mut stdout = output.stdout;
    if stdout.last().copied() == Some(b'\n') {
        stdout.pop();
    }
    String::from_utf8(stdout).ok()
}

/// Generates a version string for Carcara.
#[proc_macro]
pub fn version_string(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as syn::parse::Nothing); // error if we are given args

    let version = std::env::var("CARGO_PKG_VERSION").expect("couldn't get package version");
    let hash = run_git(&["describe", "--always"]);
    let branch = run_git(&["rev-parse", "--abbrev-ref", "HEAD"]).filter(|b| b != "HEAD");

    let full_string = match (hash, branch) {
        (None, _) => version.to_owned(),
        (Some(hash), None) => format!("{} [git {}]", version, hash),
        (Some(hash), Some(branch)) => format!("{} [git {} {}]", version, hash, branch),
    };
    quote! { #full_string }.into()
}
