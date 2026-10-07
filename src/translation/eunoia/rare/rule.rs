//! The compiler of one RARE definition into an Eunoia rule.

use super::RareTranslationError;
use crate::{
    ast::{
        Constant, Operator, Rc, Sort, Term,
        pool::Storage,
        rare_rules::{AttributeParameters, RuleDefinition},
    },
    translation::eunoia::{alethe_signature::theory::AletheTheory, ast::*},
};
use std::cell::RefCell;

pub(super) struct RuleCompiler<'a> {
    pub(super) rule: &'a RuleDefinition,
    pub(super) theory: &'a AletheTheory,
    /// The store the rule's terms are allocated in (the Eunoia AST is hash-consed).
    terms: RefCell<Storage<EunoiaTerm>>,
}

impl<'a> RuleCompiler<'a> {
    pub(super) fn new(rule: &'a RuleDefinition, theory: &'a AletheTheory) -> Self {
        RuleCompiler {
            rule,
            theory,
            terms: RefCell::new(Storage::default()),
        }
    }
}

impl RuleCompiler<'_> {
    pub(super) fn add(&self, term: EunoiaTerm) -> Rc<EunoiaTerm> {
        self.terms.borrow_mut().add(term)
    }

    pub(super) fn id(&self, name: impl Into<String>) -> Rc<EunoiaTerm> {
        self.add(EunoiaTerm::Id(name.into()))
    }

    pub(super) fn app(&self, name: impl Into<String>, args: Vec<Rc<EunoiaTerm>>) -> Rc<EunoiaTerm> {
        self.add(EunoiaTerm::App(name.into(), args))
    }

    /// Runs `f` on the store, for the signature's encoding to allocate the terms it
    /// builds in.
    pub(super) fn with_terms<T>(&self, f: impl FnOnce(&mut Storage<EunoiaTerm>) -> T) -> T {
        f(&mut self.terms.borrow_mut())
    }

    pub(super) fn error(&self, reason: impl Into<String>) -> RareTranslationError {
        RareTranslationError {
            rule: self.rule.name.clone(),
            reason: reason.into(),
        }
    }

    pub(super) fn sort(&self, sort: &Sort) -> Result<EunoiaType, RareTranslationError> {
        Ok(match sort {
            Sort::Bool => EunoiaType::Bool,
            Sort::Int => EunoiaType::Name("Int".into()),
            Sort::Real => EunoiaType::Real,
            Sort::Type => EunoiaType::Type,
            Sort::Var(name) => EunoiaType::Name(name.clone()),
            Sort::Atom(name, args) if args.is_empty() => EunoiaType::Name(name.to_string()),
            Sort::Function(sorts) if sorts.len() >= 2 => EunoiaType::Fun(
                vec![],
                sorts[..sorts.len() - 1]
                    .iter()
                    .map(|s| self.sort(s))
                    .collect::<Result<_, _>>()?,
                Box::new(self.sort(sorts.last().unwrap())?),
            ),
            _ => return Err(self.error(format!("unsupported sort '{sort}'"))),
        })
    }

    fn is_list(&self, name: &str) -> bool {
        self.rule
            .parameters
            .get(name)
            .is_some_and(|p| p.attribute == AttributeParameters::List)
    }

    pub(super) fn is_list_term(&self, term: &Term) -> bool {
        matches!(term, Term::Var(name, _) if self.is_list(name))
    }

    pub(super) fn sort_term(&self, sort: &Sort) -> Result<Rc<EunoiaTerm>, RareTranslationError> {
        // Ethos binds argument terms, not the type parameters appearing only
        // in their declarations. Recover such a type from its scalar anchor.
        let name = sort.to_string();
        if self
            .rule
            .parameters
            .get(&name)
            .is_some_and(|p| p.sort.as_ref() == &Sort::Type)
            && !self.rule.arguments.contains(&name)
        {
            if let Some(anchor) = self.rule.arguments.iter().find(|arg| {
                self.rule.parameters.get(*arg).is_some_and(|p| {
                    p.attribute != AttributeParameters::List && p.sort.as_ref() == sort
                })
            }) {
                return Ok(self.app("eo::typeof", vec![self.id(anchor.clone())]));
            }
            return Err(self.error(format!(
                "no scalar argument determines element sort '{sort}'"
            )));
        }
        Ok(self.add(EunoiaTerm::Type(self.sort(sort)?)))
    }

    pub(super) fn term(
        &self,
        term: &Term,
        allow_list: bool,
    ) -> Result<Rc<EunoiaTerm>, RareTranslationError> {
        Ok(match term {
            Term::Var(name, _) => {
                if self.is_list(name) && !allow_list {
                    return Err(self.error(format!(
                        "list parameter '{name}' used outside a supported variadic application"
                    )));
                }
                self.id(name.clone())
            }
            Term::Const(Constant::Integer(n)) => self.add(EunoiaTerm::Numeral(n.clone())),
            Term::Const(Constant::Real(r)) => self.add(EunoiaTerm::Decimal(r.clone())),
            Term::Op(Operator::True, _) => self.add(EunoiaTerm::True),
            Term::Op(Operator::False, _) => self.add(EunoiaTerm::False),
            Term::Op(op, operands) => {
                let symbol = self
                    .theory
                    .operator(*op)
                    .ok_or_else(|| self.error(format!("unsupported term in rule: {term}")))?;
                self.compile_application(*op, symbol, operands)?
            }
            Term::App(f, operands) => {
                // RARE list splicing into arbitrary functions needs arity-aware
                // application construction and is deliberately rejected here.
                self.add(EunoiaTerm::HOApp(
                    self.term(f, false)?,
                    operands
                        .iter()
                        .map(|x| self.term(x, false))
                        .collect::<Result<_, _>>()?,
                ))
            }
            _ => return Err(self.error(format!("unsupported term in rule: {term}"))),
        })
    }

    pub(super) fn operands(
        &self,
        operands: &[Rc<Term>],
        allow_list: bool,
    ) -> Result<Vec<Rc<EunoiaTerm>>, RareTranslationError> {
        operands.iter().map(|x| self.term(x, allow_list)).collect()
    }

    pub(super) fn compile(
        &self,
        generated_name: &str,
    ) -> Result<EunoiaCommand, RareTranslationError> {
        let mut parameters = Vec::new();
        for (name, parameter) in &self.rule.parameters {
            parameters.push(self.compile_parameter(name, parameter)?);
        }
        for (i, formula) in self.rule.premises.iter().enumerate() {
            parameters.push(self.compile_premise(i, formula)?);
        }

        let mut typed_params = Vec::new();
        let mut premises = Vec::new();
        let mut requirements = Vec::new();
        for parameter in parameters {
            typed_params.push(EunoiaTypedParam {
                name: parameter.name,
                eunoia_type: parameter.eunoia_type,
                attrs: parameter.attrs,
            });
            premises.extend(parameter.premise);
            requirements.extend(parameter.requirements);
        }
        Ok(EunoiaCommand::DeclareRule {
            name: generated_name.into(),
            typed_params: EunoiaList { list: typed_params },
            arguments: self
                .rule
                .arguments
                .iter()
                .map(|name| self.id(name.clone()))
                .collect(),
            premises,
            requirements,
            conclusion: self.app("@cl", vec![self.term(&self.rule.conclusion, false)?]),
        })
    }
}
