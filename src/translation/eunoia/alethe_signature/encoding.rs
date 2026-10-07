//! The two encodings the Alethe-in-Eunoia signature declares. `AletheTheory`
//! carries the encoding, so whoever emits Eunoia gets it from the signature.

use crate::{
    ast::{Operator, Rc, pool::Storage},
    translation::eunoia::ast::*,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    /// `eo::List` sequences and the `_native` declarations, built on list
    /// builtins.
    Native,
    /// Rare-lists, whose nil carries the element sort, and the declarations
    /// checked by library programs.
    RareList,
}

use Encoding::*;

fn id(terms: &mut Storage<EunoiaTerm>, name: impl Into<String>) -> Rc<EunoiaTerm> {
    terms.add(EunoiaTerm::Id(name.into()))
}

fn app(
    terms: &mut Storage<EunoiaTerm>,
    name: impl Into<String>,
    args: Vec<Rc<EunoiaTerm>>,
) -> Rc<EunoiaTerm> {
    terms.add(EunoiaTerm::App(name.into(), args))
}

impl Encoding {
    pub fn new(native: bool) -> Self {
        if native { Native } else { RareList }
    }

    /// The symbol of `op`, when the encodings name it differently.
    pub fn symbol(self, op: Operator) -> Option<&'static str> {
        match (op, self) {
            (Operator::Distinct, Native) => Some("distinct_native"),
            (Operator::Distinct, RareList) => Some("distinct"),
            _ => None,
        }
    }

    /// A sequence of `elements`, allocated in `terms`. Only the empty rare-list
    /// needs `sort`, their sort; without it, the nil is left untyped for the
    /// caller to complete.
    pub(crate) fn sequence(
        self,
        terms: &mut Storage<EunoiaTerm>,
        elements: Vec<Rc<EunoiaTerm>>,
        sort: Option<Rc<EunoiaTerm>>,
    ) -> Rc<EunoiaTerm> {
        match (self, elements.is_empty(), sort) {
            (Native, true, _) => id(terms, "eo::List::nil"),
            (Native, false, _) => app(terms, "eo::List::cons", elements),
            (RareList, true, Some(sort)) => app(terms, "@rare-list-nil", vec![sort]),
            (RareList, true, None) => id(terms, "@rare-list-nil"),
            (RareList, false, _) => app(terms, "@rare-list-cons", elements),
        }
    }

    /// The spine of the operator `symbol`, whose nil is `nil`, over
    /// `elements` of sort `sort`: list fragments are spliced, and ordinary
    /// nested formulas remain elements.
    pub(crate) fn spine(
        self,
        terms: &mut Storage<EunoiaTerm>,
        symbol: &str,
        nil: Rc<EunoiaTerm>,
        sort: Rc<EunoiaTerm>,
        elements: Vec<Rc<EunoiaTerm>>,
    ) -> Rc<EunoiaTerm> {
        let sequence = self.sequence(terms, elements, Some(sort.clone()));
        let operator = id(terms, symbol);
        match self {
            Native => app(
                terms,
                "$normalize_eo_list_native",
                vec![sort.clone(), sort, operator, sequence],
            ),
            RareList => app(
                terms,
                "$normalize_rare_list",
                vec![sort, operator, nil, sequence],
            ),
        }
    }

    /// `spine`, or its only element when it has one.
    pub(crate) fn singleton_elim(
        self,
        terms: &mut Storage<EunoiaTerm>,
        symbol: &str,
        nil: Rc<EunoiaTerm>,
        spine: Rc<EunoiaTerm>,
    ) -> Rc<EunoiaTerm> {
        let operator = id(terms, symbol);
        match self {
            Native => app(terms, "eo::list_singleton_elim", vec![operator, spine]),
            RareList => app(terms, "$f_list_singleton_elim", vec![operator, nil, spine]),
        }
    }

    /// The type of a list parameter whose elements have type `element`.
    pub fn list_type(self, element: EunoiaType) -> EunoiaType {
        match self {
            Native => EunoiaType::Name("eo::List".into()),
            RareList => element,
        }
    }

    /// The requirement that the list parameter `name` has elements of `sort`.
    pub(crate) fn list_requirement(
        self,
        terms: &mut Storage<EunoiaTerm>,
        sort: Rc<EunoiaTerm>,
        name: &str,
    ) -> (Rc<EunoiaTerm>, Rc<EunoiaTerm>) {
        let parameter = id(terms, name);
        match self {
            // Normalizing into eo::List checks every element and preserves
            // the carrier.
            Native => {
                let carrier = terms.add(EunoiaTerm::Type(EunoiaType::Name("eo::List".into())));
                let cons = id(terms, "eo::List::cons");
                (
                    app(
                        terms,
                        "$normalize_eo_list_native",
                        vec![sort, carrier, cons, parameter.clone()],
                    ),
                    parameter,
                )
            }
            // The nil terminator carries the element sort.
            RareList => (
                app(terms, "$rare_list_of_sort", vec![sort, parameter]),
                terms.add(EunoiaTerm::True),
            ),
        }
    }
}
