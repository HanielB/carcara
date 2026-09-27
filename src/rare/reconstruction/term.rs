//! Encoded terms, rewrite patterns, and their Alethe decoding.
use std::{cmp::Ordering, collections::BTreeMap};
use rug::{Integer, Rational};
use std::collections::HashMap;

/// An encoded term, hash-consed: a structurally equal term built in the
/// same thread is the same node, so a term with shared subterms is a DAG
/// whatever its source (the goal read back from egglog's text is a tree
/// there), a clone is a pointer copy, and equality and hashing are a
/// pointer comparison and a cached hash.  The fields are read through
/// `Deref` (`term.op`, `term.children`).
#[derive(Clone)]
pub struct Term(std::sync::Arc<TermNode>);

pub struct TermNode {
    pub op: String,
    pub children: Vec<Term>,
    /// Structural hash, from the operator and the children's hashes.
    hash: u64,
    /// The size as a tree (saturating): what the representative choice
    /// compares, cached so that no one walks the tree for it.
    size: usize,
}

impl std::ops::Deref for Term {
    type Target = TermNode;
    fn deref(&self) -> &TermNode {
        &self.0
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        // Interned terms are equal exactly when they are one node; the
        // structural test only runs for terms of different threads, and
        // stops at the first shared child.
        std::sync::Arc::ptr_eq(&self.0, &other.0)
            || (self.0.hash == other.0.hash
                && self.0.size == other.0.size
                && self.op == other.op
                && self.children == other.children)
    }
}

impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    /// The derived order of the tree form (operator, then the children
    /// lexicographically); shared children compare equal at once, so a
    /// comparison follows one path down.
    fn cmp(&self, other: &Self) -> Ordering {
        if std::sync::Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.op
            .cmp(&other.op)
            .then_with(|| self.children.cmp(&other.children))
    }
}

impl std::fmt::Debug for Term {
    /// Bounded like `to_egglog`: a debug line never expands the DAG.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_egglog())
    }
}

thread_local! {
    static INTERNED: std::cell::RefCell<Interner> = std::cell::RefCell::new(Interner::default());
}

/// The live terms of a thread by structural hash (weak references: a term
/// no one holds goes, and its entry with the next sweep).
#[derive(Default)]
struct Interner {
    table: HashMap<u64, Vec<std::sync::Weak<TermNode>>>,
    since_sweep: usize,
}

impl Term {
    pub fn new(op: &str, children: Vec<Self>) -> Self {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        op.hash(&mut hasher);
        children.len().hash(&mut hasher);
        for child in &children {
            hasher.write_u64(child.0.hash);
        }
        let hash = hasher.finish();
        INTERNED.with(|interned| {
            let mut interned = interned.borrow_mut();
            if let Some(bucket) = interned.table.get(&hash) {
                for weak in bucket {
                    if let Some(node) = weak.upgrade() {
                        if node.op == op
                            && node.children.len() == children.len()
                            && node.children.iter().zip(&children).all(|(a, b)| a == b)
                        {
                            return Term(node);
                        }
                    }
                }
            }
            let size = children
                .iter()
                .fold(1usize, |total, child| total.saturating_add(child.0.size));
            let node = std::sync::Arc::new(TermNode {
                op: op.to_owned(),
                children,
                hash,
                size,
            });
            interned
                .table
                .entry(hash)
                .or_default()
                .push(std::sync::Arc::downgrade(&node));
            interned.since_sweep += 1;
            if interned.since_sweep >= 1 << 20 {
                interned.since_sweep = 0;
                interned.table.retain(|_, bucket| {
                    bucket.retain(|weak| weak.strong_count() > 0);
                    !bucket.is_empty()
                });
            }
            Term(node)
        })
    }

    pub fn leaf(op: &str) -> Self {
        Self::new(op, Vec::new())
    }

    /// The size as a tree, saturating (cached).
    pub fn size(&self) -> usize {
        self.0.size
    }

    /// The number of distinct nodes: the size of the DAG.
    pub fn dag_size(&self) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            if seen.insert(std::sync::Arc::as_ptr(&term.0)) {
                stack.extend(term.children.iter());
            }
        }
        seen.len()
    }

    /// The term in egglog syntax, for a log line, as a DAG: a compound
    /// subterm with more than one parent is `#k=(...)` where it first
    /// occurs and `#k` after, and at most a few hundred nodes are written,
    /// the rest elided.
    pub fn to_egglog(&self) -> String {
        let key = |term: &Term| std::sync::Arc::as_ptr(&term.0);
        let mut parents: HashMap<*const TermNode, usize> = HashMap::new();
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            if !seen.insert(key(term)) {
                continue;
            }
            for child in &term.children {
                *parents.entry(key(child)).or_default() += 1;
                stack.push(child);
            }
        }
        let mut labels = HashMap::new();
        let mut out = String::new();
        let mut budget = 400usize;
        self.write_egglog(&mut out, &mut budget, &parents, &mut labels);
        out
    }

    fn write_egglog(
        &self,
        out: &mut String,
        budget: &mut usize,
        parents: &HashMap<*const TermNode, usize>,
        labels: &mut HashMap<*const TermNode, usize>,
    ) {
        if *budget == 0 {
            out.push('…');
            return;
        }
        *budget -= 1;
        if self.children.is_empty() {
            if self.op == "Empty" {
                out.push_str("(Empty)");
            } else {
                out.push_str(&self.op);
            }
            return;
        }
        let key = std::sync::Arc::as_ptr(&self.0);
        if let Some(label) = labels.get(&key) {
            out.push_str(&format!("#{label}"));
            return;
        }
        if parents.get(&key).is_some_and(|&count| count > 1) && self.size() > 2 {
            let label = labels.len();
            labels.insert(key, label);
            out.push_str(&format!("#{label}="));
        }
        out.push('(');
        out.push_str(&self.op);
        for child in &self.children {
            out.push(' ');
            child.write_egglog(out, budget, parents, labels);
        }
        out.push(')');
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Var(&'static str),
    App(&'static str, Vec<Pattern>),
}

#[derive(Clone, Debug)]
pub struct Rewrite {
    pub name: &'static str,
    pub lhs: Pattern,
    pub rhs: Pattern,
    /// The sort guards of the generated rule: pattern variables that may
    /// only bind a term of that sort (`Int`, `Real` or `Bool`), which keeps
    /// a rule instantiated for one numeric sort off the other.
    pub guards: Vec<(String, &'static str)>,
    /// The rule's `:list` parameters, which stand for a segment of an n-ary
    /// operator's arguments rather than for one argument.
    pub lists: Vec<String>,
    /// The premises of a conditional rule, each an equality the rule's
    /// instance holds only when it does; a certificate citing the rule
    /// carries a proof of each.
    pub premises: Vec<(Pattern, Pattern)>,
}

pub type Substitution = BTreeMap<String, Term>;
pub type ClassSubstitution = BTreeMap<&'static str, u32>;

pub fn match_pattern(pattern: &Pattern, term: &Term, substitution: &mut Substitution) -> bool {
    match pattern {
        Pattern::Var(variable) => match substitution.get(*variable) {
            Some(previous) => previous == term,
            None => {
                substitution.insert((*variable).to_owned(), term.clone());
                true
            }
        },
        Pattern::App(op, children) => {
            op == &term.op
                && children.len() == term.children.len()
                && children
                    .iter()
                    .zip(&term.children)
                    .all(|(pattern, term)| match_pattern(pattern, term, substitution))
        }
    }
}

pub fn has_unbound_variables(pattern: &Pattern, substitution: &ClassSubstitution) -> bool {
    match pattern {
        Pattern::Var(variable) => !substitution.contains_key(variable),
        Pattern::App(_, children) => children
            .iter()
            .any(|child| has_unbound_variables(child, substitution)),
    }
}

pub fn instantiate(pattern: &Pattern, substitution: &Substitution) -> Option<Term> {
    match pattern {
        Pattern::Var(variable) => substitution.get(*variable).cloned(),
        Pattern::App(op, children) => Some(Term::new(
            op,
            children
                .iter()
                .map(|child| instantiate(child, substitution))
                .collect::<Option<Vec<_>>>()?,
        )),
    }
}

pub fn encoded_args(elements: Vec<Term>) -> Term {
    elements
        .into_iter()
        .rev()
        .fold(Term::leaf("Empty"), |tail, element| {
            Term::new("Args", vec![element, tail])
        })
}

pub fn encoded_app(operator: &str, elements: Vec<Term>) -> Term {
    Term::new("Mk", vec![Term::new(operator, vec![encoded_args(elements)])])
}

pub fn encoded_bool(value: bool) -> Term {
    let literal = if value { "true" } else { "false" };
    Term::new("Mk", vec![Term::new("Bool", vec![Term::leaf(literal)])])
}

/// Elements of an encoded argument list `(Args e1 (Args e2 ... (Empty)))`.
pub fn list_elements(list: &Term) -> Option<Vec<Term>> {
    let mut elements = Vec::new();
    let mut current = list;
    loop {
        match (current.op.as_str(), current.children.as_slice()) {
            ("Empty", []) => return Some(elements),
            ("Args", [element, tail]) => {
                // A chain is read as a concatenation of segments: the
                // engine's re-association lets a cell's head be a sublist,
                // and a `:list` parameter that binds nothing leaves an empty
                // segment, which contributes no arguments.
                match (element.op.as_str(), element.children.as_slice()) {
                    ("Empty", []) => (),
                    ("Args", [_, _]) => elements.extend(list_elements(element)?),
                    _ => elements.push(element.clone()),
                }
                current = tail;
            }
            // The re-association also makes cells whose tail is a lone
            // element, `(Args a b)` for the segment `a b`: the segment a
            // `:list` variable binds is represented that way, and its
            // representative reaches the search through the grounded
            // instances.  Such a tail ends the chain as its last element.
            ("Args", _) => return None,
            _ if !elements.is_empty() || list.op == "Args" => {
                elements.push(current.clone());
                return Some(elements);
            }
            _ => return None,
        }
    }
}

/// `term` with its argument chains flattened: the segments a re-association
/// nests and the empty one a `:list` parameter leaves when it binds nothing
/// both disappear, so two encodings of the same Alethe term compare equal.
/// For comparing terms, not for looking them up: the e-graph holds the
/// shapes, not this normal form.
pub fn flat_form(term: &Term) -> Term {
    flat_form_memo(term, &mut HashMap::new())
}

/// `flat_form` once per distinct subterm.
fn flat_form_memo(term: &Term, memo: &mut HashMap<Term, Term>) -> Term {
    if let Some(known) = memo.get(term) {
        return known.clone();
    }
    let result = if term.op == "Args" || term.op == "Empty" {
        match list_elements(term) {
            Some(elements) => encoded_args(elements.iter().map(|e| flat_form_memo(e, memo)).collect()),
            None => Term::new(&term.op, term.children.iter().map(|c| flat_form_memo(c, memo)).collect()),
        }
    } else {
        Term::new(&term.op, term.children.iter().map(|c| flat_form_memo(c, memo)).collect())
    };
    memo.insert(term.clone(), result.clone());
    result
}

/// Decompose an encoded application `Mk(op(list))` into its operator and
/// argument elements.
pub fn encoded_application(term: &Term) -> Option<(&str, Vec<Term>)> {
    let ("Mk", [application]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let [arguments] = application.children.as_slice() else {
        return None;
    };
    Some((application.op.as_str(), list_elements(arguments)?))
}

pub fn bool_value(term: &Term) -> Option<bool> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let ("Bool", [literal]) = (inner.op.as_str(), inner.children.as_slice()) else {
        return None;
    };
    match literal.op.as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

pub fn rational_from_leaves(numer: &Term, denom: &Term) -> Option<Rational> {
    let numer: Integer = numer.op.parse().ok()?;
    let denom: Integer = denom.op.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

/// A serialized `BigRat` literal, `(bigrat (bigint "n") (bigint "d"))`.
pub fn bigrat_literal(literal: &str) -> Option<Rational> {
    let parts: Vec<&str> = literal.split('"').collect();
    let numer: Integer = parts.get(1)?.parse().ok()?;
    let denom: Integer = parts.get(3)?.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

pub fn integer_of(term: &Term) -> Option<i64> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Num", [value]) => value.op.parse().ok(),
        _ => None,
    }
}

/// A rational literal in either encoding: the parser's `Real` or the
/// solver's `RatConst`.
pub fn rational_of(term: &Term) -> Option<Rational> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Real", [numer, denom]) => rational_from_leaves(numer, denom),
        ("RatConst", [literal]) => bigrat_literal(&literal.op),
        _ => None,
    }
}

pub fn encoded_num(value: i64) -> Term {
    Term::new("Mk", vec![Term::new("Num", vec![Term::leaf(&value.to_string())])])
}

/// The solver's rational constant, with the `BigRat` literal spelled the
/// way egglog serializes it.
pub fn encoded_rational(value: &Rational) -> Term {
    let literal = format!(
        "(bigrat (from-string \"{}\") (from-string \"{}\"))",
        value.numer(),
        value.denom()
    );
    Term::new("Mk", vec![Term::new("RatConst", vec![Term::leaf(&literal)])])
}

/// Decode an encoded term back to SMT-LIB/Alethe syntax: `Mk`-wrapped
/// constants, booleans, variables, `@`-operator applications over `Args`
/// lists, and curried `App` chains for uninterpreted functions.  Hashed
/// variable identifiers resolve through `names` (built by walking the
/// original conclusion against the encoded goals); solver-internal shapes
/// decode to `None`.
pub fn decode_term(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    decode_inner(inner, names)
}

pub fn decode_any(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    if term.op == "Mk" {
        decode_term(term, names)
    } else {
        decode_inner(term, names)
    }
}

pub fn decode_inner(inner: &Term, names: &HashMap<String, String>) -> Option<String> {
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Const", [name]) => Some(name.op.trim_matches('"').to_owned()),
        ("Bool", [literal]) => Some(literal.op.clone()),
        ("Op", [name]) => Some(name.op.trim_matches('"').to_owned()),
        // Numerals print the way Carcara prints them, so they parse back.
        ("Num", [value]) => Some(value.op.clone()),
        ("Real", [numer, denom]) => Some(if denom.op == "1" && !numer.op.starts_with('-') {
            format!("{}.0", numer.op)
        } else {
            format!("{}/{}", numer.op, denom.op)
        }),
        ("RatConst", [literal]) => bigrat_literal(&literal.op).map(|value| {
            if value.is_integer() && value.cmp0() != Ordering::Less {
                format!("{}.0", value.numer())
            } else {
                format!("{}/{}", value.numer(), value.denom())
            }
        }),
        // A numeral past i64, carried as a big rational with denominator 1.
        ("BigNum", [literal]) => bigrat_literal(&literal.op)
            .filter(|value| value.is_integer())
            .map(|value| value.numer().to_string()),
        ("Var", [id, _sort]) => Some(
            names
                .get(&id.op)
                .cloned()
                .unwrap_or_else(|| format!("v{}", id.op.trim_start_matches('-'))),
        ),
        ("App", [_, _]) => {
            let mut arguments = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                arguments.push(argument);
                current = next;
            }
            arguments.reverse();
            let head = decode_any(current, names)?;
            let arguments = arguments
                .iter()
                .map(|argument| decode_any(argument, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", head, arguments.join(" ")))
        }
        (operator, [arguments]) if operator.starts_with('@') => {
            let elements = list_elements(arguments)?
                .iter()
                .map(|element| decode_any(element, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", &operator[1..], elements.join(" ")))
        }
        _ => None,
    }
}

/// Decodes encoded terms into Alethe text with sharing across all the terms
/// decoded with one table (the steps of one certificate), so that no term
/// is printed as a tree: the first decoding of an application with a
/// compound argument is `(! t :named <prefix><i>)`, every later one the
/// name.  A failed decoding forgets the names it defined; so does
/// `rollback` to a `mark`, for a caller that discards emitted text.
pub struct SharedDecoder {
    prefix: String,
    defined: HashMap<Term, String>,
    order: Vec<Term>,
}

impl SharedDecoder {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self { prefix: prefix.into(), defined: HashMap::new(), order: Vec::new() }
    }

    pub fn mark(&self) -> usize {
        self.order.len()
    }

    pub fn rollback(&mut self, mark: usize) {
        for term in self.order.drain(mark..) {
            self.defined.remove(&term);
        }
    }

    /// `term`'s text, wrapped in `Mk` or not.
    pub fn decode(&mut self, term: &Term, names: &HashMap<String, String>) -> Option<String> {
        let mark = self.mark();
        let text = self.decode_inner(unwrapped(term), names);
        if text.is_none() {
            self.rollback(mark);
        }
        text
    }

    fn decode_inner(&mut self, inner: &Term, names: &HashMap<String, String>) -> Option<String> {
        if let Some(name) = self.defined.get(inner) {
            return Some(name.clone());
        }
        let (text, compound) = match (inner.op.as_str(), inner.children.as_slice()) {
            ("App", [_, _]) => {
                let mut arguments = Vec::new();
                let mut current = inner;
                while let ("App", [next, argument]) =
                    (current.op.as_str(), current.children.as_slice())
                {
                    arguments.push(argument);
                    current = next;
                }
                arguments.reverse();
                let compound = !is_atom(unwrapped(current))
                    || arguments.iter().any(|argument| !is_atom(unwrapped(argument)));
                let head = self.decode_inner(unwrapped(current), names)?;
                let arguments = arguments
                    .iter()
                    .map(|argument| self.decode_inner(unwrapped(argument), names))
                    .collect::<Option<Vec<_>>>()?;
                (format!("({} {})", head, arguments.join(" ")), compound)
            }
            (operator, [arguments]) if operator.starts_with('@') => {
                let elements = list_elements(arguments)?;
                let compound = elements.iter().any(|element| !is_atom(unwrapped(element)));
                let decoded = elements
                    .iter()
                    .map(|element| self.decode_inner(unwrapped(element), names))
                    .collect::<Option<Vec<_>>>()?;
                (format!("({} {})", &operator[1..], decoded.join(" ")), compound)
            }
            _ => return decode_inner(inner, names),
        };
        if !compound {
            return Some(text);
        }
        let name = format!("{}{}", self.prefix, self.order.len());
        self.defined.insert(inner.clone(), name.clone());
        self.order.push(inner.clone());
        Some(format!("(! {text} :named {name})"))
    }
}

/// `term` without its `Mk` wrapper.
fn unwrapped(term: &Term) -> &Term {
    match (term.op.as_str(), term.children.as_slice()) {
        ("Mk", [inner]) => inner,
        _ => term,
    }
}

/// An encoded leaf: a constant, a variable, a literal.
fn is_atom(inner: &Term) -> bool {
    matches!(
        inner.op.as_str(),
        "Const" | "Bool" | "Op" | "Num" | "Real" | "RatConst" | "BigNum" | "Var"
    )
}

/// Whether two encoded terms decode to the same text, without printing
/// either: the same structure down to leaves that decode alike (a literal
/// spelled `Real` on one side and `RatConst` on the other), each pair once.
pub fn decode_alike(lhs: &Term, rhs: &Term, names: &HashMap<String, String>) -> bool {
    fn walk(
        lhs: &Term,
        rhs: &Term,
        names: &HashMap<String, String>,
        seen: &mut std::collections::HashSet<(Term, Term)>,
    ) -> bool {
        let (lhs, rhs) = (unwrapped(lhs), unwrapped(rhs));
        if lhs == rhs || seen.contains(&(lhs.clone(), rhs.clone())) {
            return true;
        }
        let alike = if is_atom(lhs) || is_atom(rhs) {
            is_atom(lhs)
                && is_atom(rhs)
                && decode_inner(lhs, names).is_some()
                && decode_inner(lhs, names) == decode_inner(rhs, names)
        } else {
            match (
                (lhs.op.as_str(), lhs.children.as_slice()),
                (rhs.op.as_str(), rhs.children.as_slice()),
            ) {
                ((a, [la]), (b, [lb])) if a == b && a.starts_with('@') => {
                    match (list_elements(la), list_elements(lb)) {
                        (Some(x), Some(y)) => {
                            x.len() == y.len()
                                && x.iter().zip(&y).all(|(p, q)| walk(p, q, names, seen))
                        }
                        _ => false,
                    }
                }
                (("App", [f, a]), ("App", [g, b])) => {
                    walk(f, g, names, seen) && walk(a, b, names, seen)
                }
                _ => false,
            }
        };
        if alike {
            seen.insert((lhs.clone(), rhs.clone()));
        }
        alike
    }
    walk(lhs, rhs, names, &mut std::collections::HashSet::new())
}

pub fn leak(string: String) -> &'static str {
    Box::leak(string.into_boxed_str())
}
