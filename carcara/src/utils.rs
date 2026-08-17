use crate::ast::{Binder, BindingList, Rc, Term};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;
use std::{
    borrow::Borrow,
    fmt,
    hash::{Hash, Hasher},
    ops,
};

/// Returns `true` if the character is a valid symbol character in the SMT-LIB and Alethe formats.
pub fn is_symbol_character(ch: char) -> bool {
    match ch {
        ch if ch.is_ascii_alphanumeric() => true,
        '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<'
        | '>' | '@' => true,

        // While `'` is not a valid symbol character according to the SMT-LIB and Alethe specs, it
        // is used by Carcara to differentiate variables renamed by capture-avoidance in
        // substitutions. To accommodate for that, we consider it a valid character when parsing.
        '\'' => true,
        _ => false,
    }
}

/// An iterator that removes duplicate elements from `iter`. This will yield the elements in
/// `iter` in order, skipping elements that have already been seen before.
pub struct Dedup<T, I> {
    seen: IndexSet<T>,
    iter: I,
}

impl<T, I> Iterator for Dedup<T, I>
where
    T: Clone + Hash + Eq,
    I: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let got = self.iter.next()?;
            let is_new = self.seen.insert(got.clone());
            if is_new {
                return Some(got);
            }
        }
    }
}

pub trait DedupIterator<T> {
    /// Creates an iterator that skips duplicate elements.
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized;
}

impl<T, I: Iterator<Item = T>> DedupIterator<T> for I {
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized,
    {
        Dedup { seen: IndexSet::new(), iter: self }
    }
}

pub struct HashCache<T> {
    hash: u64,
    value: T,
}

impl<T: PartialEq> PartialEq for HashCache<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for HashCache<T> {}

impl<T: Hash> Hash for HashCache<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<T: Eq + Hash> HashCache<T> {
    pub fn new(value: T) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::default();
        value.hash(&mut hasher);
        Self { hash: hasher.finish(), value }
    }

    pub fn unwrap(self) -> T {
        self.value
    }
}

impl<T> AsRef<T> for HashCache<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

/// A map with scoped shadowing: pushing a scope starts a new layer of bindings, and popping it
/// restores every binding the layer shadowed.
///
/// Lookups are O(1) regardless of how deep the scope stack is: every key indexes a single map
/// whose values are stacks of `(scope, value)` bindings, and a per-scope undo log records which
/// entries each scope introduced so that `pop_scope` can drop exactly those. (The previous
/// implementation kept one map per scope and searched them innermost-first, which made every
/// lookup linear in the nesting depth — pathological for proofs with deeply nested subproofs,
/// e.g. the elaboration of `let`-heavy terms.)
#[derive(Debug)]
pub struct HashMapStack<K, V> {
    /// For each key, the stack of its active bindings, tagged with the scope that introduced
    /// them. The vector may be left empty when all bindings of a key are popped.
    map: IndexMap<K, Vec<(usize, V)>>,

    /// For each scope, the indices (into `map`) of the keys it bound.
    scopes: Vec<Vec<usize>>,
}

impl<K, V> HashMapStack<K, V> {
    pub fn new() -> Self {
        Self {
            map: IndexMap::new(),
            scopes: vec![Vec::new()],
        }
    }

    pub fn height(&self) -> usize {
        self.scopes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.values().all(Vec::is_empty)
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    pub fn pop_scope(&mut self) {
        match self.scopes.len() {
            0 => unreachable!(),
            1 => panic!("trying to pop last scope in `HashMapStack`"),
            _ => {
                for index in self.scopes.pop().unwrap() {
                    self.map[index].pop();
                }
            }
        }
    }
}

impl<K: Eq + Hash, V> HashMapStack<K, V> {
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.get(key)?.last().map(|(_, v)| v)
    }

    pub fn get_with_depth<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.get(key)?.last().map(|(depth, v)| (*depth, v))
    }

    pub fn insert(&mut self, key: K, value: V) {
        let scope = self.scopes.len() - 1;
        let entry = self.map.entry(key);
        let index = entry.index();
        let bindings = entry.or_default();
        match bindings.last_mut() {
            // Inserting a key already bound in the current scope overwrites the binding
            Some((s, v)) if *s == scope => *v = value,
            _ => {
                bindings.push((scope, value));
                self.scopes.last_mut().unwrap().push(index);
            }
        }
    }
}

impl<K, V> Default for HashMapStack<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct MultiSet<T>(pub IndexMap<T, usize>);

impl<T> Default for MultiSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MultiSet<T> {
    pub fn new() -> Self {
        MultiSet(IndexMap::new())
    }
}

pub enum MultiSetDifference<'a, T> {
    None,
    Missing(&'a T),
    Extra(&'a T),
}

impl<T: Hash + Eq> MultiSet<T> {
    pub fn get(&self, value: &T) -> usize {
        self.0.get(value).copied().unwrap_or_default()
    }

    pub fn get_mut(&mut self, value: T) -> &mut usize {
        self.0.entry(value).or_default()
    }

    pub fn insert(&mut self, value: T) -> usize {
        self.insert_n(value, 1)
    }

    pub fn insert_n(&mut self, value: T, n: usize) -> usize {
        if n == 0 {
            return self.get(&value);
        }
        let v = self.get_mut(value);
        *v += n;
        *v
    }

    pub fn remove(&mut self, value: T) -> usize {
        self.remove_n(value, 1)
    }

    pub fn remove_n(&mut self, value: T, n: usize) -> usize {
        if self.get(&value) <= n {
            self.0.swap_remove(&value);
            0
        } else {
            let v = self.get_mut(value);
            *v -= n;
            *v
        }
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> MultiSetDifference<'a, T> {
        for (item, &count) in &self.0 {
            let other_count = other.get(item);
            if count > other_count {
                return MultiSetDifference::Extra(item);
            } else if count < other_count {
                return MultiSetDifference::Missing(item);
            }
        }

        for (item, &count) in &other.0 {
            let self_count = self.get(item);
            if self_count > count {
                return MultiSetDifference::Extra(item);
            } else if self_count < count {
                return MultiSetDifference::Missing(item);
            }
        }

        MultiSetDifference::None
    }
}

impl<T: Hash + Eq> PartialEq for MultiSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Hash + Eq> FromIterator<T> for MultiSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut mset = MultiSet::new();
        for i in iter {
            mset.insert(i);
        }
        mset
    }
}

impl<T: Clone> MultiSet<T> {
    pub fn into_iter(self) -> impl Iterator<Item = T> {
        // I use a custom `into_iter` method instead of implementing `IntoIterator` because the
        // actual iterator type I use can't be named (because of the closure), which `IntoIterator`
        // requires.
        self.0
            .into_iter()
            .flat_map(|(item, count)| std::iter::repeat_n(item, count))
    }
}

// TODO: Document this struct
#[derive(Debug)]
pub struct Range<T = usize>(Option<T>, Option<T>);

impl<T: std::cmp::PartialOrd> Range<T> {
    pub fn contains(&self, n: T) -> bool {
        self.0.as_ref().is_none_or(|bound| n >= *bound)
            && self.1.as_ref().is_none_or(|bound| n <= *bound)
    }
}

impl<T: fmt::Display + std::cmp::PartialEq> fmt::Display for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Range(Some(a), Some(b)) if a == b => write!(f, "{}", a),
            Range(Some(a), Some(b)) => write!(f, "between {} and {}", a, b),
            Range(Some(a), None) => write!(f, "at least {}", a),
            Range(None, Some(b)) => write!(f, "up to {}", b),
            Range(None, None) => write!(f, "any number of"),
        }
    }
}

impl From<usize> for Range {
    fn from(n: usize) -> Self {
        Self(Some(n), Some(n))
    }
}

impl From<ops::Range<usize>> for Range {
    fn from(r: ops::Range<usize>) -> Self {
        Self(Some(r.start), Some(r.end - 1))
    }
}

impl From<ops::RangeFrom<usize>> for Range {
    fn from(r: ops::RangeFrom<usize>) -> Self {
        Self(Some(r.start), None)
    }
}

impl From<ops::RangeFrom<i32>> for Range<Integer> {
    fn from(r: ops::RangeFrom<i32>) -> Self {
        Self(Some(Integer::from(r.start)), None)
    }
}

impl From<ops::RangeFull> for Range {
    fn from(_: ops::RangeFull) -> Self {
        Self(None, None)
    }
}

impl From<ops::RangeTo<usize>> for Range {
    fn from(r: ops::RangeTo<usize>) -> Self {
        Self(None, Some(r.end - 1))
    }
}

/// Provides a pretty displayable name for a type. For example, the type name for `Rc<Term>` is
/// "term".
pub trait TypeName {
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Binder {
    const NAME: &'static str = "binder";
}

impl TypeName for BindingList {
    const NAME: &'static str = "binding list";
}

impl TypeName for Integer {
    const NAME: &'static str = "integer";
}
