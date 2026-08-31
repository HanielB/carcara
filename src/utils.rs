use crate::ast::{Binder, BindingList, Rc, Sort, Term};
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

/// An iterator extension trait that provides the [`dedup`](DedupIterator::dedup) method.
///
/// This trait is implemented for all iterators.
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

/// A wrapper around a value that caches its hash, so that the wrapped value only needs to be
/// hashed once.
///
/// The hash is computed when the `HashCache` is created, and after that hashing will only write
/// that cached hash instead of hashing the wrapped value. This is useful when you need to hash the
/// same value multiple times, for example when it is used as a key in a [`HashMapStack`].
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
    /// Creates a new `HashCache`, computing and storing the hash of `value`.
    pub fn new(value: T) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::default();
        value.hash(&mut hasher);
        Self { hash: hasher.finish(), value }
    }

    /// Consumes the `HashCache`, returning the wrapped value.
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
    /// Creates an empty `HashMapStack`, containing a single empty scope.
    pub fn new() -> Self {
        Self {
            map: IndexMap::new(),
            scopes: vec![Vec::new()],
        }
    }

    /// Returns the number of scopes in the stack.
    pub fn height(&self) -> usize {
        self.scopes.len()
    }

    /// Returns `true` if every scope in the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.map.values().all(Vec::is_empty)
    }

    /// Clears the `HashMapStack`, removing all entries and popping all scopes except the base
    /// scope.
    #[allow(dead_code)]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Pushes a new, empty scope onto the stack.
    pub fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    /// Pops the topmost scope from the stack.
    ///
    /// # Panics
    ///
    /// Panics if the stack contains only one scope, since the last scope cannot be popped.
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
    /// Searches for the value bound to `key`, starting from the topmost scope.
    ///
    /// Returns the value from the first scope found that binds `key`, or `None` if no scope does.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.get(key)?.last().map(|(_, v)| v)
    }

    /// Like [`get`](HashMapStack::get), but also returns the depth of the scope in which the key
    /// was found, where `0` is the bottommost scope.
    pub fn get_with_depth<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.get(key)?.last().map(|(depth, v)| (*depth, v))
    }

    /// Inserts a key-value pair into the topmost scope.
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

impl<K: Eq + Hash, V> std::iter::Extend<(K, V)> for HashMapStack<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

/// A multiset (or bag): a collection that counts how many times each element occurs.
#[derive(Debug, Clone)]
pub struct MultiSet<T>(pub IndexMap<T, usize>);

impl<T> Default for MultiSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MultiSet<T> {
    /// Creates a new, empty `MultiSet`.
    pub fn new() -> Self {
        MultiSet(IndexMap::new())
    }

    /// Returns the number of distinct elements in the multiset.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the multiset is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// The result of comparing two multisets with [`MultiSet::symmetric_difference`].
pub enum MultiSetDifference<'a, T> {
    /// The two multisets contain the same elements with the same multiplicities.
    None,

    /// The element occurs fewer times in `self` than in the other multiset.
    Missing(&'a T),

    /// The element occurs more times in `self` than in the other multiset.
    Extra(&'a T),
}

impl<T: Hash + Eq> MultiSet<T> {
    /// Returns the number of times `value` occurs in the multiset, or `0` if it is not present.
    pub fn get<Q>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.get(value).copied().unwrap_or_default()
    }

    /// Returns a mutable reference to the number of times `value` occurs in the multiset, inserting
    /// an entry with count `0` if `value` is not present.
    pub fn get_mut(&mut self, value: T) -> &mut usize {
        self.0.entry(value).or_default()
    }

    /// Returns the number of times `value` occurs in the multiset, or `0` if it is not present.
    #[allow(dead_code)]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get(value) > 0
    }

    /// Inserts `value` into the multiset once, returning the new count for `value`.
    pub fn insert(&mut self, value: T) -> usize {
        self.insert_n(value, 1)
    }

    /// Inserts `n` copies of `value` into the multiset, returning the new count for `value`.
    pub fn insert_n(&mut self, value: T, n: usize) -> usize {
        if n == 0 {
            return self.get(&value);
        }
        let v = self.get_mut(value);
        *v += n;
        *v
    }

    /// Removes `value` from the multiset once, returning the remaining count for `value`.
    pub fn remove(&mut self, value: &T) -> usize {
        self.remove_n(value, 1)
    }

    /// Removes up to `n` copies of `value` from the multiset, returning the remaining count.
    pub fn remove_n(&mut self, value: &T, n: usize) -> usize {
        if self.get(value) <= n {
            self.0.swap_remove(value);
            0
        } else {
            let v = &mut self.0[value];
            *v -= n;
            *v
        }
    }

    /// Returns the first element that distinguishes this multiset from `other`.
    ///
    /// More precisely, this returns `MultiSetDifference::Extra` if some element occurs more times
    /// in `self` than in `other`, `MultiSetDifference::Missing` if some element occurs fewer
    /// times in `self` than in `other`, and `MultiSetDifference::None` if the two multisets are
    /// identical.
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
    /// Returns an iterator that yields each element of the multiset as many times as it occurs.
    pub fn into_iter(self) -> impl Iterator<Item = T> {
        // I use a custom `into_iter` method instead of implementing `IntoIterator` because the
        // actual iterator type I use can't be named (because of the closure), which `IntoIterator`
        // requires.
        self.0
            .into_iter()
            .flat_map(|(item, count)| std::iter::repeat_n(item, count))
    }
}

impl<T: Eq + Hash> std::iter::Extend<T> for MultiSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

/// A range type with a nice `Display` implementation, to be used in error messages.
#[derive(Debug)]
pub struct Range(Option<usize>, Option<usize>);

impl Range {
    /// Returns `true` if `n` is contained in the range.
    pub fn contains(&self, n: usize) -> bool {
        self.0.as_ref().is_none_or(|bound| n >= *bound)
            && self.1.as_ref().is_none_or(|bound| n <= *bound)
    }

    /// Returns `true` if `n` is contained in the range, for values that may not fit in a `usize`.
    pub fn contains_integer(&self, n: &Integer) -> bool {
        self.0.as_ref().is_none_or(|bound| *n >= *bound)
            && self.1.as_ref().is_none_or(|bound| *n <= *bound)
    }
}

impl fmt::Display for Range {
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

/// Provides a pretty displayable name for a type.
pub trait TypeName {
    /// The type's displayable name.
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Rc<Sort> {
    const NAME: &'static str = "sort";
}

impl TypeName for Binder {
    const NAME: &'static str = "binder";
}

impl<T> TypeName for BindingList<T> {
    const NAME: &'static str = "binding list";
}

impl TypeName for Integer {
    const NAME: &'static str = "integer";
}
