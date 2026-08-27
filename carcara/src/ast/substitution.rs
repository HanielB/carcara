//! Algorithms for creating and applying capture-avoiding substitutions over terms.

use super::{Binder, BindingList, Rc, Sort, SortedVar, Term, TermPool};
use indexmap::{IndexMap, IndexSet};
use thiserror::Error;

/// The error type for errors when constructing or applying substitutions.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum SubstitutionError {
    /// One of the mappings in the substitution was mapping a term to a term of a different sort.
    #[error("trying to substitute term '{0}' with a term of a different sort: '{1}'")]
    DifferentSorts(Rc<Term>, Rc<Term>),
}

type SubstitutionResult<T> = Result<T, SubstitutionError>;

/// Represents a capture-avoiding substitution over terms.
///
/// A substitution is a mapping from variables to terms, that, when applied to a term, will replace
/// all instances of these variables to the terms that they map to. For example, applying the
/// substitution `{x -> (+ y 3)}` to the term `(and (> x 0) (= x z))` would result in the term
/// `(and (> (+ y 3) 0) (= (+ y 3) z))`.
///
/// Note that naively applying a substitution to a term that contains binders may result in what's
/// called a capture: when a variable that was supposed to be free is captured as the result of
/// applying the substitution to the binder term. Consider applying the substitution `{x -> y}` to
/// the term `(forall ((y Int)) (= x y))`. Doing so naively would result in the term
/// `(forall ((y Int)) (= y y))`, which has a different meaning than the original term, because the
/// `x` variable was captured by the binder when it was renamed. To prevent this, these
/// substitutions are also capture-avoiding. This is done by renaming the binder variable when
/// necessary before applying the substitution. In the earlier example, the resulting term would
/// actually be `(forall ((y' Int)) (= y y'))`.
#[derive(Debug, Clone)]
pub struct Substitution {
    /// The substitution's mappings.
    map: IndexMap<Rc<Term>, Rc<Term>>,

    /// Whether the substitution should be applied in a capture-avoiding way or not. By default this
    /// will be true but can be set to false.
    avoid_capture: bool,

    /// The variables that should be renamed to preserve capture-avoidance, if they are bound by a
    /// binder term.
    should_be_renamed: Option<IndexSet<String>>,

    /// The names occurring free in the substitution's range. A binder that binds one of these
    /// genuinely has to be renamed; a binder that merely shadows a substituted variable does not
    /// (see [`Substitution::apply_to_binder`]).
    captured: Option<IndexSet<String>>,

    /// The memoization cache for `apply`. Each entry records the generation at which it was
    /// stored, which is what allows its validity to be decided lazily. See
    /// [`Substitution::get_cached`].
    cache: IndexMap<Rc<Term>, (Rc<Term>, u32)>,

    /// The number of mappings inserted into this substitution so far. This is used as a logical
    /// clock: it is incremented by every `insert`, and identifies the version of the substitution
    /// that a cache entry was computed against.
    generation: u32,

    /// For each variable that was ever inserted into this substitution, the generation at which
    /// the latest such insertion happened. A cache entry stored at generation `g` is invalidated
    /// exactly by the variables whose recorded generation is greater than `g`.
    invalidated_at: IndexMap<Rc<Term>, u32>,
}

impl Substitution {
    fn compare_sort_rare_list(lhs: &Sort, rhs: &Sort) -> bool {
        match (lhs, rhs) {
            (Sort::RareList(inner), other) => inner.as_sort().is_some_and(|s| s == other),
            (other, Sort::RareList(inner)) => inner.as_sort().is_some_and(|s| s == other),
            _ => false,
        }
    }

    /// Constructs an empty substitution.
    pub fn empty() -> Self {
        Self {
            map: IndexMap::new(),
            avoid_capture: true,
            should_be_renamed: None,
            captured: None,
            cache: IndexMap::new(),
            generation: 0,
            invalidated_at: IndexMap::new(),
        }
    }

    /// Constructs a singleton substitution mapping `x` to `t`. This returns an error if the sorts
    /// of the given terms are not the same.
    pub fn single(pool: &mut dyn TermPool, x: Rc<Term>, t: Rc<Term>) -> SubstitutionResult<Self> {
        let mut this = Self::empty();
        this.insert(pool, x, t)?;
        Ok(this)
    }

    /// Constructs a new substitution from an arbitrary mapping of terms to other terms. This
    /// returns an error if any term is mapped to a term of a different sort.
    pub fn new(
        pool: &mut dyn TermPool,
        map: IndexMap<Rc<Term>, Rc<Term>>,
    ) -> SubstitutionResult<Self> {
        for (k, v) in &map {
            let k_sort = pool.sort(k).as_sort().unwrap().clone();
            let v_sort = pool.sort(v).as_sort().unwrap().clone();
            if k_sort != v_sort
                && !k_sort.is_polymorphic()
                && !v_sort.is_polymorphic()
                && !Self::compare_sort_rare_list(&k_sort, &v_sort)
            {
                return Err(SubstitutionError::DifferentSorts(k.clone(), v.clone()));
            }
        }

        Ok(Self {
            map,
            avoid_capture: true,
            should_be_renamed: None,
            captured: None,
            cache: IndexMap::new(),
            generation: 0,
            invalidated_at: IndexMap::new(),
        })
    }

    /// Returns `true` if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Extends the substitution by adding a new mapping from `x` to `t`. This returns an error if
    /// the sorts of the given terms are not the same.
    pub(crate) fn insert(
        &mut self,
        pool: &mut dyn TermPool,
        x: Rc<Term>,
        t: Rc<Term>,
    ) -> SubstitutionResult<()> {
        let x_sort = pool.sort(&x).as_sort().unwrap().clone();
        let t_sort = pool.sort(&t).as_sort().unwrap().clone();
        if x_sort != t_sort
            && !x_sort.is_polymorphic()
            && !t_sort.is_polymorphic()
            && !Self::compare_sort_rare_list(&x_sort, &t_sort)
        {
            return Err(SubstitutionError::DifferentSorts(x, t));
        }

        // Introducing new mappings may invalidate previously defined cache entries. In particular,
        // if a term contains `x` as a free variable, the result of applying the substitution to it
        // may be different after adding the `x -> t` mapping. Instead of scanning the cache here
        // and dropping those entries eagerly, we only record that `x` was inserted at this
        // generation, and let `get_cached` decide the validity of an entry when (and only when) it
        // is actually consulted. This matters when a substitution is extended right after being
        // built from a larger one, as when composing the cumulative substitutions of nested
        // contexts: the eager scan would be paid for entries that are never looked up again.
        self.generation += 1;
        self.invalidated_at.insert(x.clone(), self.generation);

        if let Some(should_be_renamed) = &mut self.should_be_renamed {
            if x != t {
                let free_vars: Vec<String> = pool
                    .free_vars(&t)
                    .into_iter()
                    .map(|v| v.as_var().unwrap().to_owned())
                    .collect();
                should_be_renamed.extend(free_vars.iter().cloned());
                if let Some(captured) = &mut self.captured {
                    captured.extend(free_vars);
                }
                if let Some(var) = x.as_var() {
                    should_be_renamed.insert(var.to_owned());
                }
            }
        }

        self.map.insert(x, t);
        Ok(())
    }

    /// Looks up `term` in the memoization cache, validating the entry that is found.
    ///
    /// Since `insert` does not invalidate cache entries eagerly, an entry may have been computed
    /// against an older version of the substitution, in which case it can only be used if none of
    /// the mappings inserted since then can change the result. An entry stored at generation `g`
    /// is invalidated by a variable `w` if `w` was (re-)inserted after `g`, and `w` occurs free in
    /// the key. This is precisely the condition under which the eager invalidation would have
    /// dropped the entry, so both schemes use exactly the same entries.
    ///
    /// Entries that are found to still be valid are promoted to the current generation, so that
    /// they are only validated once per version of the substitution.
    fn get_cached(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Option<Rc<Term>> {
        let (value, entry_generation) = self.cache.get(term)?;

        // Fast path: the entry was stored after the latest insertion, so nothing can have
        // invalidated it. This is the common case, since a substitution is usually fully built
        // before being applied.
        if *entry_generation >= self.generation {
            return Some(value.clone());
        }

        let (value, entry_generation) = (value.clone(), *entry_generation);
        let free_vars = pool.free_vars(term);

        // We look for an invalidating variable from whichever side is smaller: the free variables
        // of the key, or the variables inserted into this substitution
        let is_invalidated = if free_vars.len() <= self.invalidated_at.len() {
            free_vars.iter().any(|w| {
                self.invalidated_at
                    .get(w)
                    .is_some_and(|g| *g > entry_generation)
            })
        } else {
            self.invalidated_at
                .iter()
                .any(|(w, g)| *g > entry_generation && free_vars.contains(w))
        };

        if is_invalidated {
            self.cache.swap_remove(term);
            None
        } else {
            self.cache
                .insert(term.clone(), (value.clone(), self.generation));
            Some(value)
        }
    }

    /// Removes a mapping from the substitution.
    ///
    /// This will clear `self.should_be_renamed`, such that it might need to be recomputed later.
    /// Therefore, you should avoid using this method if possible.
    pub(super) fn remove(&mut self, x: &Rc<Term>) {
        let was_present = self.map.swap_remove(x).is_some();
        if was_present {
            self.should_be_renamed = None;
            self.captured = None;
        }
    }

    /// This substitution with the given variables removed from its domain: what applies under a
    /// binder that binds them. It gets a fresh cache, since the same subterm can come out
    /// differently on the two sides of that binder.
    fn without(&self, vars: &[Rc<Term>]) -> Self {
        let map = self
            .map
            .iter()
            .filter(|(x, _)| !vars.contains(x))
            .map(|(x, t)| (x.clone(), t.clone()))
            .collect();
        Self {
            map,
            avoid_capture: self.avoid_capture,
            should_be_renamed: self.should_be_renamed.clone(),
            captured: self.captured.clone(),
            cache: IndexMap::new(),
            generation: 0,
            invalidated_at: IndexMap::new(),
        }
    }

    pub fn set_capture_avoidance(&mut self, avoid_capture: bool) {
        self.avoid_capture = avoid_capture;
    }

    /// Computes which binder variables will need to be renamed, and stores the result in
    /// `self.should_be_renamed`.
    fn compute_should_be_renamed(&mut self, pool: &mut dyn TermPool) {
        if self.should_be_renamed.is_some() {
            return;
        }

        // To avoid captures when applying the substitution, we may need to rename some of the
        // variables that are bound in the term.
        //
        // For example, consider the substitution `{x -> y}`. If `x` and `y` are both variables,
        // when applying the substitution to `(forall ((y Int)) (= x y))`, we would need to rename
        // `y` to avoid a capture, because the substitution would change the semantics of the term.
        // The resulting term should then be `(forall ((y' Int)) (= y y'))`.
        //
        // More precisely, for a substitution `{x -> t}`, if a bound variable `y` satisfies one the
        // following conditions, it must be renamed:
        //
        // - `y` = `x`
        // - `y` appears in the free variables of `t`
        //
        // See https://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions for
        // more details.
        let mut should_be_renamed = IndexSet::new();
        let mut captured = IndexSet::new();
        for (x, t) in &self.map {
            if x == t {
                continue; // We ignore reflexive substitutions
            }
            let free_vars = pool
                .free_vars(t)
                .into_iter()
                .map(|v| v.as_var().unwrap().to_owned());
            captured.extend(free_vars);
            if let Some(var) = x.as_var() {
                should_be_renamed.insert(var.to_owned());
            }
        }
        should_be_renamed.extend(captured.iter().cloned());
        self.should_be_renamed = Some(should_be_renamed);
        self.captured = Some(captured);
    }

    /// Applies the substitution to `term`, and returns the result as a new term.
    pub fn apply(&mut self, pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
        macro_rules! apply_to_sequence {
            ($sequence:expr) => {
                $sequence
                    .iter()
                    .map(|a| self.apply(pool, a))
                    .collect::<Vec<_>>()
            };
        }

        if let Some(t) = self.get_cached(pool, term) {
            return t;
        }
        if let Some(t) = self.map.get(term) {
            return t.clone();
        }

        let result = match term.as_ref() {
            Term::App(func, args) => {
                let new_args = apply_to_sequence!(args);
                let new_func = self.apply(pool, func);
                pool.add(Term::App(new_func, new_args))
            }
            Term::Op(op, args) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Op(*op, new_args))
            }
            Term::Binder(binder, binding_list, inner) => {
                self.apply_to_binder(pool, term, *binder, binding_list.as_ref(), inner)
            }
            Term::Let(binding_list, inner) => {
                // Renaming reads `should_be_renamed`, which only `apply_to_binder` computed
                if self.avoid_capture {
                    self.compute_should_be_renamed(pool);
                }

                // As in `apply_to_binder`: a `let` that merely shadows substituted variables
                // needs no renaming, only the mappings dropped while descending into its body.
                // Its bound *values* live in the enclosing scope, so they keep the full mapping
                if self.avoid_capture {
                    let captures = binding_list
                        .iter()
                        .any(|(name, _)| self.captured.as_ref().unwrap().contains(name));
                    let shadowed: Vec<Rc<Term>> = binding_list
                        .iter()
                        .map(|(name, value)| {
                            let sort = pool.sort(value);
                            pool.add(Term::new_var(name.clone(), sort))
                        })
                        .filter(|var| self.map.contains_key(var))
                        .collect();
                    if !captures && !shadowed.is_empty() {
                        let new_bindings = BindingList(
                            binding_list
                                .iter()
                                .map(|(var, value)| (var.clone(), self.apply(pool, value)))
                                .collect(),
                        );
                        let mut under = self.without(&shadowed);
                        let new_term = under.apply(pool, inner);
                        return pool.add(Term::Let(new_bindings, new_term));
                    }
                }

                let (new_bindings, mut renaming) =
                    self.rename_binding_list(pool, binding_list, true);
                // A `let`'s bound values live in the *enclosing* scope, so the substitution
                // applies to them as it does to any other subterm
                let new_bindings = BindingList(
                    new_bindings
                        .0
                        .iter()
                        .map(|(var, value)| (var.clone(), self.apply(pool, value)))
                        .collect(),
                );
                let new_term = if renaming.is_empty() {
                    self.apply(pool, inner)
                } else {
                    // If there are variables that would be captured by the substitution, we need
                    // to rename them first
                    let renamed = renaming.apply(pool, inner);
                    self.apply(pool, &renamed)
                };
                pool.add(Term::Let(new_bindings, new_term))
            }
            Term::Match(term, patterns) => {
                let new_term = self.apply(pool, term);
                let new_patterns = patterns
                    .iter()
                    .map(|(binding_list, pattern, res)| {
                        if self.avoid_capture {
                            self.compute_should_be_renamed(pool);
                        }
                        let (new_bindings, mut renaming) =
                            self.rename_binding_list(pool, binding_list, true);
                        let new_pattern = if renaming.is_empty() {
                            pattern.clone()
                        } else {
                            renaming.apply(pool, pattern)
                        };
                        let new_res = if renaming.is_empty() {
                            self.apply(pool, res)
                        } else {
                            let renamed = renaming.apply(pool, res);
                            self.apply(pool, &renamed)
                        };
                        (new_bindings, new_pattern, new_res)
                    })
                    .collect();
                pool.add(Term::Match(new_term, new_patterns))
            }
            Term::Const(_) | Term::Var(..) => term.clone(),
            Term::ParamOp { op, op_args, args } => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args: new_args,
                })
            }
            Term::Sort(Sort::Atom(sort, args)) => {
                let new_args = apply_to_sequence!(args).into_boxed_slice();
                pool.add(Term::Sort(Sort::Atom(sort.clone(), new_args)))
            }
            Term::Sort(Sort::Function(args)) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Sort(Sort::Function(new_args)))
            }
            Term::Sort(Sort::Array(x, y)) => {
                let [x, y] = [x, y].map(|s| self.apply(pool, s));
                pool.add(Term::Sort(Sort::Array(x, y)))
            }
            Term::Sort(Sort::Datatype(sort, args)) => {
                let new_args = apply_to_sequence!(args);
                pool.add(Term::Sort(Sort::Datatype(sort.clone(), new_args)))
            }
            Term::Sort(Sort::ParamSort(vars, sort)) => {
                let new_sort = self.apply(pool, sort);
                let mut new_vars = Vec::<Rc<Term>>::new();
                for var in vars {
                    if !self.map.contains_key(var) {
                        new_vars.push(var.clone());
                    }
                }
                if new_vars.is_empty() {
                    new_sort
                } else {
                    pool.add(Term::Sort(Sort::ParamSort(new_vars, new_sort)))
                }
            }
            Term::Sort(_) => term.clone(),
        };

        // Since frequently a term will have more than one identical subterms, we insert the
        // calculated substitution in the cache hash map so it may be reused later. This means we
        // don't re-visit already seen terms, so this method traverses the term as a DAG, not as a
        // tree
        self.cache
            .insert(term.clone(), (result.clone(), self.generation));
        result
    }

    fn can_skip_instead_of_renaming(&self, binding_list: &[SortedVar]) -> bool {
        // Note: this method assumes that `binding_list` is a "sort" binding list. "Value" lists add
        // some complications that are currently not supported. For example, the variable in the
        // domain of the substitution might be used in the value of a binding in the binding list,
        // and the behavior of the substitution may change if this use is before or after the
        // variable is bound in the list.

        if self.map.len() != 1 {
            return false;
        }
        let x = self.map.iter().next().unwrap().0.as_var().unwrap();

        let mut should_be_renamed = binding_list
            .iter()
            .filter(|&var| self.should_be_renamed.as_ref().unwrap().contains(&var.0));

        // In order for skipping to be possible, there should be only one variable in the binding
        // list that would be renamed, and that variable must be the variable in the domain of the
        // substitution
        should_be_renamed.next().map(|(var, _)| var.as_ref()) == Some(x)
            && should_be_renamed.next().is_none()
    }

    /// Applies the substitution to a binder term, renaming any bound variables as needed.
    fn apply_to_binder(
        &mut self,
        pool: &mut dyn TermPool,
        original_term: &Rc<Term>,
        binder: Binder,
        binding_list: &[SortedVar],
        inner: &Rc<Term>,
    ) -> Rc<Term> {
        if self.avoid_capture {
            self.compute_should_be_renamed(pool);
        }

        // In some situations, if the substitution has only one mapping (say, `x -> t`) we can skip
        // applying the substitution to a binder term altogether. This can happen if the variable
        // `x` appears in the binding list, while none of the free variables of `t` appear.
        // Normally, we would rename `x` to avoid shadowing before applying the substitution, but we
        // could instead remove the relevant mapping from the substitution, and add it back after
        // applying the substitution to the binder term. In this case, as there is only one mapping,
        // we can just skip the substitution entirely, which is way faster in some cases. In
        // particular, the skolemization rules require this optimization to have acceptable
        // performance.
        //
        // TODO guarding this with "avoid_capture" as well to guarantee I'm not breaking anything
        // (i.e., by not computing "should_be_renamed" maybe this will be applied inadvertently)
        if self.avoid_capture && self.can_skip_instead_of_renaming(binding_list) {
            return original_term.clone();
        }

        // The same reasoning, for any number of mappings: a binder that merely *shadows*
        // substituted variables needs no renaming, since the substitution does not reach the
        // occurrences it binds. Dropping those mappings while descending returns the term the
        // renaming would only have produced an α-variant of — which matters wherever the result
        // has to keep matching a term nothing renamed, as in a proof written by a solver or
        // replayed by the elaborator. A binder that binds a name occurring free in the range is a
        // genuine capture and still has to be renamed.
        if self.avoid_capture {
            let shadowed: Vec<Rc<Term>> = binding_list
                .iter()
                .filter(|(name, _)| !self.captured.as_ref().unwrap().contains(name))
                .map(|(name, sort)| pool.add(Term::new_var(name.clone(), sort.clone())))
                .filter(|var| self.map.contains_key(var))
                .collect();
            let captures = binding_list
                .iter()
                .any(|(name, _)| self.captured.as_ref().unwrap().contains(name));
            if !captures && !shadowed.is_empty() {
                let mut under = self.without(&shadowed);
                let new_term = under.apply(pool, inner);
                return pool.add(Term::Binder(
                    binder,
                    BindingList(binding_list.to_vec()),
                    new_term,
                ));
            }
        }

        let (new_bindings, mut renaming) = self.rename_binding_list(pool, binding_list, false);
        let new_term = if renaming.is_empty() {
            self.apply(pool, inner)
        } else {
            // If there are variables that would be captured by the substitution, we need
            // to rename them first
            let renamed = renaming.apply(pool, inner);
            self.apply(pool, &renamed)
        };
        pool.add(Term::Binder(binder, new_bindings, new_term))
    }

    /// Creates a new substitution that renames all variables in the binding list that may be
    /// captured by this substitution to a new, arbitrary name. Returns that substitution, and the
    /// new binding list, with the bindings renamed. If no variable needs to be renamed, this just
    /// returns a clone of the binding list and an empty substitution. The name chosen when renaming
    /// a variable is the old name with `'` appended. If the binding list is a "value" list, like in
    /// a `let` or `lambda` term, `is_value_list` should be true.
    fn rename_binding_list(
        &mut self,
        pool: &mut dyn TermPool,
        binding_list: &[SortedVar],
        is_value_list: bool,
    ) -> (BindingList, Self) {
        if !self.avoid_capture {
            return (BindingList(binding_list.to_vec()), Self::empty());
        }
        let mut new_substitution = Self::empty();
        let mut new_vars = IndexSet::new();
        let new_binding_list = binding_list
            .iter()
            .map(|(var, value)| {
                // If the binding list is a "sort" binding list, then `value` will be the variable's
                // sort. Otherwise, we need to get the sort of `value`
                let sort = if is_value_list {
                    pool.sort(value)
                } else {
                    value.clone()
                };

                let mut changed = false;
                let mut new_var = var.clone();

                // We keep adding `'`s to the variable name as long as it is necessary
                loop {
                    if !new_vars.contains(&new_var)
                        && !self.should_be_renamed.as_ref().unwrap().contains(&new_var)
                    {
                        break;
                    }
                    new_var.push_str("_renamed");
                    changed = true;
                }

                if changed {
                    // If the variable was renamed, we have to add this renaming to the resulting
                    // substitution
                    let old = pool.add((var.clone(), sort.clone()).into());
                    let new = pool.add((new_var.clone(), sort).into());

                    // We can safely unwrap here because `old` and `new` are guaranteed to have the
                    // same sort
                    new_substitution.insert(pool, old, new).unwrap();
                    new_vars.insert(new_var.clone());
                }

                // If the binding list is a "value" list, we need to apply the current substitution
                // to each variable's value
                let new_value = if is_value_list {
                    new_substitution.apply(pool, value)
                } else {
                    value.clone()
                };
                (new_var, new_value)
            })
            .collect();
        (BindingList(new_binding_list), new_substitution)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::PrimitivePool, parser::*};

    fn run_test(definitions: &str, original: &str, x: &str, t: &str, result: &str) {
        let mut pool = PrimitivePool::new();
        let mut parser = Parser::new(&mut pool, Config::new(), definitions).unwrap();
        parser.parse_problem().unwrap();

        let [original, x, t, result] = [original, x, t, result].map(|s| {
            parser.reset(s).unwrap();
            parser.parse_term().unwrap()
        });

        let mut map = IndexMap::new();
        map.insert(x, t);

        let got = Substitution::new(&mut pool, map)
            .unwrap()
            .apply(&mut pool, &original);

        assert_eq!(&result, &got);
    }

    macro_rules! run_tests {
        (
            definitions = $defs:literal,
            $($original:literal [$x:tt -> $t:tt] => $result:literal,)*
        ) => {{
            let definitions = $defs;
            $(run_test(definitions, $original, stringify!($x), stringify!($t), $result);)*
        }};
    }

    #[test]
    fn test_substitutions() {
        run_tests! {
            definitions = "
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "x" [x -> x] => "x",
            // A `let`'s bound values live in the enclosing scope, so they are substituted too
            "(let ((z (+ x 1))) (> z x))" [x -> y] => "(let ((z (+ y 1))) (> z y))",
            "(let ((z (+ x 1))) (> z 0))" [x -> y] => "(let ((z (+ y 1))) (> z 0))",
            "(+ 2 x)" [x -> y] => "(+ 2 y)",
            "(+ 2 x)" [x -> (+ 3 4 5)] => "(+ 2 (+ 3 4 5))",
            "(forall ((p Bool)) (and p q))" [q -> r] => "(forall ((p Bool)) (and p r))",

            // Simple renaming
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed 0))",

            // Renaming may be skipped
            "(forall ((x Int)) (> x 0))" [x -> y] => "(forall ((x Int)) (> x 0))",

            // Capture-avoidance
            "(forall ((y Int)) (> y x))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed y))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> y] =>
                "(forall ((x_renamed Int) (y_renamed Int)) (= x_renamed y_renamed))",
            "(forall ((x Int) (y Int)) (= x y))" [x -> x] => "(forall ((x Int) (y Int)) (= x y))",
            "(forall ((y Int)) (> y x))" [x -> (+ y 0)] =>
                "(forall ((y_renamed Int)) (> y_renamed (+ y 0)))",

            "(forall ((y Int) (y_renamed Int)) (= y y_renamed))" [x -> y] =>
                "(forall ((y_renamed Int) (y_renamed_renamed Int)) (= y_renamed y_renamed_renamed))",
            "(forall ((y Int) (y_renamed Int) (y_renamed_renamed Int))
                (= y y_renamed y_renamed_renamed))" [x -> y]
            => "(forall ((y_renamed Int) (y_renamed_renamed Int) (y_renamed_renamed_renamed Int))
                    (= y_renamed y_renamed_renamed y_renamed_renamed_renamed))",

            // The capture-avoidance may disambiguate repeated bindings
            "(forall ((y Int) (y_renamed Int) (y_renamed Int)) (= y y_renamed y_renamed))" [x -> y] =>
                "(forall ((y_renamed Int) (y_renamed_renamed Int) (y_renamed_renamed_renamed Int))
                    (= y_renamed y_renamed_renamed_renamed y_renamed_renamed_renamed))",

            // In theory, since x does not appear in this term, renaming y to y_renamed is unnecessary
            "(forall ((y Int)) (> y 0))" [x -> y] => "(forall ((y_renamed Int)) (> y_renamed 0))",

            // Name collision with variables with different types
            "(forall ((y Bool)) (and y (> x 0)))" [x -> y] =>
                "(forall ((y_renamed Bool)) (and y_renamed (> y 0)))",

            // TODO: Add tests for `choice`, `let`, and `lambda` terms
        }
    }
}
