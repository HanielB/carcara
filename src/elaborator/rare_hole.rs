//! Elaboration of `TRUST_THEORY_REWRITE` holes through the RARE
//! post-hoc reconstruction pipeline.
use crate::rare::reconstruction::*;
use rug::{Integer, Rational};
use std::collections::HashMap;

/// Elaborates a certificate into Alethe proof steps.  Per-kind policy:
/// RARE rules, evaluation, and ACI normalization become cvc5-style
/// `TRUST_THEORY_REWRITE` holes carrying the rewrite's string name;
/// distinct elimination decomposes into Alethe's native, fully checked
/// `distinct_elim` rule; `refl`/`symm`/`trans`/`cong` glue the chain.
/// Congruence steps over the encoding spine (`Mk`, application, `Args`
/// cells) collapse into a single decoded `cong` step.
pub struct AletheElaborator {
    pub prefix: String,
    pub steps: Vec<String>,
    pub names: HashMap<String, String>,
    /// RARE rule name -> argument order, for emitting checkable
    /// `rare_rewrite` steps instead of trusted holes.
    pub rare: HashMap<String, Vec<String>>,
    /// Which uninterpreted atoms are integer-valued, for the integer
    /// tightening that relates a negated `>=` to a `<=`.
    pub sorts: ArithSorts,
}

impl AletheElaborator {
    pub fn elaborate(certificate: &Certificate, prefix: &str) -> Option<Vec<String>> {
        Self::elaborate_with_names(certificate, prefix, HashMap::new())
    }

    pub fn elaborate_with_names(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
    ) -> Option<Vec<String>> {
        Self::elaborate_full(certificate, prefix, names, HashMap::new())
    }

    pub fn elaborate_full(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
        rare: HashMap<String, Vec<String>>,
    ) -> Option<Vec<String>> {
        Self::elaborate_in(certificate, prefix, names, rare, ArithSorts::default())
    }

    pub fn elaborate_in(
        certificate: &Certificate,
        prefix: &str,
        names: HashMap<String, String>,
        rare: HashMap<String, Vec<String>>,
        sorts: ArithSorts,
    ) -> Option<Vec<String>> {
        let mut elaborator = Self {
            prefix: prefix.to_owned(),
            steps: Vec::new(),
            names,
            rare,
            sorts,
        };
        elaborator.step_for(certificate)?;
        Some(elaborator.steps)
    }

    pub fn emit(&mut self, lhs: &Term, rhs: &Term, rule: &str, tail: &str) -> Option<String> {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let decoded = |term: &Term, names: &HashMap<String, String>| {
            let text = decode_any(term, names);
            if text.is_none() {
                log::debug!("certificate term failed to decode ({rule}): {}", term.to_egglog());
            }
            text
        };
        self.steps.push(format!(
            "(step {id} (cl (= {} {})) :rule {rule}{tail})",
            decoded(lhs, &self.names)?,
            decoded(rhs, &self.names)?,
        ));
        Some(id)
    }

    /// An ACI step as Carcara's checker takes it.  The search's ACI
    /// equality is on literal sets; the checker's `aci_simp` flattens each
    /// side under its own connective, drops the identity and *adjacent*
    /// duplicates, and compares multisets, so a side with a duplicate
    /// elsewhere, or an `(or a false)` whose `a` is a nested `and`, fails
    /// it.  In order: one `aci_simp`; one `and_simplify`/`or_simplify`
    /// (the identity and every duplicate dropped, order kept); else the
    /// side flattened by `aci_simp`, its duplicates dropped by the
    /// simplification rule, and the result permuted by `aci_simp`.
    pub fn emit_aci(&mut self, lhs: &Term, rhs: &Term) -> Option<String> {
        if aci_simp_accepts(lhs, rhs) {
            return self.emit(lhs, rhs, "aci_simp", "");
        }
        if let Some(rule) = and_or_simplify_accepts(lhs, rhs) {
            return self.emit(lhs, rhs, rule, "");
        }
        if let Some(rule) = and_or_simplify_accepts(rhs, lhs) {
            let simplified = self.emit(rhs, lhs, rule, "")?;
            return self.emit(lhs, rhs, "symm", &format!(" :premises ({simplified})"));
        }
        let (Some((operator, identity)), reversed) = (match aci_connective(lhs) {
            Some(connective) => (Some(connective), false),
            None => (aci_connective(rhs), true),
        }) else {
            return self.emit(lhs, rhs, "aci_simp", "");
        };
        let (side, other) = if reversed { (rhs, lhs) } else { (lhs, rhs) };
        let rule = if operator == "@and" { "and_simplify" } else { "or_simplify" };
        let mut literals = Vec::new();
        flatten_aci(&wrapped(side), operator, identity, &mut literals);
        let mut seen = std::collections::HashSet::new();
        let deduped: Vec<Term> = literals.iter().filter(|t| seen.insert((*t).clone())).cloned().collect();
        if literals.len() < 2 || deduped.is_empty() {
            return self.emit(lhs, rhs, "aci_simp", "");
        }
        // The rebuilt sides take the original side's wrapping.
        let shaped = |term: Term| {
            if side.op == "Mk" || term.op != "Mk" {
                term
            } else {
                term.children[0].clone()
            }
        };
        let flat = shaped(encoded_app(operator, literals.clone()));
        let dedup = if deduped.len() == 1 {
            deduped[0].clone()
        } else {
            shaped(encoded_app(operator, deduped))
        };
        let mut premises = Vec::new();
        if flat != *side {
            if !aci_simp_accepts(side, &flat) {
                return self.emit(lhs, rhs, "aci_simp", "");
            }
            premises.push(self.emit(side, &flat, "aci_simp", "")?);
        }
        premises.push(self.emit(&flat, &dedup, rule, "")?);
        if wrapped(&dedup) != wrapped(other) {
            if !aci_simp_accepts(&dedup, other) {
                return self.emit(lhs, rhs, "aci_simp", "");
            }
            premises.push(self.emit(&dedup, other, "aci_simp", "")?);
        }
        let joined = if premises.len() == 1 {
            premises.pop()?
        } else {
            self.emit(side, other, "trans", &format!(" :premises ({})", premises.join(" ")))?
        };
        if reversed {
            self.emit(lhs, rhs, "symm", &format!(" :premises ({joined})"))
        } else {
            Some(joined)
        }
    }

    pub fn trusted(&mut self, lhs: &Term, rhs: &Term, name: &str) -> Option<String> {
        let tail = format!(" :args (\"TRUST_THEORY_REWRITE\" \"{name}\")");
        self.emit(lhs, rhs, "hole", &tail)
    }

    /// An encoded integer literal.
    #[allow(dead_code)]
    fn numeral(value: &Integer) -> Term {
        Term::new(
            "Mk",
            vec![Term::new("Num", vec![Term::leaf(&value.to_string())])],
        )
    }

    /// Emits a `rare_rewrite` step for `name` instantiated at `arguments`,
    /// or `None` when the database does not carry the rule with that arity.
    fn rare_step(
        &mut self,
        lhs: &Term,
        rhs: &Term,
        name: &str,
        arguments: &[&Term],
    ) -> Option<String> {
        let parameters = self.rare.get(name)?;
        if parameters.len() != arguments.len() {
            return None;
        }
        let decoded = arguments
            .iter()
            .map(|argument| decode_any(argument, &self.names))
            .collect::<Option<Vec<_>>>()?;
        let tail = format!(" :args (\"{name}\" {})", decoded.join(" "));
        self.emit(lhs, rhs, "rare_rewrite", &tail)
    }

    /// Rewrites one side of the goal into an equivalent `>=` relation, or
    /// the negation of one, emitting the steps that justify the rewrite.
    /// Returns the polarity (`false` for a negated form), the `>=` term, and
    /// the id of a step proving `(= side form)` where `form` is the `>=`
    /// term or its negation, or `None` for a shape with no route.  Every
    /// relation is routed through the RARE elimination rules of the
    /// database: `arith-elim-leq`, `arith-elim-gt`, `arith-elim-lt`, and
    /// over the integers the tightening `arith-elim-int-lt`, so the routing
    /// steps are `rare_rewrite` steps the checker recomputes.
    fn to_geq(&mut self, side: &Term) -> Option<(bool, Term, Option<String>)> {
        let (operator, arguments) = encoded_application(side)?;
        match (operator, arguments.as_slice()) {
            ("@>=", [_, _]) => Some((true, side.clone(), None)),
            // (<= a b) = (>= b a)
            ("@<=", [a, b]) => {
                let geq = encoded_app("@>=", vec![b.clone(), a.clone()]);
                let id = self.rare_step(side, &geq, "arith-elim-leq", &[a, b])?;
                Some((true, geq, Some(id)))
            }
            // (> a b) = (not (>= b a))
            ("@>", [a, b]) => {
                let geq = encoded_app("@>=", vec![b.clone(), a.clone()]);
                let negated = encoded_app("@not", vec![geq.clone()]);
                let id = self.rare_step(side, &negated, "arith-elim-gt", &[a, b])?;
                Some((false, geq, Some(id)))
            }
            // (< a b) = (not (>= a b)); over the integers the tightened
            // (>= b (+ a 1)) is the positive form the chain prefers.
            ("@<", [a, b]) => {
                let difference = poly_of(a)?.sub(&poly_of(b)?);
                if difference.is_int_valued(&self.sorts, true) {
                    let bumped =
                        encoded_app("@+", vec![a.clone(), Self::numeral(&Integer::from(1))]);
                    let geq = encoded_app("@>=", vec![b.clone(), bumped]);
                    // arith-elim-int-lt: (= (< a b) (>= b (+ a 1)))
                    let id = self.rare_step(side, &geq, "arith-elim-int-lt", &[a, b])?;
                    return Some((true, geq, Some(id)));
                }
                let geq = encoded_app("@>=", vec![a.clone(), b.clone()]);
                let negated = encoded_app("@not", vec![geq.clone()]);
                let id = self.rare_step(side, &negated, "arith-elim-lt", &[a, b])?;
                Some((false, geq, Some(id)))
            }
            ("@not", [inner]) => {
                let (inner_operator, inner_arguments) = encoded_application(inner)?;
                let [a, b] = inner_arguments.as_slice() else {
                    return None;
                };
                if inner_operator == "@>=" {
                    // (not (>= a b)) is (< a b); over the integers that
                    // tightens to (>= b (+ a 1)).  The tightening is only
                    // sound when the difference really is integer-valued.
                    let difference = poly_of(a)?.sub(&poly_of(b)?);
                    if !difference.is_int_valued(&self.sorts, true) {
                        return Some((false, inner.clone(), None));
                    }
                    let less = encoded_app("@<", vec![a.clone(), b.clone()]);
                    // arith-elim-lt: (= (< a b) (not (>= a b)))
                    let forward = self.rare_step(&less, side, "arith-elim-lt", &[a, b])?;
                    let backward =
                        self.emit(side, &less, "symm", &format!(" :premises ({forward})"))?;
                    let bumped =
                        encoded_app("@+", vec![a.clone(), Self::numeral(&Integer::from(1))]);
                    let geq = encoded_app("@>=", vec![b.clone(), bumped]);
                    // arith-elim-int-lt: (= (< a b) (>= b (+ a 1)))
                    let tightened = self.rare_step(&less, &geq, "arith-elim-int-lt", &[a, b])?;
                    let id = self.emit(
                        side,
                        &geq,
                        "trans",
                        &format!(" :premises ({backward} {tightened})"),
                    )?;
                    return Some((true, geq, Some(id)));
                }
                // The negation of a routed relation: the inner route under
                // a congruence, its polarity flipped; a double negation the
                // flip leaves behind is stripped by `not_simplify`.
                let (polarity, geq, bridge) = self.to_geq(inner)?;
                let form = if polarity {
                    geq.clone()
                } else {
                    encoded_app("@not", vec![geq.clone()])
                };
                let negated_form = encoded_app("@not", vec![form.clone()]);
                let mut id = match bridge {
                    Some(bridge) => Some(self.emit(
                        side,
                        &negated_form,
                        "cong",
                        &format!(" :premises ({bridge})"),
                    )?),
                    None => None,
                };
                if !polarity {
                    let stripped = self.emit(&negated_form, &geq, "not_simplify", "")?;
                    id = Some(match id {
                        Some(first) => self.emit(
                            side,
                            &geq,
                            "trans",
                            &format!(" :premises ({first} {stripped})"),
                        )?,
                        None => stripped,
                    });
                }
                Some((!polarity, geq, id))
            }
            _ => None,
        }
    }

    /// The integer coefficients `(c1, c2)` with `c1 * d1 = c2 * d2`, if the
    /// two differences really are proportional.  `allow_flip` admits a
    /// sign-reversing pair, which `poly_simp_rel` permits only for `=`.
    fn scaling(d1: &Poly, d2: &Poly, allow_flip: bool) -> Option<(Integer, Integer)> {
        let (p1, p2) = (d1.pivot()?, d2.pivot()?);
        if p1 == 0 || p2 == 0 {
            return None;
        }
        let mut candidates = vec![(p2.clone(), p1.clone())];
        if allow_flip {
            candidates.push((Rational::from(-p2.clone()), p1.clone()));
        }
        for (c1, c2) in candidates {
            if d1.scale(&c1) != d2.scale(&c2) {
                continue;
            }
            // Clear denominators so the premise carries integer literals.
            let scale = Integer::from(c1.denom().lcm_ref(c2.denom()));
            let (n1, n2) = (
                Rational::from(&c1 * Rational::from(scale.clone())),
                Rational::from(&c2 * Rational::from(scale)),
            );
            if !n1.is_integer() || !n2.is_integer() {
                continue;
            }
            return Some((n1.numer().clone(), n2.numer().clone()));
        }
        None
    }

    /// `(step p (cl (= (* c1 (- x1 x2)) (* c2 (- y1 y2)))) :rule poly_simp)`
    /// followed by the `poly_simp_rel` step it licenses.
    fn poly_simp_rel_pair(
        &mut self,
        lhs: &Term,
        rhs: &Term,
        x1: &Term,
        x2: &Term,
        y1: &Term,
        y2: &Term,
        allow_flip: bool,
    ) -> Option<String> {
        let d1 = poly_of(x1)?.sub(&poly_of(x2)?);
        let d2 = poly_of(y1)?.sub(&poly_of(y2)?);
        let (c1, c2) = Self::scaling(&d1, &d2, allow_flip)?;
        let scaled = |c: &Integer, a: &Term, b: &Term| {
            encoded_app(
                "@*",
                vec![
                    Self::numeral(c),
                    encoded_app("@-", vec![a.clone(), b.clone()]),
                ],
            )
        };
        let premise = self.emit(&scaled(&c1, x1, x2), &scaled(&c2, y1, y2), "poly_simp", "")?;
        self.emit(
            lhs,
            rhs,
            "poly_simp_rel",
            &format!(" :premises ({premise})"),
        )
    }

    /// Justifies an `arith_poly_norm_rel` obligation with `poly_simp_rel`.
    /// Equalities go straight through; every other relation is routed to a
    /// `>=` form, or the negation of one, on both sides first, and the
    /// routing steps are glued back on with `trans`/`symm`.  Sides that end
    /// in opposite polarities are not one `poly_simp_rel` step and keep the
    /// trusted form.
    /// A step of arbitrary clause shape under the hole's prefix; returns
    /// its id.
    fn emit_clause(&mut self, literals: &str, rule: &str, premises: &[String], args: &str) -> String {
        let id = format!("{}.{}", self.prefix, self.steps.len() + 1);
        let premises = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        let args = if args.is_empty() {
            String::new()
        } else {
            format!(" :args ({args})")
        };
        self.steps
            .push(format!("(step {id} (cl {literals}) :rule {rule}{premises}{args})"));
        id
    }

    /// The factor by which the variable part of `right`'s difference is
    /// that of `left`'s, in absolute value: the coefficient of the stated
    /// relation in each `la_generic` implication; `None` when the parts
    /// are not proportional.
    fn relation_scale(&self, left: &Term, right: &Term) -> Option<String> {
        use crate::rare::reconstruction::computation::poly_of;
        let difference = |relation: &Term| -> Option<_> {
            let (_, sides) = encoded_application(relation)?;
            let [a, b] = sides.as_slice() else {
                return None;
            };
            Some(poly_of(a)?.sub(&poly_of(b)?).without_constant())
        };
        let (p1, p2) = (difference(left)?, difference(right)?);
        let k = match (p1.leading(), p2.leading()) {
            (Some(k1), Some(k2)) if k1 != 0 => k2 / k1,
            _ => return None,
        };
        if p2.sub(&p1.scale(&k)).as_constant().is_none_or(|c| c != 0) {
            return None;
        }
        Some(k.abs().to_string())
    }

    /// `(= lhs rhs)` for two linear relations whose variable parts are
    /// proportional, each implying the other by `la_generic` (whose
    /// integer strengthening covers the tightened forms), the implications
    /// joined through the `equiv_neg` tautologies and resolution: the
    /// certificate the normalizer states its own relation steps with,
    /// here for a relation obligation the `poly_simp_rel` routing could
    /// not express, which was a trust step before.  Two negated relations
    /// are joined under `cong`.  Equalities are left to the routing: the
    /// negation of an equality is no `la_generic` literal.
    pub(crate) fn la_generic_equivalence(&mut self, lhs: &Term, rhs: &Term) -> Option<String> {
        let relation = |term: &Term| -> Option<(bool, Term)> {
            match encoded_application(term)? {
                ("@not", inner) if inner.len() == 1 => match encoded_application(&inner[0])? {
                    ("@<" | "@<=" | "@>" | "@>=", _) => Some((false, inner[0].clone())),
                    _ => None,
                },
                ("@<" | "@<=" | "@>" | "@>=", _) => Some((true, term.clone())),
                _ => None,
            }
        };
        let (left_polarity, left) = relation(lhs)?;
        let (right_polarity, right) = relation(rhs)?;
        if left_polarity != right_polarity {
            // `(= (not R1) R2)`: R1 and R2 exclude each other and cover
            // every case, each by `la_generic`, and the equivalence follows
            // through the `equiv_neg` tautologies on the negated side.
            let (negated, positive, swapped) = if left_polarity {
                (right.clone(), left.clone(), true)
            } else {
                (left.clone(), right.clone(), false)
            };
            let scale = self.relation_scale(&negated, &positive)?;
            let (r1, r2) = (
                decode_any(&negated, &self.names)?,
                decode_any(&positive, &self.names)?,
            );
            let cover = self.emit_clause(&format!("{r1} {r2}"), "la_generic", &[], &format!("{scale} 1"));
            let exclude = self.emit_clause(
                &format!("(not {r1}) (not {r2})"),
                "la_generic",
                &[],
                &format!("{scale} 1"),
            );
            let neg2 = self.emit_clause(
                &format!("(= (not {r1}) {r2}) (not {r1}) {r2}"),
                "equiv_neg2",
                &[],
                "",
            );
            let with_r2 =
                self.emit_clause(&format!("(= (not {r1}) {r2}) {r2}"), "resolution", &[neg2, cover], "");
            let neg1 = self.emit_clause(
                &format!("(= (not {r1}) {r2}) (not (not {r1})) (not {r2})"),
                "equiv_neg1",
                &[],
                "",
            );
            let with_not_r2 = self.emit_clause(
                &format!("(= (not {r1}) {r2}) (not {r2})"),
                "resolution",
                &[neg1, exclude],
                "",
            );
            let not_r1 = encoded_app("@not", vec![negated.clone()]);
            let step = self.emit(
                &not_r1,
                &positive,
                "resolution",
                &format!(" :premises ({with_r2} {with_not_r2})"),
            )?;
            return if swapped {
                self.emit(lhs, rhs, "symm", &format!(" :premises ({step})"))
            } else {
                Some(step)
            };
        }
        let scale = self.relation_scale(&left, &right)?;
        let (a, b) = (
            decode_any(&left, &self.names)?,
            decode_any(&right, &self.names)?,
        );
        let a_implies_b =
            self.emit_clause(&format!("(not {a}) {b}"), "la_generic", &[], &format!("{scale} 1"));
        let b_implies_a =
            self.emit_clause(&format!("(not {b}) {a}"), "la_generic", &[], &format!("1 {scale}"));
        let neg2 = self.emit_clause(&format!("(= {a} {b}) {a} {b}"), "equiv_neg2", &[], "");
        let with_b =
            self.emit_clause(&format!("(= {a} {b}) {b}"), "resolution", &[neg2, a_implies_b], "");
        let neg1 =
            self.emit_clause(&format!("(= {a} {b}) (not {a}) (not {b})"), "equiv_neg1", &[], "");
        let with_not_b = self.emit_clause(
            &format!("(= {a} {b}) (not {b})"),
            "resolution",
            &[neg1, b_implies_a],
            "",
        );
        let relations = self.emit(&left, &right, "resolution", &format!(" :premises ({with_b} {with_not_b})"))?;
        if left_polarity {
            Some(relations)
        } else {
            self.emit(lhs, rhs, "cong", &format!(" :premises ({relations})"))
        }
    }

    fn poly_simp_rel_chain(&mut self, lhs: &Term, rhs: &Term) -> Option<String> {
        if let (Some(("@=", left)), Some(("@=", right))) =
            (encoded_application(lhs), encoded_application(rhs))
        {
            if let ([x1, x2], [y1, y2]) = (left.as_slice(), right.as_slice()) {
                return self.poly_simp_rel_pair(lhs, rhs, x1, x2, y1, y2, true);
            }
        }

        let mark = self.steps.len();
        let chain = (|| {
            let (left_polarity, left_geq, left_bridge) = self.to_geq(lhs)?;
            let (right_polarity, right_geq, right_bridge) = self.to_geq(rhs)?;
            if left_polarity != right_polarity {
                return None;
            }
            let (_, left_arguments) = encoded_application(&left_geq)?;
            let (_, right_arguments) = encoded_application(&right_geq)?;
            let ([x1, x2], [y1, y2]) = (left_arguments.as_slice(), right_arguments.as_slice())
            else {
                return None;
            };
            let (left_form, right_form) = if left_polarity {
                (left_geq.clone(), right_geq.clone())
            } else {
                (
                    encoded_app("@not", vec![left_geq.clone()]),
                    encoded_app("@not", vec![right_geq.clone()]),
                )
            };
            // The two routes may end in the same form, in which case the
            // bridges alone join the sides; otherwise the forms are one
            // `poly_simp_rel` step apart, under a congruence when both are
            // negated.
            let mut current = if left_geq == right_geq {
                None
            } else {
                let pair =
                    self.poly_simp_rel_pair(&left_geq, &right_geq, x1, x2, y1, y2, false)?;
                Some(if left_polarity {
                    pair
                } else {
                    self.emit(
                        &left_form,
                        &right_form,
                        "cong",
                        &format!(" :premises ({pair})"),
                    )?
                })
            };
            let mut source = left_form.clone();
            // Prepend `lhs = left_form`.
            if let Some(bridge) = left_bridge {
                current = Some(match current {
                    Some(middle) => self.emit(
                        lhs,
                        &right_form,
                        "trans",
                        &format!(" :premises ({bridge} {middle})"),
                    )?,
                    None => bridge,
                });
                source = lhs.clone();
            }
            // Append `right_form = rhs`, which is the reverse of the bridge.
            if let Some(bridge) = right_bridge {
                let reversed =
                    self.emit(&right_form, rhs, "symm", &format!(" :premises ({bridge})"))?;
                current = Some(match current {
                    Some(so_far) => self.emit(
                        &source,
                        rhs,
                        "trans",
                        &format!(" :premises ({so_far} {reversed})"),
                    )?,
                    None => reversed,
                });
            }
            // Identical sides never reach here (`step_for` has a `refl`
            // case), so at least one bridge or the pair exists.
            current
        })();
        if chain.is_none() {
            // A partial chain must not be left behind for the trusted
            // fallback to be appended to.
            self.steps.truncate(mark);
        }
        chain
    }

    /// The step id proving `(= lhs rhs)` for this certificate node.
    pub fn step_for(&mut self, certificate: &Certificate) -> Option<String> {
        let step = self.step_for_inner(certificate);
        if step.is_none() && log::log_enabled!(log::Level::Debug) {
            let kind = match certificate {
                Certificate::Refl { .. } => "refl".to_owned(),
                Certificate::Rule { name, .. } => format!("rule {name}"),
                Certificate::Computational { kind, .. } => format!("computational {kind:?}"),
                Certificate::Symm { .. } => "symm".to_owned(),
                Certificate::Congruence { child_index, .. } => format!("congruence at {child_index}"),
                Certificate::Trans { .. } => "trans".to_owned(),
            };
            log::debug!(
                "no step for {kind}: {} = {}",
                certificate.lhs().to_egglog(),
                certificate.rhs().to_egglog()
            );
        }
        step
    }

    fn step_for_inner(&mut self, certificate: &Certificate) -> Option<String> {
        match certificate {
            Certificate::Refl { term } => self.emit(term, term, "refl", ""),
            Certificate::Rule { name, lhs, rhs, substitution, premises } => {
                // A rewrite the engine compiled from the RARE database
                // carries its name, so the step becomes a checkable
                // rare_rewrite with the rule's argument instantiation, and
                // a conditional rule's premise proofs as its premises;
                // engine-internal rewrites keep the trusted form.
                let premise_steps: Option<Vec<String>> =
                    premises.iter().map(|premise| self.step_for(premise)).collect();
                let premise_steps = premise_steps?;
                let premise_tail = if premise_steps.is_empty() {
                    String::new()
                } else {
                    format!(" :premises ({})", premise_steps.join(" "))
                };
                // The checker instantiates a rule with singleton elimination:
                // `(or (or x)) = (or x)` by `bool-or-flatten` becomes `x = x`
                // there and no longer matches the stated step.  A step with a
                // one-argument connective whose sides are ACI-equal is stated
                // as the checker's ACI step instead.
                if premises.is_empty()
                    && (has_singleton_connective(lhs) || has_singleton_connective(rhs))
                    && crate::rare::reconstruction::computation::aci_equal(lhs, rhs)
                {
                    return self.emit_aci(lhs, rhs);
                }
                if let Some(parameters) = self.rare.get(name).cloned() {
                    let decoded: Option<Vec<String>> = parameters
                        .iter()
                        .map(|parameter| match substitution.get(parameter) {
                            // A `:list` parameter binds a sequence of
                            // arguments: a whole chain of them, or none at
                            // all when the rule's empty-list variant is what
                            // matched.  `rare-list` is the term for such a
                            // sequence, which the checker splices back into
                            // the operator when it recomputes the rule.
                            Some(term) => decode_any(term, &self.names)
                                .or_else(|| decode_sequence(term, &self.names)),
                            None => Some("(rare-list)".to_owned()),
                        })
                        .collect();
                    if let Some(decoded) = decoded {
                        let tail =
                            format!("{premise_tail} :args (\"{name}\" {})", decoded.join(" "));
                        return self.emit(lhs, rhs, "rare_rewrite", &tail);
                    }
                }
                // An engine-internal rewrite (`gen-N`: the built-in
                // evaluations, an `ite` on a constant condition, the
                // set-form conversions, identity and duplicate removal) has
                // no RARE name; when one of the checker's computations
                // re-decides the step it is stated as that computation,
                // otherwise it stays trusted.
                for kind in crate::rare::reconstruction::computation::COMPUTATIONS {
                    if kind.apply(lhs).is_some_and(|result| result == *rhs) {
                        let computed = Certificate::Computational {
                            kind,
                            lhs: lhs.clone(),
                            rhs: rhs.clone(),
                        };
                        if let Some(step) = self.step_for_inner(&computed) {
                            return Some(step);
                        }
                    }
                }
                if crate::rare::reconstruction::computation::aci_equal(lhs, rhs) {
                    return self.emit_aci(lhs, rhs);
                }
                self.trusted(lhs, rhs, name)
            }
            Certificate::Computational { kind, lhs, rhs } => match kind {
                // A literal renormalization (`Real` to `RatConst`) decodes to
                // the same text on both sides: nothing to trust.
                _ if decode_any(lhs, &self.names) == decode_any(rhs, &self.names) => {
                    self.emit(lhs, rhs, "refl", "")
                }
                Computation::DistinctElim => self.emit(lhs, rhs, "distinct_elim", ""),
                // Each computational kind maps to the native Carcara rule
                // that re-decides it, so the elaborated step carries no
                // trust: `evaluate` constant-folds, `aci_simp` normalizes
                // and/or, `poly_simp` compares polynomial normal forms.
                // `evaluate` decides an application of interpreted
                // operators to *values*; folding an `ite` whose condition is
                // a constant is not one of those -- Carcara's evaluator
                // needs every argument to evaluate, and the branches here
                // are arbitrary terms -- but it is the first case of
                // `ite_simplify`.
                Computation::Evaluation if constant_condition_ite(lhs) => {
                    self.emit(lhs, rhs, "ite_simplify", "")
                }
                Computation::Evaluation => self.emit(lhs, rhs, "evaluate", ""),
                Computation::AciNorm => self.emit_aci(lhs, rhs),
                // A complementary pair short-circuits the connective, which
                // is what `and_simplify`/`or_simplify` decide.
                Computation::AciComplement => {
                    // The side may have lost its `Mk` wrapper to a congruence
                    // above it, so the connective is read off either form.
                    let connective = |side: &Term| {
                        let inner = if side.op == "Mk" {
                            side.children.first()?
                        } else {
                            side
                        };
                        match inner.op.as_str() {
                            "@and" => Some("and_simplify"),
                            "@or" => Some("or_simplify"),
                            _ => None,
                        }
                    };
                    let rule = connective(lhs).or_else(|| connective(rhs))?;
                    // The checker's rule reads the complementary pair off
                    // the direct arguments; the computation found it
                    // through nested `and`/`or` too.  A nested side is first
                    // flattened by `aci_simp`, and the rule applies to the
                    // flat form.
                    let (side, constant, reversed) = if connective(lhs).is_some() {
                        (lhs, rhs, false)
                    } else {
                        (rhs, lhs, true)
                    };
                    let wrapped_side = if side.op == "Mk" {
                        side.clone()
                    } else {
                        Term::new("Mk", vec![side.clone()])
                    };
                    let (operator, identity) = match encoded_application(&wrapped_side) {
                        Some(("@and", _)) => ("@and", true),
                        _ => ("@or", false),
                    };
                    let mut literals = Vec::new();
                    flatten_aci(&wrapped_side, operator, identity, &mut literals);
                    let flat = encoded_app(operator, literals);
                    let flat = if side.op == "Mk" {
                        flat
                    } else {
                        flat.children[0].clone()
                    };
                    if flat == *side || literals_of(&wrapped_side).is_some_and(|direct| direct.len() == flat_arity(&flat)) {
                        return self.emit(lhs, rhs, rule, "");
                    }
                    let flattened = self.emit(side, &flat, "aci_simp", "")?;
                    let absorbed = self.emit(&flat, constant, rule, "")?;
                    let chained = self.emit(
                        side,
                        constant,
                        "trans",
                        &format!(" :premises ({flattened} {absorbed})"),
                    )?;
                    if reversed {
                        self.emit(lhs, rhs, "symm", &format!(" :premises ({chained})"))
                    } else {
                        Some(chained)
                    }
                }
                Computation::ArithPolyNorm => self.emit(lhs, rhs, "poly_simp", ""),
                // `poly_simp_rel` states one relation as another under a
                // scaled-difference premise, but only between the same
                // operator.  Both sides are therefore first routed to a `>=`
                // form through the RARE arithmetic-elimination rules, which
                // is where the negated and integer-tightened shapes are
                // discharged.  A relation the routing does not cover keeps
                // the trusted form.
                Computation::ArithPolyNormRel => self
                    .poly_simp_rel_chain(lhs, rhs)
                    .or_else(|| self.la_generic_equivalence(lhs, rhs))
                    .or_else(|| self.trusted(lhs, rhs, "arith_poly_norm_rel")),
            },
            Certificate::Symm { lhs, rhs, proof } => {
                let premise = self.step_for(proof)?;
                let tail = format!(" :premises ({premise})");
                self.emit(lhs, rhs, "symm", &tail)
            }
            Certificate::Trans { lhs, rhs, first, second, .. } => {
                // The solver's two-element seam (`distinct` to singleton
                // `and` to the negation) is exactly Alethe's two-element
                // `distinct_elim` shape, so the pair collapses into the
                // native rule.
                if let (
                    Certificate::Computational {
                        kind: Computation::DistinctElim,
                        lhs: d,
                        ..
                    },
                    Certificate::Computational { kind: Computation::AciNorm, .. },
                ) = (first.as_ref(), second.as_ref())
                {
                    if matches!(encoded_application(d), Some(("@distinct", elements)) if elements.len() == 2)
                    {
                        return self.emit(lhs, rhs, "distinct_elim", "");
                    }
                }
                // A leg whose sides decode identically (a literal
                // renormalization) adds nothing: the other leg already
                // states the whole equality.
                let identity = |certificate: &Certificate, names: &HashMap<String, String>| {
                    decode_any(certificate.lhs(), names) == decode_any(certificate.rhs(), names)
                };
                if identity(first, &self.names) {
                    return self.step_for(second);
                }
                if identity(second, &self.names) {
                    return self.step_for(first);
                }
                let first = self.step_for(first)?;
                let second = self.step_for(second)?;
                let tail = format!(" :premises ({first} {second})");
                self.emit(lhs, rhs, "trans", &tail)
            }
            Certificate::Congruence { lhs, rhs, child, .. } => {
                // The `Mk` wrapper is invisible in Alethe: a congruence
                // through it alone states exactly the child's equality.
                if lhs.op == "Mk" && !matches!(child.as_ref(), Certificate::Congruence { .. }) {
                    return self.step_for(child);
                }
                let mut arguments = Vec::new();
                spine_arguments(certificate, false, &mut arguments)?;
                // The premises in argument order: a spine met from the far
                // side, or a chain the search composed out of order, lists
                // its legs otherwise, and `cong` reads them by position.
                // A premise's place is the unused position whose two sides it
                // states (either way round): by its left side alone, a side
                // that holds one literal twice with two different partners
                // (`(or .. (not (= x x)) .. (not (= x x)) ..)` against two
                // different `false` conjunctions) sent both premises to the
                // first occurrence.
                if let Some((_, left)) = encoded_application(lhs) {
                    let right = encoded_application(rhs).map(|(_, elements)| elements);
                    let mut used = vec![false; left.len()];
                    let mut placed: Vec<(usize, Certificate)> = Vec::new();
                    for argument in arguments.drain(..) {
                        let states = |k: usize| match &right {
                            Some(right) if k < right.len() => {
                                (left[k] == *argument.lhs() && right[k] == *argument.rhs())
                                    || (left[k] == *argument.rhs() && right[k] == *argument.lhs())
                            }
                            _ => false,
                        };
                        let position = (0..left.len())
                            .find(|&k| !used[k] && states(k))
                            .or_else(|| {
                                (0..left.len()).find(|&k| !used[k] && left[k] == *argument.lhs())
                            });
                        if let Some(k) = position {
                            used[k] = true;
                        }
                        placed.push((position.unwrap_or(usize::MAX), argument));
                    }
                    placed.sort_by_key(|(k, _)| *k);
                    arguments = placed.into_iter().map(|(_, argument)| argument).collect();
                }
                let premises = arguments
                    .iter()
                    .map(|argument| self.step_for(argument))
                    .collect::<Option<Vec<_>>>()?;
                let tail = format!(" :premises ({})", premises.join(" "));
                self.emit(lhs, rhs, "cong", &tail)
            }
        }
    }
}

/// Descend an encoded congruence spine (`Mk` wrapper, application node,
/// `Args` cells, and the transitivity chains congruence builds when several
/// arguments differ), collecting the certificates of the differing
/// arguments in argument order — one `cong` premise each.  A spine the
/// search traversed backwards arrives under `Symm` nodes (a reversed chain
/// is the reversed legs in reverse order, a reversed congruence its child
/// reversed): those are read with `flipped`, so `(= (not (not (not E))) E)
/// = (= (not E) (not (not E)))`, met from the far side, still has its two
/// argument steps.
pub fn spine_arguments(
    certificate: &Certificate,
    flipped: bool,
    out: &mut Vec<Certificate>,
) -> Option<()> {
    match certificate {
        Certificate::Refl { .. } => Some(()),
        Certificate::Symm { proof, .. } => spine_arguments(proof, !flipped, out),
        Certificate::Congruence { lhs, child_index, child, .. } => {
            match (lhs.op.as_str(), child_index) {
                // Wrapper and application layers pass straight through.
                ("Mk", 0) => spine_arguments(child, flipped, out),
                (operator, 0) if operator.starts_with('@') => spine_arguments(child, flipped, out),
                // An Args cell: index 0 is a differing element itself, index 1
                // continues along the list spine.
                ("Args", 0) => {
                    out.push(if flipped {
                        reverse(child.as_ref().clone())
                    } else {
                        child.as_ref().clone()
                    });
                    Some(())
                }
                ("Args", 1) => spine_arguments(child, flipped, out),
                _ => None,
            }
        }
        Certificate::Trans { first, second, .. } => {
            let (first, second) = if flipped { (second, first) } else { (first, second) };
            spine_arguments(first, flipped, out)?;
            spine_arguments(second, flipped, out)
        }
        _ => None,
    }
}

use std::{
    fmt::Write as _,
    io::Write as _,
    os::unix::process::ExitStatusExt,
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use crate::{
    Status,
    ast::{
        Constant, ProblemPrelude, ProofCommand, ProofNode, ProofNodeForest, Rc, StepNode,
        pool::{PrimitivePool, TermPool},
        rare_rules::Rules,
    },
    checker,
    elaborator::{Elaborator, error::ElaborationError},
    external, parser,
    rare::engine::run_egglog,
};

/// Largest e-graph, in tuples, that is worth serializing for reconstruction.
/// Applied only when a budget is in force; an untimed run captures whatever it
/// built, as before.
pub const MAX_SNAPSHOT_TUPLES: usize = 4_000_000;

/// The tags a producer prints on a rewrite hole: cvc5's
/// `ProofRule::TRUST_THEORY_REWRITE` under the rule's own name up to April
/// 2026 and under `"untranslated rewrite"` since cvc5 #12639 renamed the
/// printed form (same rule, same code path); `"MACRO_REWRITE"` and
/// `"MACRO_SR_PRED_INTRO"` on the holes cvc5 prints at
/// `--proof-granularity=rewrite`, where a hole is one call of the full
/// rewriter on a term (`(= t rw(t))`, or an equality the rewriter takes to
/// `true`) rather than one theory rewrite of one subterm; and
/// `"preprocessing"` on the holes veriT prints for a preprocessing stage
/// under `--proof-coarse-preprocessing`.
///
/// The four last ones are the trust steps cvc5 prints at rewrite
/// granularity for what it does not expand there and does at
/// `dsl-rewrite`: the arithmetic preprocessing's rewrites
/// (`THEORY_INFERENCE_ARITH`, `ARITH_STATIC_LEARN`) and subtype
/// elimination's re-typed rewrites (`MACRO_THEORY_REWRITE_RCONS_SIMPLE`,
/// `SUBTYPE_ELIMINATION`); premise-free unit equalities as well, so the
/// pipeline attempts them like any other (run rw3 left 127k, 139k and 1k
/// of them in the elaborated proofs, the ceiling on `valid`).  Theory
/// lemmas (`THEORY_LEMMA`, `DIAMONDS`) are clauses, not rewrites, and stay
/// out.
///
/// All of them are unit equalities that the producer states without
/// premises; a macro step that carries substitution premises is printed by
/// cvc5 under its rule name and is not recognized here.
pub const THEORY_REWRITE_TAGS: [&str; 9] = [
    "TRUST_THEORY_REWRITE",
    "untranslated rewrite",
    "MACRO_REWRITE",
    "MACRO_SR_PRED_INTRO",
    "preprocessing",
    "THEORY_INFERENCE_ARITH",
    "ARITH_STATIC_LEARN",
    "MACRO_THEORY_REWRITE_RCONS_SIMPLE",
    "SUBTYPE_ELIMINATION",
];

/// Whether `step` is a rewrite hole: a `hole` step with one of the
/// [`THEORY_REWRITE_TAGS`].  (The isolated child rebuilds a hole with the
/// assumptions it may use as `:premises`, so premises are not a criterion.)
pub fn is_theory_rewrite_hole(step: &StepNode) -> bool {
    step.rule == "hole"
        && matches!(
            step.args.first().map(|arg| arg.as_ref()),
            Some(crate::ast::Term::Const(Constant::String(tag)))
                if THEORY_REWRITE_TAGS.contains(&tag.as_str())
        )
}

/// Elaborates a `TRUST_THEORY_REWRITE` hole through the post-hoc pipeline:
/// the egglog engine proves the rewrite, a certificate is reconstructed from
/// its saturated e-graph, the certificate's Alethe steps are checked against
/// the RARE database, and the checked proof replaces the hole as a subproof
/// — the same insertion an external solver's proof goes through.
/// Every `TRUST_THEORY_REWRITE` hole in the forest, in encounter order.
pub fn theory_rewrite_holes(proof: &ProofNodeForest) -> Vec<(Rc<ProofNode>, StepNode)> {
    let mut holes = Vec::new();
    let mut seen: std::collections::HashSet<Rc<ProofNode>> = std::collections::HashSet::new();
    let mut todo: Vec<Rc<ProofNode>> = proof.0.iter().cloned().collect();
    while let Some(node) = todo.pop() {
        if !seen.insert(node.clone()) {
            continue;
        }
        match node.as_ref() {
            ProofNode::Step(s) => {
                if is_theory_rewrite_hole(s) {
                    holes.push((node.clone(), s.clone()));
                }
                todo.extend(s.premises.iter().cloned());
                todo.extend(s.discharge.iter().cloned());
                todo.extend(s.previous_step.iter().cloned());
            }
            ProofNode::Subproof(s) => {
                todo.push(s.last_step.clone());
                todo.extend(s.extra_steps.iter().cloned());
                todo.extend(s.outbound_premises.iter().cloned());
            }
            ProofNode::Assume { .. } => {}
        }
    }
    holes
}

/// The line separating the problem from the hole in a child process's input.
pub const HOLE_INPUT_BOUNDARY: &str = ";; --- hole ---";

/// What a child process needs to reconstruct one hole: the problem prelude,
/// then the hole's depth-0 assumptions as top-level `assume`s and the hole
/// itself citing them as premises.  That is exactly what `run_egglog` reads
/// off the in-process node, which collects the depth-0 assumptions beneath it,
/// so the child works from the same inputs the in-process worker would.
/// The problem's text for a hole's terms: the prelude and `assertions`, plus
/// a constant declaration for every variable in `terms` the problem never
/// declares.  A hole inside a subproof may mention variables the enclosing
/// anchors bind (`:args ((x Int) ...)`), and the hole's text must stand on
/// its own.
fn hole_problem_string<'a>(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    terms: impl IntoIterator<Item = &'a crate::ast::Rc<crate::ast::Term>>,
    assertions: impl IntoIterator<Item = &'a crate::ast::Rc<crate::ast::Term>>,
) -> String {
    let mut declared: std::collections::HashSet<String> = prelude
        .function_declarations
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let mut declarations = String::new();
    for term in terms {
        let free_vars = TermPool::free_vars(pool, term).into_owned();
        for var in free_vars {
            if let crate::ast::Term::Var(name, sort) = var.as_ref() {
                if declared.insert(name.clone()) {
                    let _ = writeln!(declarations, "(declare-const {var} {sort})");
                }
            }
        }
    }
    // The same shape as `external::get_problem_string`, with the extra
    // declarations before the assertions that may use them.
    let mut text = String::new();
    let _ = writeln!(text, "(set-option :produce-proofs true)");
    let _ = write!(text, "{prelude}{declarations}");
    let mut asserts = Vec::new();
    if crate::ast::printer::write_asserts(pool, prelude, &mut asserts, assertions, false).is_ok() {
        text.push_str(&String::from_utf8_lossy(&asserts));
    }
    let _ = writeln!(text, "(check-sat)\n(get-proof)\n(exit)");
    text
}

/// The rule of the steps carrying a normal form to a child: `(step nfK (cl
/// (= t t)) :rule nf-hint :args (H))` says that the subterm of structural
/// hash `H` may be replaced by `t` in the hole's goal.
pub const NF_HINT_RULE: &str = "nf-hint";

pub fn hole_input(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    node: &Rc<ProofNode>,
    step: &StepNode,
    extra_premises: &[crate::ast::Rc<crate::ast::Term>],
    hints: &[(u64, String)],
) -> Option<String> {
    let [conclusion] = step.clause.as_slice() else {
        return None;
    };
    // The hole's own assumptions, then the equalities the caller adds (earlier
    // holes already proved whose sides occur in this goal): the child takes
    // every assumption as a union, so those give it the subterm rewrites.
    let assumptions: Vec<crate::ast::Rc<crate::ast::Term>> = node
        .get_assumptions()
        .iter()
        .filter_map(|assumption| match assumption.as_ref() {
            ProofNode::Assume { term, .. } => Some(term.clone()),
            _ => None,
        })
        .chain(extra_premises.iter().cloned())
        .collect();
    let mut text = hole_problem_string(
        pool,
        prelude,
        assumptions.iter().chain(std::iter::once(conclusion)),
        [],
    );
    text.push_str(HOLE_INPUT_BOUNDARY);
    text.push('\n');
    let mut ids = Vec::new();
    for (index, term) in assumptions.iter().enumerate() {
        let id = format!("h{index}");
        // `{:#}` prints without term sharing, so the text stands on its own.
        writeln!(text, "(assume {id} {term:#})").ok()?;
        ids.push(id);
    }
    let premises = if ids.is_empty() {
        String::new()
    } else {
        format!(" :premises ({})", ids.join(" "))
    };
    for (index, (hash, normal_form)) in hints.iter().enumerate() {
        writeln!(
            text,
            "(step nf{index} (cl (= {normal_form} {normal_form})) :rule {NF_HINT_RULE} :args ({hash}))"
        )
        .ok()?;
    }
    writeln!(
        text,
        "(step {} (cl {conclusion:#}) :rule hole{premises} :args (\"TRUST_THEORY_REWRITE\"))",
        step.id
    )
    .ok()?;
    Some(text)
}

/// The input of a batch of holes for the child process: the problem text
/// with every hole's assumptions and conclusion declared, the boundary, then
/// each hole's assumptions and its `hole` step.
pub fn holes_input(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    holes: &[(&Rc<ProofNode>, &StepNode)],
) -> Option<String> {
    let mut per_hole = Vec::with_capacity(holes.len());
    for (node, step) in holes {
        let [conclusion] = step.clause.as_slice() else {
            return None;
        };
        let assumptions: Vec<crate::ast::Rc<crate::ast::Term>> = node
            .get_assumptions()
            .iter()
            .filter_map(|assumption| match assumption.as_ref() {
                ProofNode::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();
        per_hole.push((step.id.clone(), assumptions, conclusion.clone()));
    }
    let terms: Vec<&crate::ast::Rc<crate::ast::Term>> = per_hole
        .iter()
        .flat_map(|(_, assumptions, conclusion)| {
            assumptions.iter().chain(std::iter::once(conclusion))
        })
        .collect();
    let mut text = hole_problem_string(pool, prelude, terms, []);
    text.push_str(HOLE_INPUT_BOUNDARY);
    text.push('\n');
    for (hole_index, (id, assumptions, conclusion)) in per_hole.iter().enumerate() {
        let mut ids = Vec::new();
        for (index, term) in assumptions.iter().enumerate() {
            let assume_id = format!("h{hole_index}_{index}");
            writeln!(text, "(assume {assume_id} {term:#})").ok()?;
            ids.push(assume_id);
        }
        let premises = if ids.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", ids.join(" "))
        };
        writeln!(
            text,
            "(step {id} (cl {conclusion:#}) :rule hole{premises} :args (\"TRUST_THEORY_REWRITE\"))"
        )
        .ok()?;
    }
    Some(text)
}

/// The child's half of [`check_batch_in_child`]: parse the input produced by
/// [`holes_input`] and check every hole in it in one e-graph, returning each
/// hole's id with its verdict.
pub fn check_batch_from_input(
    input: &str,
    rules: parser::Source<'_>,
    options: crate::checker::RunEgglogOptions,
    sequential: bool,
    report: &mut dyn FnMut(&str, &Result<(), String>),
) -> Result<Vec<(String, Result<(), String>)>, String> {
    let boundary = format!("{HOLE_INPUT_BOUNDARY}\n");
    let (problem, proof) = input
        .split_once(&boundary)
        .ok_or_else(|| "hole input has no boundary line".to_owned())?;
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let (_, proof, database, mut pool) = parser::parse_instance(
        parser::Source::new(Path::new("<hole problem>"), problem),
        parser::Source::new(Path::new("<hole>"), proof),
        Some(rules),
        config,
    )
    .map_err(|error| format!("parsing the hole input: {error}"))?;
    let forest = ProofNodeForest::from_commands(proof.commands);
    let holes = theory_rewrite_holes(&forest);
    if holes.is_empty() {
        return Err("hole input contains no TRUST_THEORY_REWRITE hole".to_owned());
    }
    let refs: Vec<(&Rc<ProofNode>, &StepNode)> =
        holes.iter().map(|(node, step)| (node, step)).collect();
    if sequential {
        // One prepared rule database, one e-graph per hole: each verdict is
        // reported as it is reached, so a kill loses only the rest.
        let context = crate::rare::engine::RareCtx::new(&database);
        let mut verdicts = Vec::with_capacity(refs.len());
        // The per-hole budget in `options` is only cooperative, and egglog
        // cannot be interrupted inside an iteration; alone, a hole is killed
        // with its child.  Here a watchdog does the same: past the budget it
        // reports the hole as killed, in the line format the parent parses,
        // and exits, so the parent retries only the holes after it.
        let current: std::sync::Arc<std::sync::Mutex<Option<(String, Instant)>>> =
            std::sync::Arc::new(std::sync::Mutex::new(None));
        if let Some(timeout) = options.timeout {
            let current = std::sync::Arc::clone(&current);
            let grace = Duration::from_millis(500);
            std::thread::spawn(move || loop {
                std::thread::sleep(Duration::from_millis(50));
                let guard = current.lock().unwrap();
                if let Some((id, started)) = guard.as_ref() {
                    let elapsed = started.elapsed();
                    if elapsed > timeout + grace {
                        let mut out = std::io::stdout().lock();
                        let _ = writeln!(
                            out,
                            "hole {id} failed: killed after {:.1}s during egglog: hard budget exhausted",
                            elapsed.as_secs_f64()
                        );
                        let _ = out.flush();
                        std::process::exit(3);
                    }
                }
            });
        }
        for (node, step) in &refs {
            // Announced before the check so that a parent whose child dies
            // without a verdict knows which hole took it down.
            {
                let mut out = std::io::stdout().lock();
                let _ = writeln!(out, "hole {} started", step.id);
                let _ = out.flush();
            }
            *current.lock().unwrap() = Some((step.id.clone(), Instant::now()));
            let verdict = match step.clause.as_slice() {
                [conclusion] => {
                    let assumptions = node.get_assumptions();
                    let premise_clauses: Vec<&[crate::ast::Rc<crate::ast::Term>]> =
                        assumptions.iter().map(|premise| premise.clause()).collect();
                    let (result, _) = crate::rare::engine::check_hole_rewrite_with_context(
                        &mut pool,
                        &step.id,
                        conclusion.clone(),
                        &premise_clauses,
                        &context,
                        options,
                    );
                    result
                        .map(|_| ())
                        .map_err(|error| format!("egglog check: {error}"))
                }
                clause => Err(format!(
                    "setup: expected a single-literal clause, found {} literals",
                    clause.len()
                )),
            };
            *current.lock().unwrap() = None;
            report(&step.id, &verdict);
            verdicts.push((step.id.clone(), verdict));
        }
        return Ok(verdicts);
    }
    let verdicts = check_holes_batched(&mut pool, &refs, &database, options);
    let verdicts: Vec<(String, Result<(), String>)> = refs
        .iter()
        .zip(verdicts)
        .map(|((_, step), verdict)| (step.id.clone(), verdict))
        .collect();
    for (id, verdict) in &verdicts {
        report(id, verdict);
    }
    Ok(verdicts)
}

/// Checks several holes in one e-graph, in this process.  See
/// [`crate::rare::engine::check_hole_rewrites_batched`].
pub fn check_holes_batched(
    pool: &mut dyn TermPool,
    holes: &[(&Rc<ProofNode>, &StepNode)],
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Vec<Result<(), String>> {
    let mut goals = Vec::with_capacity(holes.len());
    for (node, step) in holes {
        let [conclusion] = step.clause.as_slice() else {
            // Keep the positions aligned: an ill-formed hole gets a goal that
            // fails translation with a clear message.
            goals.push(crate::rare::engine::BatchGoal {
                label: step.id.clone(),
                conclusion: step.clause.first().cloned().unwrap_or_else(|| {
                    pool.add(crate::ast::Term::Op(crate::ast::Operator::False, vec![]))
                }),
                premise_clauses: Vec::new(),
            });
            continue;
        };
        let premise_clauses = node
            .get_assumptions()
            .iter()
            .map(|premise| premise.clause().to_vec())
            .collect();
        goals.push(crate::rare::engine::BatchGoal {
            label: step.id.clone(),
            conclusion: conclusion.clone(),
            premise_clauses,
        });
    }
    let context = crate::rare::engine::RareCtx::new(rules);
    crate::rare::engine::check_hole_rewrites_batched(pool, &goals, &context, options)
        .into_iter()
        .map(|verdict| verdict.map_err(|error| format!("egglog check: {error}")))
        .collect()
}

/// The child's half of [`reconstruct_in_child`]: parse the input produced by
/// [`hole_input`], find the hole, reconstruct it.
pub fn reconstruct_from_input(
    input: &str,
    rules: parser::Source<'_>,
    options: crate::checker::RunEgglogOptions,
    check_only: bool,
    export_normal_forms: bool,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let boundary = format!("{HOLE_INPUT_BOUNDARY}\n");
    let (problem, proof) = input
        .split_once(&boundary)
        .ok_or_else(|| "hole input has no boundary line".to_owned())?;
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let (_, proof, database, mut pool) = parser::parse_instance(
        parser::Source::new(Path::new("<hole problem>"), problem),
        parser::Source::new(Path::new("<hole>"), proof),
        Some(rules),
        config,
    )
    .map_err(|error| format!("parsing the hole input: {error}"))?;
    let forest = ProofNodeForest::from_commands(proof.commands);
    let (node, step) = theory_rewrite_holes(&forest)
        .into_iter()
        .next()
        .ok_or_else(|| "hole input contains no TRUST_THEORY_REWRITE hole".to_owned())?;
    // The worker's goals run in fresh processes spawned from its input.
    let options = if options.fresh_fallback && options.worker.is_none() {
        let worker: &'static WorkerInput = Box::leak(Box::new(WorkerInput {
            text: input.to_owned(),
            hole_id: step.id.clone(),
        }));
        crate::checker::RunEgglogOptions {
            worker: Some(worker),
            ..options
        }
    } else {
        options
    };
    if check_only {
        // The normal forms the parent handed over replace the goal's
        // subterms before translation, so the engine never sees the
        // original subterm and does not normalize it again.
        let hints = normal_form_hints(&forest);
        let [conclusion] = step.clause.as_slice() else {
            return Err(format!(
                "setup: expected a single-literal clause, found {} literals",
                step.clause.len()
            ));
        };
        if let Some(reason) = out_of_scope(conclusion) {
            return Err(reason.to_owned());
        }
        let mut memo = HashMap::new();
        let mut replaced = 0;
        let goal = crate::rare::util::substitute_by_hash(
            &mut pool,
            conclusion,
            &hints,
            &mut memo,
            &mut replaced,
        );
        if replaced > 0 {
            eprintln!("substituted {replaced} normal forms into the goal");
        }
        // The structural descent checks the atom pairs of a shared Boolean
        // skeleton one by one; the whole goal is the fallback.  The normal
        // forms are exported from the whole goal's e-graph only.
        if !export_normal_forms {
            if let Some(verdict) = check_by_descent(&mut pool, &node, &goal, &database, options, phase) {
                return verdict.map(|()| Vec::new());
            }
            if let Some(verdict) = check_by_atoms(&mut pool, &node, &goal, &database, options, phase) {
                return verdict.map(|()| Vec::new());
            }
        }
        return check_hole_exporting(
            &mut pool,
            &node,
            &goal,
            &database,
            options,
            export_normal_forms,
            phase,
        );
    }
    reconstruct_steps_timed(&mut pool, &node, &step, &database, options, phase)
}

/// The normal forms a parent handed to this child, from the `nf-hint` steps
/// of the input: structural hash of the subterm to replace -> its normal form.
fn normal_form_hints(forest: &ProofNodeForest) -> HashMap<u64, crate::ast::Rc<crate::ast::Term>> {
    let mut hints = HashMap::new();
    for root in &forest.0 {
        let ProofNode::Step(step) = root.as_ref() else {
            continue;
        };
        if step.rule != NF_HINT_RULE {
            continue;
        }
        let (Some(hash), Some(clause)) = (step.args.first(), step.clause.first()) else {
            continue;
        };
        let (Some(crate::ast::Term::Const(Constant::Integer(hash))), Some((_, lhs, _))) = (
            Some(hash.as_ref()),
            crate::rare::util::get_equational_terms(clause),
        ) else {
            continue;
        };
        if let Some(hash) = hash.to_u64() {
            hints.insert(hash, lhs.clone());
        }
    }
    hints
}

/// The most subterms of a goal whose normal forms a child exports.
pub const NF_EXPORT_CAP: usize = 256;

/// [`check_hole`] on `goal` (the hole's conclusion, possibly with normal
/// forms substituted in), which after a successful check also reports the
/// normal forms the e-graph found for the goal's compound subterms when
/// `export` is set: one `nf <hash> <term>` line per subterm whose class
/// holds a smaller term, `<hash>` being the subterm's structural hash.
fn check_hole_exporting(
    pool: &mut PrimitivePool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    export: bool,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let clock = Instant::now();
    let (result, program) = run_egglog(pool, (goal.clone(), node), rules, options);
    phase("egglog", clock.elapsed());
    let egraph = result.map_err(|error| format!("egglog check: {error}"))?;
    if !export {
        return Ok(Vec::new());
    }
    // The snapshot is skipped when it would not fit the budget or the graph
    // is too large to copy: the verdict stands, the later holes just get
    // nothing from this one.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline)
        || egraph.num_tuples() > MAX_SNAPSHOT_TUPLES
    {
        return Ok(Vec::new());
    }
    let clock = Instant::now();
    let snapshot = EGraphSnapshot::from_raw_nodes(EGraphSnapshot::serialize_production(&egraph));
    phase("serialize", clock.elapsed());
    let clock = Instant::now();
    let lines = export_normal_forms(goal, &snapshot, &program);
    phase("export", clock.elapsed());
    Ok(lines)
}

/// The `nf` lines for `goal`: its compound subterms are aligned with the
/// encoded goal the engine built (the same tree, one `Mk` node per term),
/// each is classified in the snapshot, and the smallest decodable term of
/// its class is reported when it is strictly smaller than the subterm.
fn export_normal_forms(
    goal: &crate::ast::Rc<crate::ast::Term>,
    snapshot: &EGraphSnapshot,
    program: &str,
) -> Vec<String> {
    let (lhs, rhs) = generated_goals(program);
    let names = goal_variable_names(&lhs, &rhs, goal);
    let Some((goal_lhs, goal_rhs)) = crate::rare::util::get_equational_terms(goal)
        .map(|(_, lhs, rhs)| (lhs.clone(), rhs.clone()))
    else {
        return Vec::new();
    };
    let mut aligned: Vec<(crate::ast::Rc<crate::ast::Term>, Term)> = Vec::new();
    align_encoded(&goal_lhs, &lhs, &mut aligned);
    align_encoded(&goal_rhs, &rhs, &mut aligned);
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut classes = HashMap::new();
    let mut representatives: HashMap<u32, Option<Term>> = HashMap::new();
    let mut memo = HashMap::new();
    let mut lines = Vec::new();
    for (subterm, encoded) in aligned {
        if lines.len() >= NF_EXPORT_CAP {
            break;
        }
        if !seen.insert(crate::ast::Rc::as_ptr(&subterm) as *const () as usize) {
            continue;
        }
        let Some(class) = snapshot.class_of(&encoded, &mut classes) else {
            continue;
        };
        let Some(representative) =
            smallest_in_class(snapshot, class, &mut representatives, &mut Vec::new())
        else {
            continue;
        };
        if representative.size() >= encoded.size() || !all_variables_named(&representative, &names)
        {
            continue;
        }
        let Some(text) = decode_any(&representative, &names) else {
            continue;
        };
        lines.push(format!(
            "nf {} {text}",
            crate::rare::util::structural_hash(&subterm, &mut memo)
        ));
    }
    lines
}

/// Pairs each compound subterm of `term` with its encoding, walking both
/// trees in step: an operator application is `(Mk (@op (Args ...)))` with
/// one list element per argument, a function application a curried `App`
/// chain.  A subtree whose shapes disagree is left out.
fn align_encoded(
    term: &crate::ast::Rc<crate::ast::Term>,
    encoded: &Term,
    out: &mut Vec<(crate::ast::Rc<crate::ast::Term>, Term)>,
) {
    let ("Mk", [inner]) = (encoded.op.as_str(), encoded.children.as_slice()) else {
        return;
    };
    match term.as_ref() {
        crate::ast::Term::Op(_, args) if !args.is_empty() => {
            let (operator, [list]) = (inner.op.as_str(), inner.children.as_slice()) else {
                return;
            };
            if !operator.starts_with('@') {
                return;
            }
            let Some(elements) = list_elements(list) else {
                return;
            };
            if elements.len() != args.len() {
                return;
            }
            out.push((term.clone(), encoded.clone()));
            for (arg, element) in args.iter().zip(&elements) {
                align_encoded(arg, element, out);
            }
        }
        crate::ast::Term::App(function, args) => {
            let mut arguments = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                arguments.push(argument);
                current = next;
            }
            arguments.reverse();
            if arguments.len() != args.len() {
                return;
            }
            out.push((term.clone(), encoded.clone()));
            align_encoded(function, current, out);
            for (arg, argument) in args.iter().zip(arguments) {
                align_encoded(arg, argument, out);
            }
        }
        _ => {}
    }
}

/// Whether every variable of an encoded term has a name in `names`, i.e.
/// comes from the goal; a term over a premise's variables cannot be printed.
fn all_variables_named(term: &Term, names: &HashMap<String, String>) -> bool {
    if term.op == "Var" {
        return term
            .children
            .first()
            .is_some_and(|id| names.contains_key(&id.op));
    }
    term.children
        .iter()
        .all(|child| all_variables_named(child, names))
}

/// The smallest term of a class, built from the class's enodes over the
/// smallest terms of their children (solver-internal rows skipped), or
/// `None` for a class reachable only through internal rows or a cycle.
fn smallest_in_class(
    snapshot: &EGraphSnapshot,
    class: u32,
    memo: &mut HashMap<u32, Option<Term>>,
    visiting: &mut Vec<u32>,
) -> Option<Term> {
    if let Some(known) = memo.get(&class) {
        return known.clone();
    }
    if visiting.contains(&class) {
        return None;
    }
    visiting.push(class);
    let mut best: Option<Term> = None;
    if let Some(indices) = snapshot.class_nodes.get(class as usize) {
        for &index in indices {
            let node = &snapshot.nodes[index as usize];
            let op = snapshot.ops.names[node.op as usize].as_str();
            if INTERNAL_OPS.contains(&op) {
                continue;
            }
            let Some(children) = node
                .child_classes
                .iter()
                .map(|&child| smallest_in_class(snapshot, child, memo, visiting))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let candidate = Term::new(op, children);
            if best
                .as_ref()
                .is_none_or(|current| (candidate.size(), &candidate) < (current.size(), current))
            {
                best = Some(candidate);
            }
        }
    }
    visiting.pop();
    memo.insert(class, best.clone());
    best
}

/// Reconstructs a hole in a child process that is killed outright when the
/// budget expires.  This is the only hard per-hole bound: the in-process
/// budget can stop egglog only between iterations, and one iteration may run
/// for minutes.  The child is this same binary's hidden `reconstruct-hole`
/// subcommand, fed [`hole_input`] on stdin and read back as Alethe text; an
/// optional address-space limit is applied to it through `ulimit`, so a hole
/// that blows up in memory dies alone instead of taking the parent with it.
pub fn reconstruct_in_child(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    node: &Rc<ProofNode>,
    step: &StepNode,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    deadline: Option<Instant>,
    extra_premises: &[crate::ast::Rc<crate::ast::Term>],
    hints: &[(u64, String)],
    export_normal_forms: bool,
) -> Result<Vec<String>, String> {
    let input = hole_input(pool, prelude, node, step, extra_premises, hints)
        .ok_or_else(|| "expected a single-literal clause".to_owned())?;
    run_hole_worker(
        &step.id,
        input,
        rare_file,
        options,
        None,
        memory_limit_mb,
        check_only,
        if export_normal_forms {
            WorkerMode::SingleExporting
        } else {
            WorkerMode::Single
        },
        deadline,
    )
    .map_err(|(reason, _)| reason)
}

/// Checks a batch of holes in one child process (`reconstruct-hole
/// --check-only --batch`), which saturates them in one e-graph and reports
/// one verdict per hole.  `Ok` maps each hole's id to its verdict; `Err` is
/// the batch as a whole failing (killed at its budget or the proof's, out of
/// memory, or a worker error), in which case the caller may retry the holes
/// one by one.  `options.timeout` is the batch's own budget.
#[allow(clippy::too_many_arguments)]
pub fn check_batch_in_child(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    holes: &[(&Rc<ProofNode>, &StepNode)],
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    sequential: bool,
    deadline: Option<Instant>,
) -> Result<HashMap<String, Result<(), String>>, (String, HashMap<String, Result<(), String>>)> {
    let input = holes_input(pool, prelude, holes)
        .ok_or_else(|| ("expected single-literal clauses".to_owned(), HashMap::new()))?;
    let label = format!("batch of {} holes", holes.len());
    // Verdict lines, plus the hole the child had started when it died: that
    // one is charged with the death rather than retried, since alone it
    // would die the same way.
    let parse = |lines: Vec<String>, death: Option<&str>| {
        let mut verdicts = HashMap::new();
        let mut started: Option<String> = None;
        for line in lines {
            let Some(rest) = line.strip_prefix("hole ") else {
                continue;
            };
            let Some((id, verdict)) = rest.split_once(' ') else {
                continue;
            };
            if verdict == "started" {
                started = Some(id.to_owned());
                continue;
            }
            let verdict = match verdict.strip_prefix("failed: ") {
                Some(reason) => Err(reason.to_owned()),
                None => Ok(()),
            };
            verdicts.insert(id.to_owned(), verdict);
        }
        if let (Some(id), Some(reason)) = (started, death) {
            verdicts
                .entry(id)
                .or_insert_with(|| Err(reason.to_owned()));
        }
        verdicts
    };
    match run_hole_worker(
        &label,
        input,
        rare_file,
        options,
        kill_after,
        memory_limit_mb,
        true,
        if sequential { WorkerMode::BatchSequential } else { WorkerMode::Batch },
        deadline,
    ) {
        Ok(lines) => Ok(parse(lines, None)),
        // A killed child may have reported some verdicts before dying.
        Err((reason, lines)) => {
            let partial = parse(lines, Some(&reason));
            Err((reason, partial))
        }
    }
}

/// What the child checks: one hole, a batch in one e-graph, or a batch one
/// hole at a time over a shared rule database.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WorkerMode {
    Single,
    /// One hole, checked, with the normal forms of its goal's subterms
    /// reported afterwards.
    SingleExporting,
    Batch,
    BatchSequential,
}

/// Runs this binary's `reconstruct-hole` subcommand on `input`, killed at
/// the earlier of `options.timeout` and `deadline`, and returns its stdout
/// lines; on failure, the reason together with whatever stdout lines the
/// child produced before it died.
#[allow(clippy::too_many_arguments)]
fn run_hole_worker(
    label: &str,
    input: String,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    mode: WorkerMode,
    deadline: Option<Instant>,
) -> Result<Vec<String>, (String, Vec<String>)> {
    let batch = !matches!(mode, WorkerMode::Single | WorkerMode::SingleExporting);
    run_hole_worker_inner(
        label,
        input,
        rare_file,
        options,
        kill_after,
        memory_limit_mb,
        check_only,
        batch,
        mode == WorkerMode::BatchSequential,
        mode == WorkerMode::SingleExporting,
        deadline,
    )
}

/// `kill_after` is the child's hard budget when it differs from the
/// cooperative one in `options` (a sequential batch: the per-hole budget
/// inside, the batch's outside).
#[allow(clippy::too_many_arguments)]
fn run_hole_worker_inner(
    label: &str,
    input: String,
    rare_file: &Path,
    options: crate::checker::RunEgglogOptions,
    kill_after: Option<Duration>,
    memory_limit_mb: Option<usize>,
    check_only: bool,
    batch: bool,
    sequential: bool,
    export_normal_forms: bool,
    deadline: Option<Instant>,
) -> Result<Vec<String>, (String, Vec<String>)> {
    let fail = |reason: String| (reason, Vec::new());
    let exe = std::env::current_exe()
        .map_err(|error| fail(format!("locating carcara: {error}")))?;
    // At debug level the child logs too and its whole stderr is reported, so
    // a reconstruction can be followed.
    let debug = log::log_enabled!(log::Level::Debug);
    let mut arguments: Vec<std::ffi::OsString> = Vec::new();
    if debug {
        arguments.push("--log".into());
        arguments.push("debug".into());
    }
    arguments.extend::<[std::ffi::OsString; 3]>([
        "reconstruct-hole".into(),
        "--rare-file".into(),
        rare_file.into(),
    ]);
    if let Some(timeout) = options.timeout {
        arguments.push("--rare-check-timeout".into());
        arguments.push(timeout.as_millis().to_string().into());
    }
    if options.continuous_saturation {
        arguments.push("--continuous-saturation".into());
    }
    if options.seed_from_goal {
        arguments.push("--seed-from-goal".into());
    }
    if options.sort_guards {
        arguments.push("--sort-guards".into());
    }
    // The worker prepares its own RARE database, so the encoding has to
    // travel with it or an isolated hole would silently use the default.
    arguments.push("--list-encoding".into());
    arguments.push(
        match options.list_encoding {
            crate::checker::ListEncoding::SetForm => "set-form",
            crate::checker::ListEncoding::Chain => "chain",
        }
        .into(),
    );
    if options.growth_cap_arith > 0 {
        arguments.push("--growth-cap-arith".into());
        arguments.push(options.growth_cap_arith.to_string().into());
    }
    if options.growth_cap_plain > 0 {
        arguments.push("--growth-cap-plain".into());
        arguments.push(options.growth_cap_plain.to_string().into());
    }
    if options.memory_soft_cap_mb > 0 {
        arguments.push("--memory-soft-cap".into());
        arguments.push(options.memory_soft_cap_mb.to_string().into());
    }
    if options.descend_min_nodes > 0 {
        arguments.push("--descend-min-nodes".into());
        arguments.push(options.descend_min_nodes.to_string().into());
    }
    if check_only {
        arguments.push("--check-only".into());
    }
    if batch {
        arguments.push("--batch".into());
    }
    if sequential {
        arguments.push("--batch-sequential".into());
    }
    if export_normal_forms {
        arguments.push("--export-normal-forms".into());
    }
    let mut command = match memory_limit_mb {
        // `exec` keeps the child's pid on carcara itself, so killing the pid
        // kills the worker and not a shell wrapped around it.
        Some(megabytes) => {
            let mut command = Command::new("sh");
            command
                .arg("-c")
                .arg("ulimit -v \"$0\" && exec \"$@\"")
                .arg((megabytes * 1024).to_string())
                .arg(&exe)
                .args(&arguments);
            command
        }
        None => {
            let mut command = Command::new(&exe);
            command.args(&arguments);
            command
        }
    };
    let started = Instant::now();
    // The child dies at the earlier of its own budget and the proof's.
    let own_deadline = kill_after
        .or(options.timeout)
        .and_then(|timeout| started.checked_add(timeout));
    let kill_at = match (own_deadline, deadline) {
        (Some(own), Some(all)) => Some(own.min(all)),
        (own, all) => own.or(all),
    };
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| fail(format!("spawning the hole worker: {error}")))?;
    // A child that dies early closes the pipe; the write then fails with
    // EPIPE (Rust ignores SIGPIPE), which the exit status below explains.
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(input.as_bytes());
    }
    // Both pipes are drained concurrently: the steps can run to megabytes, and
    // a child blocked on a full pipe would look exactly like a stuck one.
    let drain = |mut pipe: Option<_>| {
        std::thread::spawn(move || {
            let mut buffer = Vec::new();
            if let Some(pipe) = pipe.as_mut() {
                let _ = std::io::Read::read_to_end(pipe, &mut buffer);
            }
            buffer
        })
    };
    let stdout = child
        .stdout
        .take()
        .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>);
    let stderr = child
        .stderr
        .take()
        .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>);
    let stdout = drain(stdout);
    let stderr = drain(stderr);
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| fail(format!("waiting for the hole worker: {error}")))?
        {
            break Some(status);
        }
        if kill_at.is_some_and(|kill_at| Instant::now() >= kill_at) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = stdout.join().unwrap_or_default();
    let stderr = stderr.join().unwrap_or_default();
    if debug {
        log::debug!("hole worker stderr:\n{}", String::from_utf8_lossy(&stderr));
    }
    // The child reports "phase <name>=<seconds>" as each phase completes, so
    // the phases seen say how far it got.
    let phases: Vec<(String, String)> = String::from_utf8_lossy(&stderr)
        .lines()
        .filter_map(|line| line.strip_prefix("phase ")?.split_once('='))
        .map(|(name, secs)| (name.to_owned(), secs.to_owned()))
        .collect();
    let phase_in_progress = || {
        PHASES
            .iter()
            .find(|name| !phases.iter().any(|(seen, _)| seen == *name))
            .copied()
            .unwrap_or("emit")
    };
    if !phases.is_empty() && !check_only {
        log::info!(
            "hole {}: phases {}",
            label,
            phases
                .iter()
                .map(|(name, secs)| format!("{name}={secs}"))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }
    let lines = || -> Vec<String> {
        String::from_utf8_lossy(&stdout)
            .lines()
            .filter(|line| !line.trim().is_empty())
            .map(str::to_owned)
            .collect()
    };
    let tail = || {
        // The reason is the last thing the child said that was not egglog's
        // routine "Query took a long time" chatter, which would otherwise
        // crowd the real error out of a three-line tail.
        let text = String::from_utf8_lossy(&stderr);
        let lines: Vec<&str> = text
            .lines()
            .filter(|l| {
                let l = l.trim_start();
                !l.is_empty() && !l.starts_with("warn:") && !l.starts_with("phase ")
            })
            .collect();
        lines[lines.len().saturating_sub(3)..].join(" | ")
    };
    match status {
        None => {
            let by_proof = deadline.is_some_and(|all| own_deadline.is_none_or(|own| all < own));
            // The phases already completed say how the budget was spent
            // before the kill, e.g. "(after egglog=0.2)".
            let completed = phases
                .iter()
                .map(|(name, secs)| format!("{name}={secs}"))
                .collect::<Vec<_>>()
                .join(" ");
            Err((format!(
                "killed after {:.1}s during {}{}: {}",
                started.elapsed().as_secs_f64(),
                if check_only {
                    "egglog"
                } else {
                    phase_in_progress()
                },
                if completed.is_empty() {
                    String::new()
                } else {
                    format!(" (after {completed})")
                },
                if by_proof {
                    "the proof's hole budget ran out"
                } else {
                    "hard budget exhausted"
                }
            ), lines()))
        }
        Some(status) if status.success() => Ok(lines()),
        Some(status) => match status.signal() {
            // The phase says whether egglog had proved the hole before the
            // memory limit took the worker: a kill during serialization or
            // the search is a checked hole the elaboration lost.
            Some(signal) => Err((
                format!(
                    "worker killed by signal {signal} during {}{}: {}",
                    if check_only {
                        "egglog"
                    } else {
                        phase_in_progress()
                    },
                    {
                        let completed = phases
                            .iter()
                            .map(|(name, secs)| format!("{name}={secs}"))
                            .collect::<Vec<_>>()
                            .join(" ");
                        if completed.is_empty() {
                            String::new()
                        } else {
                            format!(" (after {completed})")
                        }
                    },
                    tail()
                ),
                lines(),
            )),
            None => Err((
                format!(
                    "worker exited with status {}: {}",
                    status.code().unwrap_or(-1),
                    tail()
                ),
                lines(),
            )),
        },
    }
}

/// The egglog phase alone: whether the engine proves the hole's equality
/// within the budget.  This is the checking half of the evaluation, run under
/// the same workers and limits as reconstruction so the two are comparable.
pub fn check_hole(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Result<(), String> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(format!(
            "setup: expected a single-literal clause, found {} literals",
            step.clause.len()
        ));
    };
    let (result, _) = run_egglog(pool, (conclusion.clone(), node), rules, options);
    result
        .map(|_| ())
        .map_err(|error| format!("egglog check: {error}"))
}

/// [`check_hole`] over an already prepared rule database, so that a run of
/// holes pays for the database once.
pub fn check_hole_with_context(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    context: &crate::rare::engine::RareCtx<'_>,
    options: crate::checker::RunEgglogOptions,
) -> Result<(), String> {
    let [conclusion] = step.clause.as_slice() else {
        return Err(format!(
            "setup: expected a single-literal clause, found {} literals",
            step.clause.len()
        ));
    };
    let assumptions = node.get_assumptions();
    let premise_clauses: Vec<&[crate::ast::Rc<crate::ast::Term>]> =
        assumptions.iter().map(|premise| premise.clause()).collect();
    let (result, _) = crate::rare::engine::check_hole_rewrite_with_context(
        pool,
        &step.id,
        conclusion.clone(),
        &premise_clauses,
        context,
        options,
    );
    result
        .map(|_| ())
        .map_err(|error| format!("egglog check: {error}"))
}

/// Whether a term is `(ite c x y)` with `c` a Boolean constant, in either
/// the wrapped or the unwrapped encoding.
fn constant_condition_ite(term: &Term) -> bool {
    let inner = if term.op == "Mk" {
        match term.children.first() {
            Some(inner) => inner,
            None => return false,
        }
    } else {
        term
    };
    if inner.op != "@ite" {
        return false;
    }
    let Some(arguments) = inner.children.first() else {
        return false;
    };
    matches!(list_elements(arguments).as_deref(), Some([condition, _, _])
        if crate::rare::reconstruction::term::bool_value(condition).is_some())
}

/// The Alethe steps justifying one `TRUST_THEORY_REWRITE` hole.
///
/// Split out from [`elaborate`] because it is the whole cost of a hole and
/// touches nothing shared: it reads the proof node, drives egglog on a pool of
/// its own, and returns text.  That makes it safe to run for many holes at
/// once, with the results parsed back into the proof's own pool afterwards.
pub fn reconstruct_steps(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
) -> Result<Vec<String>, String> {
    reconstruct_steps_timed(pool, node, step, rules, options, &mut |_, _| {})
}

/// The phases of one hole's reconstruction, in order.  A worker reports each
/// as it completes, so a hole cut short can be attributed to the phase it was
/// in.
pub const PHASES: [&str; 5] = ["egglog", "serialize", "index", "search", "emit"];

/// [`reconstruct_steps`], calling `phase` with each phase's name and duration
/// as it completes.
pub fn reconstruct_steps_timed(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let stage = |stage: &str, detail: String| format!("{stage}: {detail}");
    let [conclusion] = step.clause.as_slice() else {
        return Err(stage(
            "setup",
            format!(
                "expected a single-literal clause, found {} literals",
                step.clause.len()
            ),
        ));
    };

    if let Some(reason) = out_of_scope(conclusion) {
        return Err(reason.to_owned());
    }
    // One budget covers the whole hole: the egglog check and the search that
    // follows it are two phases of the same per-hole work, so bounding only
    // the first leaves the second free to run away.
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    // The whole goal first, on a quarter of the budget: most holes close
    // that way in a second, and a descent pair the alignment got wrong can
    // take the worker's memory with it.  Then the descent on half of what
    // is left, then the whole goal again with the rest, in a fresh process
    // when the caller can give one.
    let structural = descent_sides(pool, conclusion, options).is_some();
    let atoms = !structural && atom_sides(pool, conclusion, options).is_some();
    if !options.descend_first && (structural || atoms) {
        let started = Instant::now();
        // A quarter of the budget, ten seconds at most: a goal the whole
        // attempt closes closes fast, and a Dartagnan goal of seventy
        // pairs needs the budget for its pairs.
        let quarter = deadline.map(|d| {
            started + (d.saturating_duration_since(started) / 4).min(Duration::from_secs(10))
        });
        if let Ok(steps) =
            reconstruct_subgoal(pool, node, conclusion, &step.id, rules, options, quarter, phase)
        {
            return Ok(steps);
        }
        eprintln!("phase whole-first={:.3}", started.elapsed().as_secs_f64());
    }
    if let Descent::Proved(steps) =
        reconstruct_by_descent(pool, node, conclusion, &step.id, rules, options, deadline, phase)
    {
        return Ok(steps);
    }
    if atoms {
        if let Descent::Proved(steps) =
            reconstruct_by_atoms(pool, node, conclusion, &step.id, rules, options, deadline, phase)
        {
            return Ok(steps);
        }
    }
    reconstruct_subgoal(pool, node, conclusion, &step.id, rules, options, deadline, phase)
}

/// An isolated worker's input and the id of its hole, kept (leaked, once)
/// for the fresh processes the worker spawns for its goals.
#[derive(Debug, PartialEq, Eq)]
pub struct WorkerInput {
    pub text: String,
    pub hole_id: String,
}

/// One goal `(= lhs rhs)`, numbered under `prefix`: in a fresh process
/// when the worker has one to give (`RunEgglogOptions::worker`), in this
/// one otherwise.  The child gets the worker's input with the hole step
/// replaced by the goal, the worker's command line without the descent,
/// what is left of the deadline as its budget, and a kill a few seconds
/// past it; its steps are its stdout.
#[allow(clippy::too_many_arguments)]
fn reconstruct_subgoal(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    prefix: &str,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    deadline: Option<Instant>,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let Some(worker) = options.worker else {
        return reconstruct_goal(pool, node, goal, prefix, rules, options, deadline, phase);
    };
    let budget = deadline
        .map(|d| d.saturating_duration_since(Instant::now()))
        .or(options.timeout);
    if budget.is_some_and(|b| b.is_zero()) {
        return Err(format!("{prefix}: budget exhausted"));
    }
    subgoal_in_fresh_process(worker, goal, prefix, budget, true)
}

/// The checking-only counterpart of [`reconstruct_subgoal`]: the goal
/// checked by egglog in a fresh process when the worker has one (the
/// child inherits `--check-only`), in this one otherwise.
fn check_subgoal(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    prefix: &str,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    budget: Option<Duration>,
) -> Result<(), String> {
    if let Some(worker) = options.worker {
        if budget.is_some_and(|b| b.is_zero()) {
            return Err(format!("{prefix}: budget exhausted"));
        }
        return subgoal_in_fresh_process(worker, goal, prefix, budget, false).map(|_| ());
    }
    let (result, _) = run_egglog(pool, (goal.clone(), node), rules, options);
    result.map(|_| ()).map_err(|error| format!("egglog check: {error}"))
}

fn subgoal_in_fresh_process(
    worker: &WorkerInput,
    goal: &crate::ast::Rc<crate::ast::Term>,
    prefix: &str,
    budget: Option<Duration>,
    expect_steps: bool,
) -> Result<Vec<String>, String> {
    use std::io::{Read, Write};
    let head = format!("(step {} (cl ", worker.hole_id);
    let mut text = String::with_capacity(worker.text.len());
    let mut replaced = false;
    for line in worker.text.lines() {
        match line.strip_prefix(&head) {
            Some(rest) => {
                let tail = rest
                    .find(") :rule hole")
                    .ok_or_else(|| "fresh process: the hole step has no rule".to_owned())?;
                text.push_str(&format!("(step {prefix} (cl {goal:#}){}", &rest[tail + 1..]));
                replaced = true;
            }
            None => text.push_str(line),
        }
        text.push('\n');
    }
    if !replaced {
        return Err("fresh process: the hole step is not in the input".to_owned());
    }
    // A diagnostic: the inputs of the fresh processes, one file per goal.
    if let Ok(dir) = std::env::var("CARCARA_SUBGOAL_DUMP") {
        let _ = std::fs::write(format!("{dir}/{prefix}.in"), &text);
    }
    let mut arguments: Vec<String> = Vec::new();
    let mut skip = false;
    for argument in std::env::args().skip(1) {
        if skip {
            skip = false;
            continue;
        }
        match argument.as_str() {
            "--descend-min-nodes" | "--rare-check-timeout" => skip = true,
            "--descend-first" => {}
            _ => arguments.push(argument),
        }
    }
    if let Some(budget) = budget {
        arguments.push("--rare-check-timeout".to_owned());
        arguments.push(budget.as_millis().max(1).to_string());
    }
    let exe = std::env::current_exe().map_err(|e| format!("fresh process: {e}"))?;
    let mut command = std::process::Command::new(exe);
    command
        .args(&arguments)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::inherit());
    // The child dies with this worker: the parent's budget kills this pid
    // only, and an orphan would run on.
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::process::CommandExt;
        unsafe {
            command.pre_exec(|| {
                libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL);
                Ok(())
            });
        }
    }
    let mut child = command.spawn().map_err(|e| format!("fresh process: {e}"))?;
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(text.as_bytes());
    }
    let mut stdout = child
        .stdout
        .take()
        .ok_or_else(|| "fresh process: no stdout".to_owned())?;
    let reader = std::thread::spawn(move || {
        let mut output = String::new();
        let _ = stdout.read_to_string(&mut output);
        output
    });
    let started = Instant::now();
    let kill_at = budget.map(|b| started + b + Duration::from_secs(3));
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| format!("fresh process: {e}"))? {
            break Some(status);
        }
        if kill_at.is_some_and(|kill_at| Instant::now() >= kill_at) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = reader.join().unwrap_or_default();
    match status {
        Some(status) if status.success() => {
            let steps: Vec<String> = output
                .lines()
                .filter(|line| !line.trim().is_empty())
                .map(str::to_owned)
                .collect();
            if steps.is_empty() && expect_steps {
                Err(format!("fresh process for {prefix}: no steps"))
            } else {
                Ok(steps)
            }
        }
        Some(status) => Err(format!("fresh process for {prefix} exited with {status}")),
        None => Err(format!("fresh process for {prefix}: budget exhausted, killed")),
    }
}

/// What the structural descent made of a goal.
pub enum Descent {
    /// The goal's sides share no skeleton, or it is below the size bound.
    NotApplicable,
    Proved(Vec<String>),
    /// A pair could not be proved; the whole goal is the fallback.
    Failed,
}

/// Whether the structural descent looks through `term`: a Boolean
/// connective, or an `ite` or `=` over Boolean arguments.  Atoms (relations,
/// equalities of terms, applications) are where a pair becomes a goal of
/// its own.
fn descends_through(pool: &mut dyn TermPool, term: &crate::ast::Rc<crate::ast::Term>) -> bool {
    use crate::ast::Operator::*;
    let crate::ast::Term::Op(op, args) = term.as_ref() else {
        return false;
    };
    let _ = pool;
    match op {
        And | Or | Not | Implies | Xor => true,
        Ite => args.get(1).is_some_and(is_boolean),
        Equals => args.first().is_some_and(is_boolean),
        _ => false,
    }
}

/// Whether `term` is of sort Bool, read off the term itself (an in-process
/// worker's pool need not know the sort of every subterm); a predicate of
/// another theory reads as not Boolean, which only keeps the descent out.
fn is_boolean(term: &crate::ast::Rc<crate::ast::Term>) -> bool {
    use crate::ast::Operator::*;
    match term.as_ref() {
        crate::ast::Term::Var(_, sort) => matches!(sort.as_ref(), crate::ast::Sort::Bool),
        crate::ast::Term::Op(
            True | False | Not | Implies | And | Or | Xor | Equals | Distinct | LessThan
            | GreaterThan | LessEq | GreaterEq | IsInt,
            _,
        ) => true,
        crate::ast::Term::Op(Ite, args) => args.get(1).is_some_and(is_boolean),
        crate::ast::Term::App(function, _) => match function.as_ref() {
            crate::ast::Term::Var(_, sort) => match sort.as_ref() {
                crate::ast::Sort::Function(sorts) => {
                    sorts.last().is_some_and(|s| matches!(s.as_ref(), crate::ast::Sort::Bool))
                }
                _ => false,
            },
            _ => false,
        },
        crate::ast::Term::Binder(crate::ast::Binder::Forall | crate::ast::Binder::Exists, ..) => true,
        crate::ast::Term::Let(_, body) => is_boolean(body),
        _ => false,
    }
}

/// The sides of `(= lhs rhs)` share a skeleton the descent looks through.
fn shares_skeleton(
    pool: &mut dyn TermPool,
    lhs: &crate::ast::Rc<crate::ast::Term>,
    rhs: &crate::ast::Rc<crate::ast::Term>,
) -> bool {
    match (lhs.as_ref(), rhs.as_ref()) {
        (crate::ast::Term::Op(f, fa), crate::ast::Term::Op(g, ga)) => {
            f == g
                && (fa.len() == ga.len()
                    || matches!(f, crate::ast::Operator::And | crate::ast::Operator::Or))
                && descends_through(pool, lhs)
        }
        _ => false,
    }
}

/// The structural descent of `(= lhs rhs)`: over a shared Boolean skeleton
/// the equality follows by `cong` from the equalities of the argument pairs
/// that differ, recursively; a pair the skeleton does not share is a goal
/// of its own, handed to `base` with its number.  Returns the id of the
/// step concluding `(= lhs rhs)`, `None` when the sides are identical; the
/// `cong` steps go to `out`, numbered `{id}.{position}`, so that the last
/// step pushed is the conclusion.
#[allow(clippy::too_many_arguments)]
fn descend(
    pool: &mut dyn TermPool,
    lhs: &crate::ast::Rc<crate::ast::Term>,
    rhs: &crate::ast::Rc<crate::ast::Term>,
    id: &str,
    out: &mut Vec<String>,
    goals: &mut usize,
    base: &mut dyn FnMut(
        &mut dyn TermPool,
        &crate::ast::Rc<crate::ast::Term>,
        &crate::ast::Rc<crate::ast::Term>,
        usize,
        &mut Vec<String>,
    ) -> Result<String, String>,
) -> Result<Option<String>, String> {
    if lhs == rhs {
        return Ok(None);
    }
    // `(= (= a b) true)`, the shape of a predicate rewritten to `true`
    // (cvc5's `MACRO_SR_PRED_INTRO`): the equality's two sides are the
    // pair to prove, then `(= (= a b) (= b b))` by `cong` and
    // `(= (= b b) true)` by `eq-refl`.
    if let (crate::ast::Term::Op(crate::ast::Operator::Equals, fa), true) =
        (lhs.as_ref(), rhs.is_bool_true())
    {
        if fa.len() == 2 && fa[0] != fa[1] {
            let (a, b) = (fa[0].clone(), fa[1].clone());
            let inner = descend(pool, &a, &b, id, out, goals, base)?
                .ok_or_else(|| "descent: identical sides under an equality".to_owned())?;
            let reflexive = pool.add(crate::ast::Term::Op(
                crate::ast::Operator::Equals,
                vec![b.clone(), b.clone()],
            ));
            let cong_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {cong_id} (cl (= {lhs:#} {reflexive:#})) :rule cong :premises ({inner}))"
            ));
            let refl_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {refl_id} (cl (= {reflexive:#} {rhs:#})) :rule rare_rewrite :args (\"eq-refl\" {b:#}))"
            ));
            let step_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {step_id} (cl (= {lhs:#} {rhs:#})) :rule trans :premises ({cong_id} {refl_id}))"
            ));
            return Ok(Some(step_id));
        }
    }
    // `(= (= a b) (= b a))`, the orientation of an equality, is
    // `eq_symmetric`; pairing the arguments by position would fail.
    if let (
        crate::ast::Term::Op(crate::ast::Operator::Equals, fa),
        crate::ast::Term::Op(crate::ast::Operator::Equals, ga),
    ) = (lhs.as_ref(), rhs.as_ref())
    {
        if fa.len() == 2 && ga.len() == 2 && fa[0] == ga[1] && fa[1] == ga[0] {
            let step_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {step_id} (cl (= {lhs:#} {rhs:#})) :rule eq_symmetric)"
            ));
            return Ok(Some(step_id));
        }
    }
    if shares_skeleton(pool, lhs, rhs) {
        let (crate::ast::Term::Op(op, fa), crate::ast::Term::Op(_, ga)) = (lhs.as_ref(), rhs.as_ref())
        else {
            unreachable!("a shared skeleton is an operator application")
        };
        let op = *op;
        // Under `and`/`or` the arguments are matched, not paired by
        // position: the normal forms order them by term address, so the
        // identical ones align but the rewritten ones need not.  A
        // reordering is an `aci_simp` step on each side around the `cong`.
        let (fa, ga) = if matches!(op, crate::ast::Operator::And | crate::ast::Operator::Or) {
            align_aci(pool, op, fa, ga)
                .ok_or_else(|| "descent: the arguments do not align".to_owned())?
        } else {
            (fa.clone(), ga.clone())
        };
        let aligned_lhs = pool.add(crate::ast::Term::Op(op, fa.clone()));
        let aligned_rhs = pool.add(crate::ast::Term::Op(op, ga.clone()));
        let mut premises = Vec::new();
        for (a, b) in fa.iter().zip(ga.iter()) {
            if let Some(step) = descend(pool, a, b, id, out, goals, base)? {
                premises.push(step);
            }
        }
        let mut chain = Vec::new();
        if aligned_lhs != *lhs {
            let step_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {step_id} (cl (= {lhs:#} {aligned_lhs:#})) :rule aci_simp)"
            ));
            chain.push(step_id);
        }
        // Sides that differ only in the order of their arguments align to
        // one term: no `cong` between them (an empty `:premises` does not
        // parse), the two reorderings carry the step.
        if !premises.is_empty() {
            let step_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {step_id} (cl (= {aligned_lhs:#} {aligned_rhs:#})) :rule cong :premises ({}))",
                premises.join(" ")
            ));
            chain.push(step_id);
        }
        if aligned_rhs != *rhs {
            let step_id = format!("{id}.{}", out.len() + 1);
            out.push(format!(
                "(step {step_id} (cl (= {aligned_rhs:#} {rhs:#})) :rule aci_simp)"
            ));
            chain.push(step_id);
        }
        if chain.len() == 1 {
            return Ok(chain.pop());
        }
        let step_id = format!("{id}.{}", out.len() + 1);
        out.push(format!(
            "(step {step_id} (cl (= {lhs:#} {rhs:#})) :rule trans :premises ({}))",
            chain.join(" ")
        ));
        return Ok(Some(step_id));
    }
    *goals += 1;
    base(pool, lhs, rhs, *goals, out).map(Some)
}

/// The size of an encoded term as a tree (the `Args` cells and wrappers
/// included), what a candidate vertex of the search costs to hold.
fn term_nodes(term: &Term) -> usize {
    1 + term.children.iter().map(term_nodes).sum::<usize>()
}

/// `term` printed, cut to a line for a log message.
fn abbreviated(term: &crate::ast::Rc<crate::ast::Term>) -> String {
    let text = format!("{term:#}");
    if text.len() <= 240 {
        text
    } else {
        format!("{}...", &text[..240])
    }
}

/// The leaves (variables and constants) of `term`, for matching arguments.
fn leaves(
    term: &crate::ast::Rc<crate::ast::Term>,
    out: &mut std::collections::HashSet<crate::ast::Rc<crate::ast::Term>>,
) {
    match term.as_ref() {
        crate::ast::Term::Op(_, args) => args.iter().for_each(|a| leaves(a, out)),
        crate::ast::Term::App(function, args) => {
            out.insert(function.clone());
            args.iter().for_each(|a| leaves(a, out));
        }
        _ => {
            out.insert(term.clone());
        }
    }
}

/// The arguments of two `and`/`or` terms of the same arity, reordered so
/// that identical arguments align first and the rest are paired by the
/// leaves they share (a rewritten atom shares its variables with its
/// original), in the left side's order.
fn align_aci(
    pool: &mut dyn TermPool,
    op: crate::ast::Operator,
    fa: &[crate::ast::Rc<crate::ast::Term>],
    ga: &[crate::ast::Rc<crate::ast::Term>],
) -> Option<(
    Vec<crate::ast::Rc<crate::ast::Term>>,
    Vec<crate::ast::Rc<crate::ast::Term>>,
)> {
    let mut used = vec![false; ga.len()];
    let (mut out_f, mut out_g) = (Vec::with_capacity(fa.len()), Vec::with_capacity(ga.len()));
    let mut rest_f = Vec::new();
    for a in fa {
        match (0..ga.len()).find(|&j| !used[j] && ga[j] == *a) {
            Some(j) => {
                used[j] = true;
                out_f.push(a.clone());
                out_g.push(ga[j].clone());
            }
            None => rest_f.push(a.clone()),
        }
    }
    let rest_g: Vec<_> = (0..ga.len()).filter(|&j| !used[j]).map(|j| ga[j].clone()).collect();
    if rest_f.is_empty() != rest_g.is_empty() {
        log::debug!(
            "descent: {} arguments left on one side and none on the other",
            rest_f.len().max(rest_g.len())
        );
        return None;
    }
    // The side with more arguments left is grouped onto the other: every
    // argument of it goes to the argument of the other side it shares the
    // most leaves with, and a group becomes a nested application, so that
    // an atom the producer expanded into several (`(= x 1)` into two
    // bounds) is one pair, `(= a (and b1 b2))`.  An argument with no leaf
    // in common with anything, or an argument left without a partner, is
    // no alignment.
    let leaves_of = |t: &crate::ast::Rc<crate::ast::Term>| {
        let mut set = std::collections::HashSet::new();
        leaves(t, &mut set);
        set
    };
    let (few, many, few_is_left) = if rest_f.len() <= rest_g.len() {
        (&rest_f, &rest_g, true)
    } else {
        (&rest_g, &rest_f, false)
    };
    let few_leaves: Vec<_> = few.iter().map(leaves_of).collect();
    let many_leaves: Vec<_> = many.iter().map(leaves_of).collect();
    let overlap = |i: usize, j: usize| few_leaves[i].intersection(&many_leaves[j]).count();
    let mut groups: Vec<Vec<crate::ast::Rc<crate::ast::Term>>> = vec![Vec::new(); few.len()];
    let mut taken = vec![false; many.len()];
    // First a partner for every argument of the smaller side, best pairs
    // first, so that none is left empty by the greedy grouping; then the
    // rest of the larger side joins the argument it shares most with.
    for _ in 0..few.len() {
        let best = (0..few.len())
            .filter(|&i| groups[i].is_empty())
            .flat_map(|i| (0..many.len()).filter(|&j| !taken[j]).map(move |j| (overlap(i, j), i, j)))
            .max_by_key(|&(shared, i, j)| (shared, std::cmp::Reverse(i), std::cmp::Reverse(j)))?;
        if best.0 == 0 {
            log::debug!("descent: no partner shares a leaf with {}", abbreviated(&few[best.1]));
            return None;
        }
        taken[best.2] = true;
        groups[best.1].push(many[best.2].clone());
    }
    for (j, b) in many.iter().enumerate() {
        if taken[j] {
            continue;
        }
        let best = (0..few.len())
            .map(|i| (overlap(i, j), std::cmp::Reverse(i)))
            .max()?;
        if best.0 == 0 {
            log::debug!("descent: no partner shares a leaf with {}", abbreviated(b));
            return None;
        }
        groups[best.1 .0].push(b.clone());
    }
    for (i, a) in few.iter().enumerate() {
        let group = std::mem::take(&mut groups[i]);
        let grouped = match group.len() {
            0 => {
                log::debug!("descent: nothing aligned with {}", abbreviated(a));
                return None;
            }
            1 => group[0].clone(),
            _ => pool.add(crate::ast::Term::Op(op, group)),
        };
        if few_is_left {
            out_f.push(a.clone());
            out_g.push(grouped);
        } else {
            out_f.push(grouped);
            out_g.push(a.clone());
        }
    }
    Some((out_f, out_g))
}

/// The engine options of one pair of the descent: the remaining time,
/// and caps well below the whole goal's, so that a pair the alignment got
/// wrong fails fast instead of taking the worker's memory with it (a
/// mispaired Dartagnan atom asked egglog for 6 GB in one allocation where
/// the whole goal proves in 6 s).
fn descent_pair_options(
    options: crate::checker::RunEgglogOptions,
    remaining: Option<Duration>,
) -> crate::checker::RunEgglogOptions {
    let capped = |cap: usize, at: usize| if cap == 0 { at } else { cap.min(at) };
    crate::checker::RunEgglogOptions {
        timeout: remaining.or(options.timeout),
        descend_min_nodes: 0,
        // A sixth of the whole goal's caps: a pair whose block needs more
        // is one the alignment got wrong (a Dartagnan block of four bound
        // pairs proves under 4 M plain tuples; the production 500 k did
        // not hold it).
        growth_cap_arith: capped(options.growth_cap_arith, 20_000_000),
        growth_cap_plain: capped(options.growth_cap_plain, 4_000_000),
        // Two gigabytes of growth: the cap is on the resident set, and a
        // process that already tried the whole goal (or earlier pairs)
        // keeps what it freed.
        memory_soft_cap_mb: capped(
            options.memory_soft_cap_mb,
            2_000 + crate::rare::engine::resident_mb().unwrap_or(0),
        ),
        ..options
    }
}

/// The goal's sides, when the descent applies to it: an equality whose
/// sides share a skeleton and whose size reaches the option's threshold.
fn descent_sides(
    pool: &mut dyn TermPool,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
    options: crate::checker::RunEgglogOptions,
) -> Option<(crate::ast::Rc<crate::ast::Term>, crate::ast::Rc<crate::ast::Term>)> {
    if options.descend_min_nodes == 0 {
        return None;
    }
    let (_, lhs, rhs) = crate::rare::util::get_equational_terms(conclusion)?;
    let predicate_to_true = rhs.is_bool_true()
        && matches!(lhs.as_ref(), crate::ast::Term::Op(crate::ast::Operator::Equals, fa) if fa.len() == 2);
    if !(shares_skeleton(pool, lhs, rhs) || predicate_to_true)
        || super::term_dag_size(conclusion) < options.descend_min_nodes
    {
        return None;
    }
    Some((lhs.clone(), rhs.clone()))
}

/// Reconstructs `(= lhs rhs)` by the structural descent, each atom pair a
/// reconstruction of its own under `{id}.d{n}`; when the descent does not
/// apply or a pair fails, the whole goal is the caller's fallback.  The
/// phases of the pairs are reported summed, once.
#[allow(clippy::too_many_arguments)]
fn reconstruct_by_descent(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
    id: &str,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    deadline: Option<Instant>,
    phase: &mut dyn FnMut(&str, Duration),
) -> Descent {
    let Some((lhs, rhs)) = descent_sides(pool, conclusion, options) else {
        return Descent::NotApplicable;
    };
    let started = Instant::now();
    // How many pairs the descent has (a dry run, no goal solved), so
    // that each gets its share of the budget: twice an even share, eight
    // seconds at least, what is left at most -- one pair the alignment
    // got wrong cannot take the others' time.
    let mut pairs = 0usize;
    let mut dry = |_: &mut dyn TermPool,
                   _: &crate::ast::Rc<crate::ast::Term>,
                   _: &crate::ast::Rc<crate::ast::Term>,
                   _: usize,
                   _: &mut Vec<String>|
     -> Result<String, String> {
        pairs += 1;
        Ok(String::new())
    };
    if descend(pool, &lhs, &rhs, id, &mut Vec::new(), &mut 0, &mut dry).is_err() {
        return Descent::NotApplicable;
    }
    // The descent gets three quarters of what is left: a descent that
    // fails late must leave the whole-goal fallback something (rw3 lost
    // fifteen LassoRanker proofs that way), and its pairs are where a
    // Dartagnan goal's time goes.
    let deadline = deadline.map(|d| started + d.saturating_duration_since(started) * 3 / 4);
    let mut timed: Vec<(String, Duration)> = Vec::new();
    let mut out = Vec::new();
    let mut goals = 0;
    let mut base = |pool: &mut dyn TermPool,
                    a: &crate::ast::Rc<crate::ast::Term>,
                    b: &crate::ast::Rc<crate::ast::Term>,
                    n: usize,
                    out: &mut Vec<String>|
     -> Result<String, String> {
        let remaining = deadline.map(|d| d.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|r| r.is_zero()) {
            return Err("descent: budget exhausted".to_owned());
        }
        let remaining = remaining.map(|r| {
            let left = (pairs + 1).saturating_sub(n).max(1) as u32;
            r.min((r / left * 2).max(Duration::from_secs(8)))
        });
        let deadline = remaining.map(|r| Instant::now() + r);
        let prefix = format!("{id}.d{n}");
        let goal = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![a.clone(), b.clone()],
        ));
        let sub_options = descent_pair_options(options, remaining);
        let mut accumulate = |name: &str, spent: Duration| {
            match timed.iter_mut().find(|(seen, _)| seen == name) {
                Some((_, total)) => *total += spent,
                None => timed.push((name.to_owned(), spent)),
            }
        };
        // A pair whose sides differ in a numeric atom (a relation over
        // sums holding an `ite` the producer rewrote) goes through the
        // atom alignment first; the pair as stated is its fallback.
        let atom_options = crate::checker::RunEgglogOptions {
            descend_min_nodes: options.descend_min_nodes,
            ..sub_options
        };
        if let Descent::Proved(steps) =
            reconstruct_by_atoms(pool, node, &goal, &prefix, rules, atom_options, deadline, &mut accumulate)
        {
            let last = format!("{prefix}.{}", steps.len());
            out.extend(steps);
            return Ok(last);
        }
        let steps =
            reconstruct_subgoal(pool, node, &goal, &prefix, rules, sub_options, deadline, &mut accumulate)
                .map_err(|reason| format!("{reason}; atom goal {n}: {}", abbreviated(&goal)))?;
        let last = format!("{prefix}.{}", steps.len());
        out.extend(steps);
        Ok(last)
    };
    match descend(pool, &lhs, &rhs, id, &mut out, &mut goals, &mut base) {
        Ok(Some(_)) => {
            for (name, total) in timed {
                phase(&name, total);
            }
            eprintln!("phase descent={goals}");
            log::debug!("hole {id}: descent over {goals} atom goals, {} steps", out.len());
            Descent::Proved(out)
        }
        Ok(None) => Descent::NotApplicable,
        Err(reason) => {
            eprintln!("phase descent-failed={:.3}", started.elapsed().as_secs_f64());
            log::debug!("hole {id}: descent failed after {goals} atom goals: {reason}");
            Descent::Failed
        }
    }
}

/// The arithmetic atoms of `term`: the maximal subterms of sort Int or
/// Real that the polynomial view treats as opaque -- a numeric `ite`, an
/// application, `div`, `mod`, `abs`, `to_int` -- in first-occurrence order.
fn arithmetic_atoms(
    pool: &mut dyn TermPool,
    term: &crate::ast::Rc<crate::ast::Term>,
    out: &mut Vec<crate::ast::Rc<crate::ast::Term>>,
) {
    use crate::ast::Operator::*;
    let is_atom = match term.as_ref() {
        crate::ast::Term::App(..) | crate::ast::Term::Op(Ite | IntDiv | Mod | Abs | ToInt, _) => {
            is_numeric(term)
        }
        _ => false,
    };
    if is_atom {
        if !out.contains(term) {
            out.push(term.clone());
        }
        return;
    }
    match term.as_ref() {
        crate::ast::Term::Op(_, args) | crate::ast::Term::App(_, args) => {
            for a in args {
                arithmetic_atoms(pool, a, out);
            }
        }
        _ => {}
    }
}

/// Whether `term` is of sort Int or Real, read off the term itself: an
/// in-process worker's pool need not know the sort of every subterm.
fn is_numeric(term: &crate::ast::Rc<crate::ast::Term>) -> bool {
    use crate::ast::Operator::*;
    let numeric_sort = |sort: &crate::ast::Sort| matches!(sort, crate::ast::Sort::Int | crate::ast::Sort::Real);
    match term.as_ref() {
        crate::ast::Term::Const(crate::ast::Constant::Integer(_) | crate::ast::Constant::Real(_)) => true,
        crate::ast::Term::Var(_, sort) => numeric_sort(sort),
        crate::ast::Term::Op(Add | Sub | Mult | RealDiv | IntDiv | Mod | Abs | ToReal | ToInt, _) => true,
        crate::ast::Term::Op(Ite, args) => args.get(1).is_some_and(is_numeric),
        crate::ast::Term::App(function, _) => match function.as_ref() {
            crate::ast::Term::Var(_, sort) => match sort.as_ref() {
                crate::ast::Sort::Function(sorts) => sorts.last().is_some_and(|s| numeric_sort(s)),
                _ => false,
            },
            _ => false,
        },
        crate::ast::Term::Let(_, body) => is_numeric(body),
        _ => false,
    }
}

/// The atoms one side has and the other lacks, paired across the sides by
/// the leaves they share (most shared first, one partner each); `None`
/// when nothing pairs.
fn atom_pairs(
    pool: &mut dyn TermPool,
    lhs: &crate::ast::Rc<crate::ast::Term>,
    rhs: &crate::ast::Rc<crate::ast::Term>,
) -> Option<Vec<(crate::ast::Rc<crate::ast::Term>, crate::ast::Rc<crate::ast::Term>)>> {
    let mut left = Vec::new();
    arithmetic_atoms(pool, lhs, &mut left);
    let mut right = Vec::new();
    arithmetic_atoms(pool, rhs, &mut right);
    let only_left: Vec<_> = left.iter().filter(|a| !right.contains(a)).cloned().collect();
    let only_right: Vec<_> = right.iter().filter(|a| !left.contains(a)).cloned().collect();
    if only_left.is_empty() || only_right.is_empty() {
        return None;
    }
    let leaf_set = |t: &crate::ast::Rc<crate::ast::Term>| {
        let mut set = std::collections::HashSet::new();
        leaves(t, &mut set);
        set
    };
    let left_leaves: Vec<_> = only_left.iter().map(leaf_set).collect();
    let right_leaves: Vec<_> = only_right.iter().map(leaf_set).collect();
    let mut scored = Vec::new();
    for (i, a) in left_leaves.iter().enumerate() {
        for (j, b) in right_leaves.iter().enumerate() {
            let common = a.intersection(b).count();
            if common > 0 {
                scored.push((common, i, j));
            }
        }
    }
    scored.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(&y.1)).then(x.2.cmp(&y.2)));
    let mut used_left = vec![false; only_left.len()];
    let mut used_right = vec![false; only_right.len()];
    let mut pairs = Vec::new();
    for (_, i, j) in scored {
        if !used_left[i] && !used_right[j] {
            used_left[i] = true;
            used_right[j] = true;
            pairs.push((only_left[i].clone(), only_right[j].clone()));
        }
    }
    (!pairs.is_empty()).then_some(pairs)
}

/// The sides and atom pairs of a goal the atom alignment applies to.
#[allow(clippy::type_complexity)]
fn atom_sides(
    pool: &mut dyn TermPool,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
    options: crate::checker::RunEgglogOptions,
) -> Option<(
    crate::ast::Rc<crate::ast::Term>,
    crate::ast::Rc<crate::ast::Term>,
    Vec<(crate::ast::Rc<crate::ast::Term>, crate::ast::Rc<crate::ast::Term>)>,
)> {
    if options.descend_min_nodes == 0 {
        return None;
    }
    let (_, lhs, rhs) = crate::rare::util::get_equational_terms(conclusion)?;
    let pairs = atom_pairs(pool, lhs, rhs)?;
    Some((lhs.clone(), rhs.clone(), pairs))
}

/// `term` with the atoms of `map` replaced by their partners, and the
/// `cong` steps deriving `(= term rewritten)` from the pairs' steps,
/// numbered under `id` into `out`; `None` when `term` holds none of them.
fn rewrite_atoms(
    pool: &mut dyn TermPool,
    term: &crate::ast::Rc<crate::ast::Term>,
    map: &[(crate::ast::Rc<crate::ast::Term>, crate::ast::Rc<crate::ast::Term>, String)],
    id: &str,
    out: &mut Vec<String>,
) -> Option<(crate::ast::Rc<crate::ast::Term>, String)> {
    if let Some((_, to, step)) = map.iter().find(|(from, _, _)| from == term) {
        return Some((to.clone(), step.clone()));
    }
    let args = match term.as_ref() {
        crate::ast::Term::Op(_, args) | crate::ast::Term::App(_, args) => args,
        _ => return None,
    };
    let mut new_args = Vec::with_capacity(args.len());
    let mut premises = Vec::new();
    for a in args {
        match rewrite_atoms(pool, a, map, id, out) {
            Some((rewritten, step)) => {
                new_args.push(rewritten);
                premises.push(step);
            }
            None => new_args.push(a.clone()),
        }
    }
    if premises.is_empty() {
        return None;
    }
    let rewritten = match term.as_ref() {
        crate::ast::Term::Op(op, _) => crate::ast::Term::Op(*op, new_args),
        crate::ast::Term::App(f, _) => crate::ast::Term::App(f.clone(), new_args),
        _ => unreachable!("an application"),
    };
    let rewritten = pool.add(rewritten);
    let step_id = format!("{id}.{}", out.len() + 1);
    out.push(format!(
        "(step {step_id} (cl (= {term:#} {rewritten:#})) :rule cong :premises ({}))",
        premises.join(" ")
    ));
    Some((rewritten, step_id))
}

/// Reconstructs `(= lhs rhs)` by an atom alignment: the arithmetic atoms
/// one side has and the other lacks (a numeric `ite` the producer rewrote,
/// say) are paired by their leaves and each pair is a goal of its own
/// (`{id}.a{n}`); the left side with the pairs substituted, by `cong`, is
/// then one goal against the right side (`{id}.w`), whose polynomial keys
/// see one atom where the original goal's saw two.  The e-graph computes
/// its keys before its rules union such atoms, so the original goal never
/// meets them.
#[allow(clippy::too_many_arguments)]
fn reconstruct_by_atoms(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
    id: &str,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    deadline: Option<Instant>,
    phase: &mut dyn FnMut(&str, Duration),
) -> Descent {
    let Some((lhs, rhs, pairs)) = atom_sides(pool, conclusion, options) else {
        return Descent::NotApplicable;
    };
    let started = Instant::now();
    // The pairs get three quarters of what is left, each its share (as
    // the descent's pairs), the rewritten goal the rest.
    let pair_deadline = deadline.map(|d| started + d.saturating_duration_since(started) * 3 / 4);
    let mut timed: Vec<(String, Duration)> = Vec::new();
    let mut out = Vec::new();
    let mut map = Vec::new();
    let failed = |started: Instant, reason: String| {
        eprintln!("phase atoms-failed={:.3}", started.elapsed().as_secs_f64());
        log::debug!("hole {id}: atom alignment failed: {reason}");
        Descent::Failed
    };
    for (n, (a, b)) in pairs.iter().enumerate() {
        let remaining = pair_deadline.map(|d| d.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|r| r.is_zero()) {
            return failed(started, "budget exhausted".to_owned());
        }
        let remaining = remaining.map(|r| {
            let left = (pairs.len() - n).max(1) as u32;
            r.min((r / left * 2).max(Duration::from_secs(8)))
        });
        let pair_deadline = remaining.map(|r| Instant::now() + r);
        let prefix = format!("{id}.a{}", n + 1);
        let goal = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![a.clone(), b.clone()],
        ));
        let sub_options = descent_pair_options(options, remaining);
        let mut accumulate = |name: &str, spent: Duration| {
            match timed.iter_mut().find(|(seen, _)| seen == name) {
                Some((_, total)) => *total += spent,
                None => timed.push((name.to_owned(), spent)),
            }
        };
        match reconstruct_subgoal(pool, node, &goal, &prefix, rules, sub_options, pair_deadline, &mut accumulate) {
            Ok(steps) => {
                let last = format!("{prefix}.{}", steps.len());
                out.extend(steps);
                map.push((a.clone(), b.clone(), last));
            }
            Err(reason) => {
                return failed(started, format!("{reason}; atom pair {}: {}", n + 1, abbreviated(&goal)));
            }
        }
    }
    let Some((rewritten, cong_id)) = rewrite_atoms(pool, &lhs, &map, id, &mut out) else {
        return Descent::NotApplicable;
    };
    if rewritten != rhs {
        let remaining = deadline.map(|d| d.saturating_duration_since(Instant::now()));
        let whole = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![rewritten.clone(), rhs.clone()],
        ));
        let prefix = format!("{id}.w");
        let whole_options = crate::checker::RunEgglogOptions {
            timeout: remaining.or(options.timeout),
            descend_min_nodes: 0,
            ..options
        };
        let mut accumulate = |name: &str, spent: Duration| {
            match timed.iter_mut().find(|(seen, _)| seen == name) {
                Some((_, total)) => *total += spent,
                None => timed.push((name.to_owned(), spent)),
            }
        };
        match reconstruct_subgoal(pool, node, &whole, &prefix, rules, whole_options, deadline, &mut accumulate) {
            Ok(steps) => {
                let last = format!("{prefix}.{}", steps.len());
                out.extend(steps);
                let step_id = format!("{id}.{}", out.len() + 1);
                out.push(format!(
                    "(step {step_id} (cl (= {lhs:#} {rhs:#})) :rule trans :premises ({cong_id} {last}))"
                ));
            }
            Err(reason) => {
                return failed(started, format!("{reason}; rewritten goal: {}", abbreviated(&whole)));
            }
        }
    }
    for (name, total) in timed {
        phase(&name, total);
    }
    eprintln!("phase atoms={}", map.len());
    log::debug!("hole {id}: atom alignment over {} pairs, {} steps", map.len(), out.len());
    Descent::Proved(out)
}

/// The checking-only atom alignment: each atom pair checked by egglog on
/// its own, then the left side with the pairs substituted against the
/// right; `None` when it does not apply or a check fails (the whole goal
/// is the fallback).
fn check_by_atoms(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    phase: &mut dyn FnMut(&str, Duration),
) -> Option<Result<(), String>> {
    let (lhs, rhs, pairs) = atom_sides(pool, goal, options)?;
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let started = Instant::now();
    let pair_deadline = deadline.map(|d| started + d.saturating_duration_since(started) / 2);
    let mut map = Vec::new();
    for (n, (a, b)) in pairs.iter().enumerate() {
        let remaining = pair_deadline.map(|d| d.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|r| r.is_zero()) {
            eprintln!("phase atoms-failed={:.3}", started.elapsed().as_secs_f64());
            return None;
        }
        let remaining = remaining.map(|r| {
            let left = (pairs.len() - n).max(1) as u32;
            r.min((r / left * 2).max(Duration::from_secs(8)))
        });
        let pair = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![a.clone(), b.clone()],
        ));
        let prefix = format!("check.a{}", n + 1);
        let sub_options = descent_pair_options(options, remaining);
        if let Err(error) = check_subgoal(pool, node, &pair, &prefix, rules, sub_options, remaining) {
            eprintln!("phase atoms-failed={:.3}", started.elapsed().as_secs_f64());
            log::debug!("atom pair {} not checked: {error}; {}", n + 1, abbreviated(&pair));
            return None;
        }
        map.push((a.clone(), b.clone(), format!("a{}", n + 1)));
    }
    let (rewritten, _) = rewrite_atoms(pool, &lhs, &map, "check", &mut Vec::new())?;
    if rewritten != rhs {
        let remaining = deadline.map(|d| d.saturating_duration_since(Instant::now()));
        let whole = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![rewritten, rhs],
        ));
        let whole_options = crate::checker::RunEgglogOptions {
            timeout: remaining.or(options.timeout),
            descend_min_nodes: 0,
            ..options
        };
        if let Err(error) = check_subgoal(pool, node, &whole, "check.w", rules, whole_options, remaining) {
            eprintln!("phase atoms-failed={:.3}", started.elapsed().as_secs_f64());
            log::debug!("rewritten goal not checked: {error}; {}", abbreviated(&whole));
            return None;
        }
    }
    phase("egglog", started.elapsed());
    eprintln!("phase atoms={}", map.len());
    Some(Ok(()))
}

/// The checking-only descent: every atom pair of the shared skeleton is
/// checked by egglog on its own; `None` when the descent does not apply,
/// `Some(Err)` when a pair is not proved (the whole goal is the fallback).
fn check_by_descent(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    goal: &crate::ast::Rc<crate::ast::Term>,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    phase: &mut dyn FnMut(&str, Duration),
) -> Option<Result<(), String>> {
    let (lhs, rhs) = descent_sides(pool, goal, options)?;
    let deadline = options
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let started = Instant::now();
    // The pairs counted first, for their shares (as in the elaboration).
    let mut pairs = 0usize;
    let mut dry = |_: &mut dyn TermPool,
                   _: &crate::ast::Rc<crate::ast::Term>,
                   _: &crate::ast::Rc<crate::ast::Term>,
                   _: usize,
                   _: &mut Vec<String>|
     -> Result<String, String> {
        pairs += 1;
        Ok(String::new())
    };
    descend(pool, &lhs, &rhs, "check", &mut Vec::new(), &mut 0, &mut dry).ok()?;
    let deadline = deadline.map(|d| started + d.saturating_duration_since(started) * 3 / 4);
    let mut out = Vec::new();
    let mut goals = 0;
    let mut base = |pool: &mut dyn TermPool,
                    a: &crate::ast::Rc<crate::ast::Term>,
                    b: &crate::ast::Rc<crate::ast::Term>,
                    n: usize,
                    _out: &mut Vec<String>|
     -> Result<String, String> {
        let remaining = deadline.map(|d| d.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|r| r.is_zero()) {
            return Err("descent: budget exhausted".to_owned());
        }
        let remaining = remaining.map(|r| {
            let left = (pairs + 1).saturating_sub(n).max(1) as u32;
            r.min((r / left * 2).max(Duration::from_secs(8)))
        });
        let goal = pool.add(crate::ast::Term::Op(
            crate::ast::Operator::Equals,
            vec![a.clone(), b.clone()],
        ));
        let sub_options = descent_pair_options(options, remaining);
        let atom_options = crate::checker::RunEgglogOptions {
            descend_min_nodes: options.descend_min_nodes,
            ..sub_options
        };
        if let Some(Ok(())) = check_by_atoms(pool, node, &goal, rules, atom_options, &mut |_, _| {}) {
            return Ok(format!("d{n}"));
        }
        let prefix = format!("check.d{n}");
        check_subgoal(pool, node, &goal, &prefix, rules, sub_options, remaining)
            .map(|()| format!("d{n}"))
            .map_err(|error| format!("{error}; atom goal {n}: {}", abbreviated(&goal)))
    };
    let verdict = descend(pool, &lhs, &rhs, "check", &mut out, &mut goals, &mut base);
    match verdict {
        Ok(Some(_)) => {
            phase("egglog", started.elapsed());
            eprintln!("phase descent={goals}");
            Some(Ok(()))
        }
        Ok(None) => None,
        Err(reason) => {
            eprintln!("phase descent-failed={:.3}", started.elapsed().as_secs_f64());
            log::debug!("descent failed after {goals} atom goals: {reason}");
            None
        }
    }
}

/// Reconstructs one goal `(= lhs rhs)` through egglog, the snapshot, the
/// certificate search and the Alethe elaboration, the steps numbered under
/// `id`; `deadline` bounds the whole of it.
#[allow(clippy::too_many_arguments)]
fn reconstruct_goal(
    pool: &mut dyn TermPool,
    node: &crate::ast::Rc<ProofNode>,
    conclusion: &crate::ast::Rc<crate::ast::Term>,
    id: &str,
    rules: &Rules,
    options: crate::checker::RunEgglogOptions,
    deadline: Option<Instant>,
    phase: &mut dyn FnMut(&str, Duration),
) -> Result<Vec<String>, String> {
    let stage = |stage: &str, detail: String| format!("{stage}: {detail}");
    let clock = Instant::now();
    let (result, program) = run_egglog(pool, (conclusion.clone(), node), rules, options);
    phase("egglog", clock.elapsed());
    let egraph = result.map_err(|error| stage("egglog check", error))?;
    // Serializing the saturated e-graph is proportional to its size and cannot
    // be interrupted once begun, so a budget already spent stops the hole here
    // rather than paying for a snapshot that has no time left to be searched.
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(stage(
            "egglog check",
            "budget exhausted before the e-graph could be captured".to_owned(),
        ));
    }
    // The copy's cost is proportional to the e-graph, and one saturation
    // iteration can add millions of tuples at once, so the deadline alone does
    // not bound it: an e-graph too large to copy is rejected outright.
    let tuples = egraph.num_tuples();
    if deadline.is_some() && tuples > MAX_SNAPSHOT_TUPLES {
        return Err(stage(
            "egglog check",
            format!("e-graph too large to capture: {tuples} tuples"),
        ));
    }
    // The snapshot's two halves are timed apart: egglog's serialization of
    // the e-graph, then the indexing of what it produced.
    let clock = Instant::now();
    let raw = EGraphSnapshot::serialize_production(&egraph);
    phase("serialize", clock.elapsed());
    let clock = Instant::now();
    let snapshot = EGraphSnapshot::from_raw_nodes(raw);
    phase("index", clock.elapsed());
    let clock = Instant::now();
    let (lhs, rhs) = generated_goals(&program);
    let rewrites = rules_from_generated_program(&program);
    let sorts = ArithSorts::from_generated_program(&program);
    let reconstruction = reconstruct_with_sorts(
        &snapshot,
        &lhs,
        &rhs,
        &rewrites,
        &sorts,
        // A timed search is bounded by its deadline, not by the fixed
        // state count of the default strategy -- and by the goal's size:
        // a candidate vertex is a copy of the goal's term, so the state
        // bound is what fits in a worker's memory for terms of that size.
        if deadline.is_some() {
            SearchStrategy::generous(
                deadline,
                (options.memory_soft_cap_mb > 0).then_some(options.memory_soft_cap_mb),
            )
            .sized_for(term_nodes(&lhs) + term_nodes(&rhs))
        } else {
            SearchStrategy::default()
        },
    );
    phase("search", clock.elapsed());
    let certificate = reconstruction.certificate.ok_or_else(|| {
        stage(
            "reconstruction",
            format!("no certificate found; stats: {:?}", reconstruction.stats),
        )
    })?;
    let clock = Instant::now();
    let names = goal_variable_names(&lhs, &rhs, conclusion);
    let index = rare_arguments(&rules.rules);
    let steps = AletheElaborator::elaborate_in(&certificate, id, names, index, sorts)
        .ok_or_else(|| {
            log::debug!("hole {id}: certificate that failed to elaborate: {certificate:?}");
            stage(
                "alethe elaboration",
                "a certificate term failed to decode".to_owned(),
            )
        });
    phase("emit", clock.elapsed());
    steps
}

/// Elaborates a `TRUST_THEORY_REWRITE` hole through the post-hoc pipeline:
/// the egglog engine proves the rewrite, a certificate is reconstructed from
/// its saturated e-graph, the certificate's Alethe steps are checked against
/// the RARE database, and the checked proof replaces the hole as a subproof
/// — the same insertion an external solver's proof goes through.
pub fn elaborate(
    elaborator: &mut Elaborator,
    node: &crate::ast::Rc<ProofNode>,
    step: &StepNode,
) -> Result<crate::ast::Rc<ProofNode>, ElaborationError> {
    let rules = elaborator.rare_rules.ok_or_else(|| {
        ElaborationError::RareReconstruction("setup: no RARE database was given".to_owned())
    })?;
    let options = elaborator.config.hole_rewrite_options;
    let steps = reconstruct_steps(elaborator.pool, node, step, rules, options)
        .map_err(ElaborationError::RareReconstruction)?;
    insert_steps(elaborator, step, steps)
}

/// Checks the reconstructed steps against the problem and splices them in.
/// Always runs on the proof's own pool: the steps arrive as text precisely so
/// that the terms they mention are interned once, here.
/// Whether `term` holds an `and`/`or` application of one argument.
fn has_singleton_connective(term: &Term) -> bool {
    if let Some((operator, elements)) = encoded_application(term) {
        if (operator == "@and" || operator == "@or") && elements.len() == 1 {
            return true;
        }
    }
    term.children.iter().any(has_singleton_connective)
}

/// The connective of an encoded `and`/`or` side and its identity.
fn aci_connective(term: &Term) -> Option<(&'static str, bool)> {
    match encoded_application(&wrapped(term)) {
        Some(("@and", _)) => Some(("@and", true)),
        Some(("@or", _)) => Some(("@or", false)),
        _ => None,
    }
}

/// One side as Carcara's `aci_simp` reads it: flattened under its own
/// connective, the identity and adjacent duplicates dropped, a single
/// element standing on its own.
fn aci_simp_side(term: &Term) -> Term {
    let side = wrapped(term);
    let Some((operator, identity)) = aci_connective(&side) else {
        return side;
    };
    let mut literals = Vec::new();
    flatten_aci(&side, operator, identity, &mut literals);
    literals.dedup();
    if literals.len() == 1 {
        wrapped(&literals[0])
    } else {
        encoded_app(operator, literals)
    }
}

/// Whether Carcara's `aci_simp` accepts `lhs = rhs`: the two processed
/// sides are applications of one connective with the same multiset of
/// elements, or are equal.
fn aci_simp_accepts(lhs: &Term, rhs: &Term) -> bool {
    let (a, b) = (aci_simp_side(lhs), aci_simp_side(rhs));
    match (encoded_application(&a), encoded_application(&b)) {
        (Some((op1, mut e1)), Some((op2, mut e2)))
            if op1 == op2 && (op1 == "@and" || op1 == "@or") =>
        {
            e1.sort();
            e2.sort();
            e1 == e2
        }
        _ => a == b,
    }
}

/// The rule among `and_simplify`/`or_simplify` that accepts `lhs = rhs` by
/// dropping the identity and duplicates from `lhs`'s direct elements,
/// order kept (Carcara's `generic_and_or_simplify` without the
/// short-circuit case); `None` when it does not.
fn and_or_simplify_accepts(lhs: &Term, rhs: &Term) -> Option<&'static str> {
    let (operator, identity) = aci_connective(lhs)?;
    let rule = if operator == "@and" { "and_simplify" } else { "or_simplify" };
    let (_, mut phis) = encoded_application(&wrapped(lhs))?;
    if phis.len() == 1 {
        if let Some((op, elements)) = encoded_application(&wrapped(&phis[0])) {
            if op == operator {
                phis = elements;
            }
        }
    }
    let result: Vec<Term> = match encoded_application(&wrapped(rhs)) {
        Some((op, elements)) if op == operator => elements,
        _ => vec![rhs.clone()],
    };
    let same = |phis: &[Term], result: &[Term]| {
        phis.len() == result.len() && phis.iter().zip(result).all(|(a, b)| wrapped(a) == wrapped(b))
    };
    phis.retain(|t| bool_value(&wrapped(t)) != Some(identity));
    // Nothing left but the identity: the result is the identity itself.
    if phis.is_empty() {
        return (result.len() == 1 && bool_value(&wrapped(&result[0])) == Some(identity))
            .then_some(rule);
    }
    if same(&phis, &result) {
        return Some(rule);
    }
    let mut seen = std::collections::HashSet::new();
    phis.retain(|t| seen.insert(wrapped(t)));
    same(&phis, &result).then_some(rule)
}

/// Why a goal is one the pipeline does not attempt: it applies a lambda
/// (a `define-fun` the producer printed inlined), whose beta reduction is
/// left to another route.  Tallied `out-of-scope`, as the pivot defect is.
pub fn out_of_scope(term: &crate::ast::Rc<crate::ast::Term>) -> Option<&'static str> {
    fn applies_lambda(term: &crate::ast::Rc<crate::ast::Term>) -> bool {
        match term.as_ref() {
            crate::ast::Term::App(function, args) => {
                matches!(function.as_ref(), crate::ast::Term::Binder(crate::ast::Binder::Lambda, ..))
                    || args.iter().any(applies_lambda)
            }
            crate::ast::Term::Op(_, args) => args.iter().any(applies_lambda),
            crate::ast::Term::Binder(_, _, body) | crate::ast::Term::Let(_, body) => applies_lambda(body),
            _ => false,
        }
    }
    applies_lambda(term)
        .then_some("out of scope: the goal applies a lambda, whose beta reduction is not attempted")
}

/// The class of a residue reason, for the runner's tally: a short tag that
/// names what stopped the hole, read off the reason text at its one log
/// site so the counts do not depend on where in the text the runner's
/// truncation falls.  The specific stops come first: a worker that exits
/// with a status carries the engine's own message in its tail.
pub fn residue_class(reason: &str) -> &'static str {
    if reason.contains("out of scope") {
        "out-of-scope"
    } else if reason.contains("grew past the memory cap") {
        "memory-soft-cap"
    } else if reason.contains("grew past the bound") {
        "growth-cap"
    } else if reason.contains("memory allocation") || reason.contains("out of memory") {
        "memory"
    } else if reason.contains("hole budget ran out") {
        "pass-budget"
    } else if reason.contains("budget exhausted") {
        "hole-time"
    } else if reason.contains("no certificate found") {
        "no-certificate"
    } else if reason.contains("rejected") || reason.contains("checking the reconstructed steps") {
        "checker-rejected"
    } else if reason.contains("egglog check for") || reason.contains("Check failed") {
        // The worker's tail carries egglog's own `Check failed` for a goal
        // it could not prove; the runner tallied that as a worker error.
        "unproved"
    } else if reason.contains("failed to decode") {
        "decode-failed"
    } else if reason.contains("killed by signal 6") || reason.contains("killed by signal 9") {
        "memory"
    } else if reason.contains("killed by signal") {
        "signal"
    } else if reason.contains("exited with status") {
        "worker-error"
    } else {
        "other"
    }
}

pub fn insert_steps(
    elaborator: &mut Elaborator,
    step: &StepNode,
    steps: Vec<String>,
) -> Result<crate::ast::Rc<ProofNode>, ElaborationError> {
    let fail = |stage: &str, detail: String| {
        ElaborationError::RareReconstruction(format!("{stage}: {detail}"))
    };
    let rules = elaborator
        .rare_rules
        .ok_or_else(|| fail("setup", "no RARE database was given".to_owned()))?;
    let [conclusion] = step.clause.as_slice() else {
        return Err(fail(
            "setup",
            format!(
                "expected a single-literal clause, found {} literals",
                step.clause.len()
            ),
        ));
    };

    // `insert_solver_proof` expects a refutation of the negated conclusion,
    // so the equality proof is closed by resolving its last step against
    // that assumption.
    let negated = elaborator.pool.add(crate::ast::Term::Op(
        crate::ast::Operator::Not,
        vec![conclusion.clone()],
    ));
    let problem = hole_problem_string(
        elaborator.pool,
        &elaborator.problem.prelude,
        [conclusion],
        [&negated],
    );
    let assumption = format!("{}.h", step.id);
    let last = format!("{}.{}", step.id, steps.len());
    let proof = format!(
        "(assume {assumption} {negated})\n{}\n(step {}.{} (cl) :rule resolution :premises ({last} {assumption}))\n",
        steps.join("\n"),
        step.id,
        steps.len() + 1,
    );
    log::debug!("hole {}: reconstructed steps:\n{proof}", step.id);
    // A holey inner proof (a relation hole the routing could not discharge)
    // is still accepted: the trusted content strictly decreased.
    let checked = parse_and_check(elaborator.pool, &problem, &proof, rules);
    // A diagnostic: the rejected certificates, one file per hole.
    if checked.is_err() {
        if let Ok(dir) = std::env::var("CARCARA_REJECT_DUMP") {
            let _ = std::fs::write(
                format!("{dir}/{}.rejected", step.id),
                format!("{problem}\n;; --- reconstructed steps\n{proof}"),
            );
        }
    }
    let (commands, _status) =
        checked.map_err(|error| fail("checking the reconstructed steps", error.to_string()))?;
    Ok(external::insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}

/// Parses the reconstructed proof against the problem's prelude and checks it
/// with the RARE database, so its `rare_rewrite` steps resolve.
fn parse_and_check(
    pool: &mut PrimitivePool,
    problem: &str,
    proof: &str,
    rules: &Rules,
) -> Result<(Vec<ProofCommand>, Status), crate::Error> {
    let config = parser::Config::new()
        .expand_lets(true)
        .allow_int_real_subtyping(true)
        .parse_hole_args(true);
    let problem = parser::Source::new(Path::new("<problem for reconstructed rewrite>"), problem);
    let proof = parser::Source::new(Path::new("<reconstructed rewrite proof>"), proof);
    let (problem, proof, _) = parser::parse_instance_with_pool(problem, proof, None, config, pool)?;
    let status =
        checker::ProofChecker::new(pool, rules, checker::Config::new()).check(&problem, &proof)?;
    Ok((proof.commands, status))
}

/// The `rare-list` term of an encoded argument chain: what a `:list`
/// parameter binding several arguments is written as.
fn decode_sequence(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    let elements = list_elements(term)?;
    let decoded = elements
        .iter()
        .map(|element| decode_any(element, names))
        .collect::<Option<Vec<_>>>()?;
    Some(format!("(rare-list {})", decoded.join(" ")))
}

/// The direct arguments of an encoded `and`/`or`, if the term is one.
fn literals_of(term: &Term) -> Option<Vec<Term>> {
    encoded_application(term).map(|(_, elements)| elements)
}

/// The number of direct arguments of an encoded application, wrapped or not.
fn flat_arity(term: &Term) -> usize {
    let wrapped = if term.op == "Mk" {
        term.clone()
    } else {
        Term::new("Mk", vec![term.clone()])
    };
    encoded_application(&wrapped).map_or(0, |(_, elements)| elements.len())
}
