//! Per-rule accounting of how much each reduction grows the proof.
//!
//! A step's reduction replaces one command by a derivation. The interesting number is not the
//! derivation's size on its own but the *net* one: how many commands the proof gained per instance
//! of that input rule, after the sharing pass has had its say. That is what decides whether a rule
//! belongs in the reducible tier, and — over a corpus large enough that the tail matters — which
//! reductions are worth optimizing.
//!
//! The accounting is per *input rule*, since that is the unit a classification decision is about:
//!
//! ```text
//! RULE_GROWTH ite_intro     instances=7  emitted=266 net=259 net_per_instance=37.00 share=59.95
//! RULE_GROWTH equiv1        instances=95 emitted=190 net=95  net_per_instance=1.00  share=21.99
//! RULE_GROWTH th_resolution instances=53 emitted=53  net=0   net_per_instance=0.00  share=0.00
//! ```
//!
//! - **instances** — steps of that rule the pass reduced (a step it left alone is not counted).
//! - **emitted** — *newly built* commands in the derivations it produced, counting a subproof's
//!   body and its anchor. The step's own premises and everything below them are excluded: they
//!   were in the proof already.
//! - **net** — `emitted − instances`: the commands the proof gained. A *rename* has net 0 by
//!   construction, which is exactly why renames are the cheapest reductions in the ladder —
//!   `th_resolution` above is one.
//! - **share of growth** — that rule's net against the *gross* growth (the sum of the positive
//!   nets), so the table ranks by what actually drives a corpus's size rather than by per-instance
//!   cost. The two are very different questions: a 40-step recipe used twice matters less than a
//!   2-step one used a hundred thousand times.
//!
//! A rule can report a **negative** net: its reduction produced fewer new commands than the number
//! of steps it replaced, because the sharing pass folded its derivations together. That is a
//! saving, and it is why shares are normalized by the gross rather than the algebraic total.
//!
//! **Sharing is attributed to the reduction that first built the derivation.** A node is charged
//! once; when the sharing pass replaces a later reduction's output by an earlier identical one,
//! that later instance is charged nothing. So a rule whose derivations are highly repetitive shows
//! a low `net_per_instance`, which is the honest reading — the proof really did not grow for it.
//!
//! Enabled by `CARCARA_RULE_GROWTH=1`; the table is printed once at the end of a run, so a sweep
//! can concatenate the per-file tables and aggregate them.

use crate::ast::*;
use std::collections::HashMap;
use std::sync::Mutex;

/// Per-rule totals: (instances reduced, commands emitted).
static GROWTH: Mutex<Option<HashMap<String, (usize, usize)>>> = Mutex::new(None);

/// The nodes already charged to some rule. A derivation the sharing pass replaces by an earlier
/// identical one is therefore charged once, to the reduction that first built it, and the later
/// uses cost nothing — which is what actually happened to the proof.
static COUNTED: Mutex<Option<std::collections::HashSet<usize>>> = Mutex::new(None);

/// Whether the accounting is on. Checked once per reduction, so it stays a cheap env lookup behind
/// a `OnceLock`.
fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("CARCARA_RULE_GROWTH").is_some())
}

/// Records one reduction: `step` was replaced by the derivation rooted at `node`.
///
/// Only *newly built* commands are charged. Three things are therefore not counted: the step's own
/// premises and anything below them (they were in the proof already), nodes at a smaller depth
/// (likewise), and nodes an earlier reduction already paid for (the sharing case).
pub(super) fn record(step: &StepNode, node: &Rc<ProofNode>) {
    if !enabled() {
        return;
    }
    let boundary: std::collections::HashSet<usize> = step
        .premises
        .iter()
        .chain(&step.discharge)
        .chain(&step.previous_step)
        .map(|p| Rc::as_ptr(p) as usize)
        .collect();

    let mut counted_guard = COUNTED.lock().unwrap();
    let counted = counted_guard.get_or_insert_with(std::collections::HashSet::new);

    let depth = node.depth();
    let mut local: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut todo = vec![node.clone()];
    let mut emitted = 0;
    while let Some(current) = todo.pop() {
        let key = Rc::as_ptr(&current) as usize;
        if current.depth() < depth || boundary.contains(&key) || !local.insert(key) {
            continue;
        }
        let fresh = counted.insert(key);
        if fresh {
            emitted += 1;
        }
        match current.as_ref() {
            ProofNode::Step(s) => todo.extend(
                s.premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .cloned(),
            ),
            ProofNode::Subproof(s) => {
                if fresh {
                    // the anchor
                    emitted += 1;
                }
                todo.push(s.last_step.clone());
                todo.extend(s.extra_steps.iter().chain(&s.outbound_premises).cloned());
            }
            ProofNode::Assume { .. } => (),
        }
    }
    drop(counted_guard);

    let mut guard = GROWTH.lock().unwrap();
    let map = guard.get_or_insert_with(HashMap::new);
    let entry = map.entry(step.rule.clone()).or_default();
    entry.0 += 1;
    entry.1 += emitted;
}

/// Prints the per-rule growth table collected during the run, if any.
///
/// The format is one `RULE_GROWTH` line per rule so that a sweep over many files can concatenate
/// and aggregate them without parsing a table layout.
pub fn report() {
    let guard = GROWTH.lock().unwrap();
    let Some(map) = guard.as_ref() else {
        return;
    };
    // Shares are taken against the *gross* growth — the sum of the positive nets — because a rule
    // can have a negative net: a reduction whose derivations the sharing pass folds together
    // produces fewer new commands than the steps it replaced, and that is a saving, not a share of
    // the growth. Normalizing by the algebraic total would let those savings inflate everyone
    // else's percentage past 100
    let gross: i64 = map
        .values()
        .map(|(i, e)| *e as i64 - *i as i64)
        .filter(|net| *net > 0)
        .sum();
    let total: i64 = map.values().map(|(i, e)| *e as i64 - *i as i64).sum();
    let mut rows: Vec<_> = map
        .iter()
        .map(|(rule, (i, e))| (rule, *i, *e, *e as i64 - *i as i64))
        .collect();
    rows.sort_by_key(|(rule, _, _, net)| (std::cmp::Reverse(*net), (*rule).clone()));
    for (rule, instances, emitted, net) in rows {
        let share = if gross > 0 {
            100.0 * net as f64 / gross as f64
        } else {
            0.0
        };
        println!(
            "RULE_GROWTH {rule} instances={instances} emitted={emitted} net={net} \
             net_per_instance={:.2} share={share:.2}",
            net as f64 / instances.max(1) as f64,
        );
    }
    println!("RULE_GROWTH TOTAL net={total} gross={gross}");
}
