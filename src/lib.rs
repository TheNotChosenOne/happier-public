//! A SAT solver.
//!
//! `SATState::satisfiable` answers whether a solution exists
//! `SATState::can_pos` answers which variables can be true in *some* solution

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "unchecked"), forbid(unsafe_code))]

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

use alloc::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "serde")]
use bincode::{Decode, Encode};
#[cfg(feature = "contracts")]
use contracts::{debug_ensures as ensures, debug_requires as requires};

#[macro_use]
mod trace;

mod assign;
mod bitvec;
mod clause;
mod debug_fmt;
pub mod dedup;
mod guess;
mod guess_select;
#[cfg(feature = "contracts")]
mod invariants;
mod learn;
mod store;
#[cfg_attr(not(feature = "unchecked"), path = "checked.rs")]
mod unchecked;
use bitvec::BitVec;
pub use clause::{Clause, Clauseish, CowClause};
use clause::{DualClauses, SoloClauses};
use guess::{AssignmentLedger, AssignmentReason, UndoableGuess, active_ledger, active_ledger_len};
use guess_select::{potential_guess, potential_unguess};
#[cfg(feature = "contracts")]
use invariants::CowClauseInvariants;
use store::{ClauseList, ClauseStore, DesatisfyStack};
use unchecked::{
    unchecked_err, unchecked_find_swap, unchecked_get, unchecked_mut, unchecked_ok,
    unchecked_remove, unchecked_shift_left, unchecked_shift_right, unchecked_split,
    unchecked_unwrap,
};

#[cfg(feature = "trace")]
use core::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "trace")]
static STATS_GUESSES: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "trace")]
static STATS_HINTED_GUESSES: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "trace")]
static STATS_ROLLBACKS: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "trace")]
static STATS_ASSIGNMENTS: AtomicU64 = AtomicU64::new(0);

const GUESS_HINTS: bool = false;

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal(u32);

impl core::fmt::Debug for Literal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_true() {
            write!(f, "{}", self.var_index())
        } else {
            write!(f, "¬{}", self.var_index())
        }
    }
}

impl Literal {
    #[inline(always)]
    pub fn variable(self) -> Variable {
        let var_index = self.0 >> 1;
        Variable(var_index)
    }

    #[inline(always)]
    pub fn lit_index(self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    pub fn var_index(self) -> usize {
        self.variable().index()
    }

    #[inline(always)]
    pub fn matching(self, value: bool) -> bool {
        if value {
            (self.0 & 1) == 1
        } else {
            (self.0 & 1) == 0
        }
    }

    #[inline(always)]
    pub fn is_true(self) -> bool {
        self.0 & 1 != 0
    }

    #[inline(always)]
    pub fn is_false(self) -> bool {
        self.0 & 1 == 0
    }

    pub fn negate(self) -> Literal {
        Literal(self.0 ^ 1)
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(u32);

impl Variable {
    #[cfg_attr(feature = "contracts", requires(index < (1 << 31)))]
    pub fn new(index: u32) -> Self {
        Self(index)
    }

    #[cfg_attr(feature = "contracts", ensures(ret.variable() == self))]
    #[cfg_attr(feature = "contracts", ensures(ret.is_true()))]
    #[inline(always)]
    pub fn literal_pos(self) -> Literal {
        Literal(self.0 << 1 | 1)
    }

    #[cfg_attr(feature = "contracts", ensures(ret.variable() == self))]
    #[cfg_attr(feature = "contracts", ensures(ret.is_false()))]
    #[inline(always)]
    pub fn literal_neg(self) -> Literal {
        Literal(self.0 << 1)
    }

    #[inline(always)]
    pub fn index(&self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    pub fn literal_both(self) -> (Literal, Literal) {
        let base = self.0 << 1;
        (Literal(base | 1), Literal(base))
    }

    #[inline(always)]
    pub fn literal(self, value: bool) -> Literal {
        if value {
            self.literal_pos()
        } else {
            self.literal_neg()
        }
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, PartialEq, Eq)]
pub struct SATState {
    solos: SoloClauses,
    duals: DualClauses,

    store: ClauseStore,

    desatisfy_stack: DesatisfyStack,
    #[cfg(debug_assertions)]
    assign_order: Vec<Literal>,

    big_clause_set: BTreeSet<Vec<Literal>>,

    assignments: Vec<Option<bool>>,

    unassigned: usize,
    done: bool,
    presolved_contradiction: Option<ContradictionReason>,
    active_contradiction: Vec<ContradictionReason>,
    unsatisfiable: bool,
    presolved: bool,
    not_a_guess: AssignmentLedger,

    next_clause_guess_var: Option<Variable>,

    guess_hints: BTreeMap<Variable, Vec<Option<bool>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Control {
    Continue,
    Stop,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    Continue,
    TopLevel,
    Forced,
    Ready,
}

impl Step {
    #[cfg(feature = "trace")]
    fn rolled_back(self) -> bool {
        matches!(self, Step::Continue | Step::Forced)
    }
}

pub fn just_satisfiable(_: &SATState) -> Control {
    Control::Stop
}

pub fn tour_all_solutions(_: &SATState) -> Control {
    Control::Continue
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContradictionReason {
    ForcedLiteral(Literal),
    Clause(u32),
    DualContradiction(Literal, Literal),
    ForcedDual(Literal),
    Blocked(Variable),
}

impl Default for SATState {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(debug_assertions)]
impl Drop for SATState {
    fn drop(&mut self) {
        self.not_a_guess.mark_rolled_back();
    }
}

#[cfg(debug_assertions)]
pub(crate) fn validate_unassignment(
    assignments: &mut [Option<bool>],
    order: &mut Vec<Literal>,
    var: Variable,
) {
    let value = assignments[var.index()];
    debug_assert!(value.is_some());
    let value = value.unwrap();
    debug_assert!(!order.is_empty());
    let last = order.pop().unwrap();
    debug_assert_eq!(last, var.literal(value), "unassigned out of order");
}

#[cfg(debug_assertions)]
pub(crate) fn record_assignment(
    assignments: &mut [Option<bool>],
    order: &mut Vec<Literal>,
    var: Variable,
    value: bool,
) {
    let lit = var.literal(value);
    debug_assert!(!order.contains(&lit));
    debug_assert!(!order.contains(&lit.negate()));
    debug_assert_eq!(assignments[var.index()], Some(value));
    order.push(lit);
}

impl SATState {
    pub fn new() -> Self {
        Self {
            solos: SoloClauses::new(),
            duals: DualClauses::new(),
            store: ClauseStore::new(),
            desatisfy_stack: DesatisfyStack::new(),
            #[cfg(debug_assertions)]
            assign_order: Vec::with_capacity(256),
            big_clause_set: BTreeSet::new(),
            assignments: Vec::with_capacity(256),
            unassigned: 0,
            done: false,
            active_contradiction: Vec::new(),
            presolved_contradiction: None,
            unsatisfiable: false,
            presolved: false,
            not_a_guess: AssignmentLedger::empty(),
            next_clause_guess_var: None,
            guess_hints: BTreeMap::new(),
        }
    }

    pub fn max_known_variable(&self) -> Option<Variable> {
        if self.assignments.is_empty() {
            None
        } else {
            Some(Variable((self.assignments.len() - 1) as u32))
        }
    }

    pub fn variable_count(&self) -> usize {
        self.assignments.len()
    }

    pub fn assignments(&self) -> &[Option<bool>] {
        &self.assignments
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_tracking(), "unassigned invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking(), "unassigned invariant holds"))]
    pub fn new_variable(&mut self) -> Variable {
        let var_index = self.assignments.len() as u32;
        self.assignments.push(None);
        self.store.usages.push(ClauseList::new());
        self.store.clause_presence.push(0);
        debug_assert_eq!(self.assignments.len(), self.store.usages.len());
        self.unassigned += 1;
        self.duals.add_one();

        Variable(var_index)
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_tracking(), "unassigned invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking(), "unassigned invariant holds"))]
    pub fn new_variable_at(&mut self, index: usize) -> Variable {
        if index >= self.assignments.len() {
            let increase = index - self.assignments.len() + 1;
            self.assignments.resize(index + 1, None);
            self.store.usages.resize(index + 1, ClauseList::new());
            self.store.clause_presence.resize(index + 1, 0);
            self.duals.add_n(increase);
            debug_assert_eq!(self.assignments.len(), self.store.usages.len());
            self.unassigned += increase;
        }
        Variable(index as u32)
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(!self.presolved))]
    #[cfg_attr(feature = "contracts", ensures(self.presolved_contradiction == old(self.presolved_contradiction) || self.invariant_has_contradiction()))]
    #[cfg_attr(feature = "contracts", ensures(!self.done))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unit_indexes_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_all_variables_accounted_for()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_per_variable_state()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    pub fn add_clause(&mut self, clause: impl CowClause) {
        debug_assert!(self.not_a_guess.is_empty() || self.done);
        if self.done {
            self.unroll();
        }
        debug_assert!(self.not_a_guess.is_empty());

        let max_var = clause.max_var();
        self.new_variable_at(max_var.0 as usize);
        let _index = self.internal_add_clause(clause);
        #[cfg(debug_assertions)]
        #[cfg(feature = "contracts")]
        if let Some(Some(resolved)) = _index {
            debug_assert!(self.clause_slice(resolved).invariant_well_formed_input());
        }
        self.done = false;
        self.presolved = false;

        debug_assert!(self.not_a_guess.is_empty());
    }

    fn add_learned_clause(&mut self, clause: impl CowClause) -> Option<Option<u32>> {
        debug_assert!(
            (clause.max_var().0 as usize) < self.assignments.len(),
            "learned clause introduced a new variable"
        );
        debug_assert!(self.active_contradiction.is_empty());
        debug_assert!(!self.done);

        self.internal_add_clause(clause)
    }

    fn internal_add_clause(&mut self, clause: impl CowClause) -> Option<Option<u32>> {
        if clause.is_empty() {
            None
        } else if 1 == clause.len() {
            let literal = clause.get_literal(0);
            if let Some(new) = self.solos.insert(literal) {
                if let Some(contradiction) = new {
                    self.active_contradiction.push(contradiction);
                }
                Some(None)
            } else {
                None
            }
        } else if 2 == clause.len() {
            let lita = clause.get_literal(0);
            let litb = clause.get_literal(1);
            if lita.variable() == litb.variable() {
                if lita != litb {
                    return None;
                } else {
                    return self.internal_add_clause(&[lita][..]);
                }
            }
            if self.duals.expand_implication_graph(
                &mut self.solos,
                lita,
                litb,
                &self.assignments,
                &mut self.active_contradiction,
            ) {
                Some(None)
            } else {
                None
            }
        } else {
            let mut clause = clause.to_owned();
            clause.sort_unstable();
            clause.dedup();
            for i in 1..clause.len() {
                if clause[i].variable() == clause[i - 1].variable() {
                    return None;
                }
            }
            if clause.len() < 3 {
                return self.internal_add_clause(clause);
            }

            match self.big_clause_set.get(&clause) {
                Some(_) => return None,
                None => {
                    self.big_clause_set.insert(clause.clone());
                }
            }
            let mut clause = Clause::new(clause, &self.assignments);

            if self.store.clauses.contains(&clause) {
                return None;
            }

            let clause_index = self.store.clauses.len() as u32;

            self.store
                .unit_indices
                .max_entries(self.store.clauses.len() + 1);
            self.desatisfy_stack
                .stacked
                .resize(self.store.clauses.len() + 1);
            self.store
                .unsatisfied_clauses
                .resize(self.store.clauses.len() + 1);

            if 0 == clause.satisfying_count() {
                if clause.has_one_unassigned() {
                    self.store.unit_indices.insert(clause_index);
                }
                self.store.mark_unsatisfied(clause_index);

                for &lit in &clause.literals {
                    let index = lit.var_index();
                    self.store.usages[index].insert(clause_index);
                    self.store.clause_presence[index] += 1;
                    let var = Variable(index as u32);
                    potential_guess(
                        &self.assignments,
                        &self.store.clause_presence,
                        &mut self.next_clause_guess_var,
                        var,
                    );
                }
            } else {
                self.desatisfy_stack
                    .retroactive_one(clause_index, &mut clause, &self.assignments);
            }
            if clause.definitely_contradictory() {
                self.active_contradiction
                    .push(ContradictionReason::Clause(clause_index));
            }
            self.store.clauses.push(clause);
            Some(Some(clause_index))
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for(), "all variables invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg(feature = "std")]
    pub fn analyze_problem(&self) {
        if true {
            return;
        }
        let total_variables = self.assignments.len();
        let total_clauses = self.store.clauses.len();
        let mut var_connections = vec![0; total_variables];

        println!("=== Problem Analysis ===");
        println!("Self: {self:?}");
        println!("Variables: {}", total_variables);
        println!(
            "Assigned/Unassigned: {} / {}",
            total_variables - self.unassigned,
            self.unassigned
        );
        println!("Clauses: {}", total_clauses,);
        println!("Forced: {}", self.solos.forced_assignments.len());

        println!(
            "Implications: {}",
            self.duals
                .implication_graph
                .iter()
                .map(|v| v.len())
                .sum::<usize>()
        );

        if 0 == total_clauses || 0 == total_variables {
            println!("========================");
            return;
        }

        for clause in &self.store.clauses {
            for lit in clause.dyn_iter_all() {
                var_connections[lit.var_index()] += 1;
            }
        }

        println!(
            "Unused variables: {}",
            var_connections.iter().filter(|&&c| c == 0).count()
        );

        var_connections.sort_unstable();
        let total_connections: usize = var_connections.iter().sum();
        let mean = total_connections as f64 / total_variables as f64;

        let variance = var_connections
            .iter()
            .map(|&x| (x as f64 - mean).powi(2))
            .sum::<f64>()
            / total_variables as f64;
        println!("Mean variable connections: {:.2}", mean);
        println!(
            "Max variable connections: {}",
            var_connections.last().unwrap()
        );
        println!(
            "Min variable connections: {}",
            var_connections.first().unwrap()
        );
        println!(
            "Median variable connections: {:.2}",
            var_connections[var_connections.len() / 2]
        );
        let p25 = var_connections[total_variables / 4];
        let p75 = var_connections[(total_variables * 3) / 4];
        println!("25th percentile variable connections: {}", p25);
        println!("75th percentile variable connections: {}", p75);
        let structure_ratio = if mean > 0.0 { variance / mean } else { 0.0 };

        if !self.store.clauses.is_empty() {
            let mut big_clause_sizes: Vec<usize> = self
                .store
                .clauses
                .iter()
                .map(|c| c.literals.len())
                .collect();
            big_clause_sizes.sort_unstable();
            let avg_clause_size =
                big_clause_sizes.iter().sum::<usize>() as f64 / self.store.clauses.len() as f64;
            println!("Average big clause size: {:.2}", avg_clause_size);
            let max_clause_size = big_clause_sizes.last().unwrap();
            println!("Max big clause size: {}", max_clause_size);
            let min_clause_size = big_clause_sizes.first().unwrap();
            println!("Min big clause size: {}", min_clause_size);
            let median_clause_size = big_clause_sizes[big_clause_sizes.len() / 2];
            println!("Median big clause size: {}", median_clause_size);
            let p25_clause_size = big_clause_sizes[self.store.clauses.len() / 4];
            let p75_clause_size = big_clause_sizes[(self.store.clauses.len() * 3) / 4];
            println!("25th percentile big clause size: {}", p25_clause_size);
            println!("75th percentile big clause size: {}", p75_clause_size);
        }

        let structure_level = if structure_ratio > mean * 0.5 {
            "High"
        } else if structure_ratio > mean * 0.2 {
            "Medium"
        } else {
            "Low"
        };
        println!(
            "Structure level: {} (ratio: {:.3}, mean connections: {:.2})",
            structure_level, structure_ratio, mean
        );
        println!("========================");
    }

    pub fn iter_all_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.store.clauses.iter()
    }

    #[cfg_attr(feature = "contracts", ensures(!matches!(ret, Step::Ready) || self.active_contradiction.is_empty()))]
    #[inline(always)]
    fn handle_conflict(
        &mut self,
        guesses: &mut Vec<UndoableGuess>,
        on_learn: impl FnOnce(&mut Vec<UndoableGuess>),
    ) -> Step {
        let Some(reason) = self.active_contradiction.last().cloned() else {
            return Step::Ready;
        };
        let Some(guess) = guesses.pop() else {
            self.done = true;
            trace_flow!("contradiction at top level: {reason:?}");
            return Step::TopLevel;
        };
        if self.learn_and_backtrack(guesses, guess, reason) {
            on_learn(guesses);
            if !self.solos.forced_contradictions.is_empty()
                || !self.duals.forced_contradictions.is_empty()
            {
                return Step::Forced;
            }
        }
        Step::Continue
    }

    #[cfg_attr(feature = "contracts", ensures(!matches!(ret, Step::Ready) || self.active_contradiction.is_empty()))]
    #[inline(always)]
    fn propagate(&mut self, guesses: &mut [UndoableGuess]) -> Step {
        let Some(change_contradiction) = self.assign_forced(guesses) else {
            return Step::Ready;
        };
        if let Some(reason) = change_contradiction {
            self.active_contradiction.push(reason);
        }
        Step::Continue
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.assignments[guess.variable.index()].is_some()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_frame_owns_contradictions(&guess)))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    fn rollback_guess(&mut self, mut guess: UndoableGuess, guesses: &mut [UndoableGuess]) {
        trace_flow!(
            "rollback guess: {:?}={}",
            guess.variable,
            unchecked_unwrap(self.assignments[guess.variable.index()])
        );
        guess.mark_rolled_back();
        for (var, _) in guess.rollback_drain() {
            trace_assign!("rollback unassignment: {var:?}");
            self.make_unassignment(var);
        }
        let next_guess = !unchecked_unwrap(self.assignments[guess.variable.index()]);
        trace_assign!("rollback reassignment: {:?}={}", guess.variable, next_guess);

        let assigning = guess.variable.literal(next_guess);
        if let Some(contra) = self
            .duals
            .reassignment_will_contradict(&self.assignments, assigning)
        {
            self.active_contradiction
                .push(ContradictionReason::DualContradiction(assigning, contra));
            let prev = active_ledger(guesses, &mut self.not_a_guess);
            prev.push_assignment(guess.variable, AssignmentReason::Guess(assigning.negate()));
            return;
        }

        let mut pseudo_guess = AssignmentLedger::empty();
        pseudo_guess.push_assignment(guess.variable, AssignmentReason::Guess(assigning.negate()));
        if let Some(contradiction_index) =
            self.make_reassignment(guess.variable, next_guess, &mut pseudo_guess)
        {
            self.active_contradiction
                .push(ContradictionReason::Clause(contradiction_index));
        } else {
            self.active_contradiction.clear();
            #[cfg(feature = "contracts")]
            debug_assert!(self.invariant_no_contradiction());
        }
        let prev = active_ledger(guesses, &mut self.not_a_guess);
        prev.consume_assignments(pseudo_guess);
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_no_contradiction()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    fn rollback_guess_completely(&mut self, mut guess: UndoableGuess) {
        trace_flow!(
            "rollback guess completely: {:?}={}",
            guess.variable,
            unchecked_unwrap(self.assignments[guess.variable.index()])
        );
        guess.mark_rolled_back();
        for (var, _) in guess.rollback_drain() {
            trace_assign!("complete rollback unassignment: {var:?}");
            self.make_unassignment(var);
        }
        trace_assign!("complete rollback unassignment: {:?}", guess.variable);
        self.make_unassignment(guess.variable);
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_all_variables_accounted_for()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_per_variable_state()))]
    /// Returns false if single/dual variable clauses are unsatisfiable
    ///
    /// Called automatically by `satisfiable` and `can_pos`.
    pub fn presolve(&mut self) -> bool {
        if !self.solos.forced_contradictions.is_empty() {
            return false;
        }
        if !self.duals.forced_contradictions.is_empty() {
            return false;
        }
        if self.presolved || self.done {
            return self.active_contradiction.is_empty();
        }
        debug_assert!(self.not_a_guess.is_empty());
        self.presolved = true;

        debug_assert!(self.not_a_guess.is_empty());

        let mut must_assign = BTreeSet::new();
        for &unit in &self.solos.forced_assignments {
            must_assign.insert(unit);
            for &implied in self.duals.implication_graph[unit.lit_index()].iter() {
                must_assign.insert(implied);
            }
        }
        debug_assert!(self.not_a_guess.is_empty());

        for &assignment in &must_assign {
            if must_assign.contains(&assignment.negate()) {
                self.active_contradiction
                    .push(ContradictionReason::DualContradiction(
                        assignment,
                        assignment.negate(),
                    ));
                self.presolved_contradiction = Some(*self.active_contradiction.last().unwrap());
                debug_assert!(self.not_a_guess.is_empty());
                return false;
            }

            if let Some(assigned) = self.assignments[assignment.var_index()]
                && !assignment.matching(assigned)
            {
                self.active_contradiction
                    .push(ContradictionReason::ForcedLiteral(assignment));
                self.presolved_contradiction = Some(*self.active_contradiction.last().unwrap());
                debug_assert!(self.not_a_guess.is_empty());
                return false;
            }
        }
        debug_assert!(self.not_a_guess.is_empty());

        for assignment in must_assign {
            debug_assert!(self.not_a_guess.is_empty());
            if self.assignments[assignment.var_index()].is_some() {
                continue;
            }

            if let Some(contradiction) = self
                .duals
                .assignment_will_contradict(&self.assignments, assignment)
            {
                self.active_contradiction
                    .push(ContradictionReason::DualContradiction(
                        assignment,
                        contradiction,
                    ));
                self.presolved_contradiction = Some(*self.active_contradiction.last().unwrap());
                debug_assert!(self.not_a_guess.is_empty());
                return false;
            }
            debug_assert!(self.not_a_guess.is_empty());
            if let Some(contradiction) = Self::make_assign_one(
                assignment,
                &mut self.store,
                &mut self.assignments,
                #[cfg(debug_assertions)]
                &mut self.assign_order,
                &mut self.unassigned,
                &mut self.duals,
                &mut self.desatisfy_stack,
                &mut self.next_clause_guess_var,
            ) {
                self.active_contradiction
                    .push(ContradictionReason::Clause(contradiction));
                self.presolved_contradiction = Some(*self.active_contradiction.last().unwrap());
                debug_assert!(self.not_a_guess.is_empty());
                return false;
            }
            debug_assert!(self.not_a_guess.is_empty());
        }

        debug_assert!(self.not_a_guess.is_empty());
        while let Some(opt_contradiction) = self.assign_forced(&mut []) {
            self.not_a_guess.clear();
            if let Some(contradiction_index) = opt_contradiction {
                self.active_contradiction.push(contradiction_index);
                self.presolved_contradiction = Some(*self.active_contradiction.last().unwrap());
                debug_assert!(self.not_a_guess.is_empty());
                return false;
            }
            continue;
        }
        self.not_a_guess.clear();
        debug_assert!(self.not_a_guess.is_empty());

        true
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state()))]
    #[cfg_attr(feature = "contracts", ensures(!self.done))]
    #[cfg_attr(feature = "contracts", ensures(self.presolved))]
    #[cfg_attr(feature = "contracts", ensures(self.not_a_guess.is_empty()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    /// Undoes any active search,
    /// to make ready for a new search with potentially modified clauses
    ///
    /// Called automatically by `satisfiable` and `can_pos` when re-solving.
    pub fn unroll(&mut self) {
        self.done = false;
        self.presolved = true;
        let mut assignments = AssignmentLedger::empty();
        core::mem::swap(&mut assignments, &mut self.not_a_guess);
        assignments.mark_rolled_back();
        for (assignment, _) in assignments.rollback_drain() {
            trace_assign!("unroll unassignment: {assignment:?}");
            self.make_unassignment(assignment);
        }
        self.active_contradiction.clear();
        if let Some(pre) = self.presolved_contradiction {
            self.active_contradiction.push(pre);
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for(), "all variables invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", requires(range.start <= range.end))]
    #[cfg_attr(feature = "contracts", requires(range.end <= self.assignments.len()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(ret.len() == old(range.end - range.start)))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    /// Which variables in `range` are true in at least one solution.
    ///
    /// `range` identifies 0-based variable indices
    /// returned vec is the size of the range
    pub fn can_pos(&mut self, range: core::ops::Range<usize>) -> Vec<bool> {
        self.sat_header();

        let mut output = vec![false; range.end - range.start];
        if self.unsatisfiable {
            return output;
        }
        if !self.solos.forced_contradictions.is_empty() {
            return output;
        }
        if !self.duals.forced_contradictions.is_empty() {
            return output;
        }

        let mut guesses: Vec<UndoableGuess> = Vec::new();
        #[cfg(feature = "trace")]
        let mut guess_count = 0;
        #[cfg(feature = "trace")]
        let mut hinted_guess_count = 0;
        #[cfg(feature = "trace")]
        let mut backtrack_count = 0;
        #[cfg(feature = "trace")]
        let mut learned_count = 0;

        let mut next_guess = 0;
        let mut any_satisfying = false;
        let mut top_level_probe: Option<usize> = None;

        #[cfg(feature = "trace")]
        let mut iteration = 0;

        #[cfg(feature = "trace")]
        let mut stuck = false;
        #[cfg(not(feature = "trace"))]
        #[allow(non_upper_case_globals)]
        const stuck: bool = false;

        loop {
            #[cfg(feature = "trace")]
            {
                iteration += 1;
                if iteration > 1_000_000 && guesses.is_empty() {
                    stuck = true;
                }
            }
            let step = self.handle_conflict(&mut guesses, |guesses| {
                #[cfg(feature = "trace")]
                {
                    learned_count += 1;
                }
                if guesses.is_empty()
                    && let Some(probe) = top_level_probe.take()
                {
                    next_guess = next_guess.min(probe);
                }
            });
            #[cfg(feature = "trace")]
            if step.rolled_back() {
                backtrack_count += 1;
            }
            match step {
                Step::Continue => continue,
                Step::TopLevel | Step::Forced => break,
                Step::Ready => {}
            }

            match self.propagate(&mut guesses) {
                Step::Continue => continue,
                Step::TopLevel | Step::Forced => break,
                Step::Ready => {}
            }

            if self.store.unsatisfied > 0 {
                let var_to_guess = if guesses.is_empty() {
                    let next_pos = output
                        .iter()
                        .enumerate()
                        .skip(next_guess)
                        .position(|(i, &b)| !b && self.assignments[range.start + i].is_none());
                    if let Some(pos) = next_pos {
                        next_guess += pos;
                        let index = next_guess + range.start;
                        next_guess += 1;
                        top_level_probe = Some(next_guess - 1);
                        debug_assert!(self.assignments[index].is_none());
                        if stuck {
                            trace_flow!("C");
                        }
                        Some(Variable(index as u32))
                    } else if !any_satisfying {
                        if stuck {
                            trace_flow!("D");
                        }
                        self.select_next_guess()
                    } else {
                        if stuck {
                            trace_flow!("no more top level guesses required");
                        }
                        break;
                    }
                } else {
                    let mut next_guess = None;
                    for (i, out) in output.iter().enumerate() {
                        if !out
                            && self.assignments[range.start + i].is_none()
                            && self.duals.possible_assignments[range.start + i].can_be_pos()
                        {
                            next_guess = Some(Variable((range.start + i) as u32));
                            break;
                        }
                    }
                    if let Some(next) = next_guess {
                        if stuck {
                            trace_flow!("B");
                        }
                        Some(next)
                    } else {
                        if stuck {
                            trace_flow!("A");
                        }
                        self.select_next_guess()
                    }
                };

                if let Some(var) = var_to_guess {
                    if !self.duals.possible_assignments[var.index()].allows_any() {
                        self.active_contradiction
                            .push(ContradictionReason::Blocked(var));
                        continue;
                    }
                    #[cfg(feature = "trace")]
                    {
                        guess_count += 1;
                    }
                    let mut guessing;
                    let mut undoable = UndoableGuess::new(var);

                    guessing = self.duals.possible_assignments[var.index()].any();
                    if range.start <= var.index()
                        && var.index() < range.end
                        && GUESS_HINTS
                        && let Some(new_guess) = self.hinted_guess(range.clone(), &output, var)
                    {
                        #[cfg(feature = "trace")]
                        {
                            hinted_guess_count += 1;
                        }
                        guessing = !new_guess;
                    }

                    debug_assert!(
                        self.duals
                            .assignment_will_contradict(&self.assignments, var.literal(guessing))
                            .is_none()
                    );

                    if stuck {
                        trace_flow!(
                            "guess: {var:?}={guessing} / {}, previous forced {}",
                            guesses.len(),
                            active_ledger_len(&guesses, &self.not_a_guess)
                        );
                    } else {
                        trace_assign!(
                            "guess: {var:?}={guessing} / {}, previous forced {}",
                            guesses.len(),
                            active_ledger_len(&guesses, &self.not_a_guess)
                        );
                    }
                    debug_assert!(self.active_contradiction.is_empty());
                    if let Some(contradiction_index) =
                        self.make_assignment_with_implications(var, guessing, &mut undoable)
                    {
                        self.active_contradiction
                            .push(ContradictionReason::Clause(contradiction_index));
                    }
                    guesses.push(undoable);
                    continue;
                }
            }

            debug_assert!(self.active_contradiction.is_empty());

            debug_assert!(
                (0..self.assignments.len())
                    .all(|i| self.assignments[i].is_some() || self.store.clause_presence[i] == 0)
            );

            #[cfg(feature = "contracts")]
            debug_assert!(self.invariant_solution_satisfies_all());

            any_satisfying = true;
            #[cfg(feature = "trace")]
            let mut output_count = 0;
            for i in range.clone() {
                let credit = self.assignments[i]
                    .unwrap_or_else(|| self.duals.possible_assignments[i].can_be_pos());
                if credit && !output[i - range.start] {
                    if stuck {
                        trace_flow!("setting output {} to true", i);
                    }
                    output[i - range.start] = true;
                    #[cfg(feature = "trace")]
                    {
                        output_count += 1;
                    }
                    if GUESS_HINTS {
                        if let Some(hints) = self.guess_hints.get(&Variable(i as u32)) {
                            if hints != &self.assignments {
                                self.guess_hints
                                    .insert(Variable(i as u32), self.assignments.clone());
                            }
                        } else {
                            self.guess_hints
                                .insert(Variable(i as u32), self.assignments.clone());
                        }
                    }
                }
            }
            #[cfg(feature = "trace")]
            if output_count > 0 {
                trace_flow!(
                    "new outputs set: {output_count}, total true: {} / {}, {} guesses",
                    output.iter().filter(|&&b| b).count(),
                    output.len(),
                    guesses.len()
                );
            }
            if guesses.is_empty() {
                if stuck {
                    trace_flow!("no guesses left to backtrack after full assignment");
                }
                break;
            }

            #[cfg(feature = "trace")]
            {
                backtrack_count += 1;
            }
            if stuck {
                trace_flow!("full assignment, rolling back completely");
            }
            top_level_probe = None;
            while let Some(guess) = guesses.pop() {
                self.rollback_guess_completely(guess);
            }
        }
        self.done = true;
        self.unsatisfiable |= !any_satisfying;

        for guess in guesses {
            self.not_a_guess.consume(guess, &self.assignments);
        }

        #[cfg(feature = "trace")]
        if tracing_enabled!("happier::stats") {
            trace_stats!(
                "guesses: {guess_count} ({hinted_guess_count} hinted), backtracks: {backtrack_count}, learned: {learned_count}"
            );
            let global_guesses = STATS_GUESSES.fetch_add(guess_count, Ordering::Relaxed);
            let global_backtracks = STATS_ROLLBACKS.fetch_add(backtrack_count, Ordering::Relaxed);
            let global_hinted_guesses =
                STATS_HINTED_GUESSES.fetch_add(hinted_guess_count, Ordering::Relaxed);
            trace_stats!(
                "global guesses: {} ({} hinted), backtracks: {}",
                global_guesses + guess_count,
                global_hinted_guesses + hinted_guess_count,
                global_backtracks + backtrack_count
            );
            trace_stats!(
                "global assignments: {}",
                STATS_ASSIGNMENTS.load(Ordering::Relaxed)
            );
        }

        output
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for(), "all variables invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", ensures(!self.done))]
    fn sat_header(&mut self) {
        #[cfg(all(debug_assertions, feature = "std"))]
        self.analyze_problem();
        if self.done {
            self.unroll();
        }
        if !self.presolved {
            self.presolve();
        }
        debug_assert!(self.not_a_guess.is_empty());
    }

    fn clause_slice(&self, index: u32) -> &[Literal] {
        self.store.slice(index)
    }

    fn clause_is_contradiction(&self, index: u32) -> bool {
        self.store.is_contradiction(index)
    }

    pub fn all_solutions(&mut self) -> Vec<Vec<Option<bool>>> {
        let mut dedup = dedup::DisjointCubes::new();
        self.satisfiable(&mut |state| {
            dedup.admit(&state.assignments);
            Control::Continue
        });
        dedup.into_served()
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_all_variables_accounted_for(), "all variables invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_per_variable_state(), "per variable invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    /// Whether any solution exists.
    ///
    /// `analyze_solutions` will be run for each complete assignment
    pub fn satisfiable<F>(&mut self, analyze_solutions: &mut F) -> bool
    where
        F: FnMut(&SATState) -> Control,
    {
        self.sat_header();

        if self.unsatisfiable {
            return false;
        }
        if !self.solos.forced_contradictions.is_empty() {
            return false;
        }
        if !self.duals.forced_contradictions.is_empty() {
            return false;
        }

        #[cfg(debug_assertions)]
        let presolve_depth = self.assign_order.len();

        let mut guesses: Vec<UndoableGuess> = Vec::new();
        #[cfg(feature = "trace")]
        let mut guess_count = 0;
        #[cfg(feature = "trace")]
        let mut backtrack_count = 0;
        #[cfg(feature = "trace")]
        let mut learned_count = 0;
        let mut any_satisfying = 0 == self.unassigned && self.active_contradiction.is_empty();

        loop {
            if let Some(last) = guesses.last() {
                debug_assert!(self.assignments[last.variable.index()].is_some());
            }

            let step = self.handle_conflict(&mut guesses, |_| {
                #[cfg(feature = "trace")]
                {
                    learned_count += 1;
                }
            });
            #[cfg(feature = "trace")]
            if step.rolled_back() {
                backtrack_count += 1;
            }
            match step {
                Step::Continue => continue,
                Step::TopLevel | Step::Forced => break,
                Step::Ready => {}
            }

            match self.propagate(&mut guesses) {
                Step::Continue => continue,
                Step::TopLevel | Step::Forced => break,
                Step::Ready => {}
            }

            if let Some(var) = self.select_next_guess() {
                let guessing = self.duals.possible_assignments[var.index()].any();
                #[cfg(feature = "trace")]
                {
                    guess_count += 1;
                }

                let mut undoable = UndoableGuess::new(var);

                debug_assert!(
                    self.duals
                        .assignment_will_contradict(&self.assignments, var.literal(guessing))
                        .is_none()
                );

                trace_assign!(
                    "guess: {var:?}={guessing} / {}, previous forced {}",
                    guesses.len(),
                    active_ledger_len(&guesses, &self.not_a_guess)
                );
                if let Some(contradiction_index) =
                    self.make_assignment_with_implications(var, guessing, &mut undoable)
                {
                    self.active_contradiction
                        .push(ContradictionReason::Clause(contradiction_index));
                }
                debug_assert!(self.assignments[undoable.variable.index()].is_some());
                guesses.push(undoable);
                continue;
            }

            #[cfg(feature = "contracts")]
            debug_assert!(self.invariant_clause_tracking_all());
            debug_assert_eq!(0, self.store.unsatisfied);
            if self.active_contradiction.is_empty() {
                #[cfg(feature = "contracts")]
                debug_assert!(self.invariant_solution_satisfies_all());
                any_satisfying = true;
                match analyze_solutions(self) {
                    Control::Continue => {
                        if let Some(guess) = guesses.pop() {
                            #[cfg(feature = "trace")]
                            {
                                backtrack_count += 1;
                            }
                            trace_flow!("continuing search, rolling back last guess");
                            self.rollback_guess(guess, &mut guesses);
                            continue;
                        }
                    }
                    Control::Stop => (),
                }
            }
            trace_flow!("all variables assigned, exiting");
            break;
        }
        self.done = true;
        self.unsatisfiable |= !any_satisfying;
        #[cfg(feature = "trace")]
        if tracing_enabled!("happier::stats") {
            trace_stats!(
                "guesses: {guess_count}, backtracks: {backtrack_count}, learned: {learned_count}"
            );
        }

        for guess in guesses {
            self.not_a_guess.consume(guess, &self.assignments);
        }
        #[cfg(debug_assertions)]
        self.validate_rollback_ledger(presolve_depth);

        any_satisfying
    }
}

#[cfg(feature = "rsat")]
pub mod rsat {
    use super::*;

    use rustsat::solvers::{Solve, SolverResult};
    use rustsat::types::constraints::Cl;
    use rustsat::types::{Clause, Lit, TernaryVal};

    impl Extend<Clause> for SATState {
        fn extend<I: IntoIterator<Item = rustsat::types::Clause>>(&mut self, iter: I) {
            for clause in iter {
                let clause_lits = clause
                    .iter()
                    .map(|&lit| {
                        let var = self.new_variable_at(lit.vidx32() as usize);
                        if lit.is_pos() {
                            var.literal_pos()
                        } else {
                            var.literal_neg()
                        }
                    })
                    .collect::<alloc::vec::Vec<_>>();
                self.add_clause(clause_lits);
            }
        }
    }

    impl<'a> Extend<&'a Clause> for SATState {
        fn extend<I: IntoIterator<Item = &'a rustsat::types::Clause>>(&mut self, iter: I) {
            for clause in iter {
                let clause_lits = clause
                    .iter()
                    .map(|&lit| {
                        let var = self.new_variable_at(lit.vidx32() as usize);
                        if lit.is_pos() {
                            var.literal_pos()
                        } else {
                            var.literal_neg()
                        }
                    })
                    .collect::<alloc::vec::Vec<_>>();
                self.add_clause(clause_lits);
            }
        }
    }

    impl Solve for SATState {
        fn signature(&self) -> &'static str {
            "happier v0.1.0"
        }

        fn solve(&mut self) -> anyhow::Result<SolverResult> {
            Ok(if self.satisfiable(&mut just_satisfiable) {
                SolverResult::Sat
            } else {
                SolverResult::Unsat
            })
        }

        fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
            let variable_index = lit.vidx();
            Ok(self
                .assignments
                .get(variable_index)
                .map(|&a| match a {
                    Some(value) if value == lit.is_pos() => TernaryVal::True,
                    Some(_) => TernaryVal::False,
                    None => TernaryVal::DontCare,
                })
                .unwrap_or(TernaryVal::DontCare))
        }

        fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
        where
            C: AsRef<Cl> + ?Sized,
        {
            let max_variable = clause
                .as_ref()
                .iter()
                .map(|&lit| lit.vidx())
                .max()
                .unwrap_or(0);
            self.new_variable_at(max_variable);
            self.add_clause(ClauseAdapter { clause });
            Ok(())
        }
    }

    pub struct ClauseAdapter<C: AsRef<Cl>> {
        clause: C,
    }
    impl<C: AsRef<Cl>> ClauseAdapter<C> {
        pub fn new(clause: C) -> Self {
            ClauseAdapter { clause }
        }
    }

    impl<C: AsRef<Cl>> CowClause for ClauseAdapter<C> {
        fn to_owned(self) -> Vec<Literal> {
            self.clause
                .as_ref()
                .iter()
                .map(|&lit| {
                    let var = Variable(lit.vidx32());
                    if lit.is_pos() {
                        var.literal_pos()
                    } else {
                        var.literal_neg()
                    }
                })
                .collect()
        }
        fn len(&self) -> usize {
            self.clause.as_ref().len()
        }
        fn get_literal(&self, i: usize) -> Literal {
            let lit = self.clause.as_ref().iter().nth(i).unwrap();
            let var = Variable(lit.vidx32());
            if lit.is_pos() {
                var.literal_pos()
            } else {
                var.literal_neg()
            }
        }
        fn max_var(&self) -> Variable {
            let max_vidx = self
                .clause
                .as_ref()
                .iter()
                .map(|&lit| lit.vidx32())
                .max()
                .unwrap_or(0);
            Variable(max_vidx)
        }
    }
}
