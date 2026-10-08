#[cfg(feature = "trace")]
use crate::STATS_ASSIGNMENTS;
use crate::clause::DualClauses;
use crate::store::{ClauseStore, DesatisfyStack};
use crate::{
    AssignmentLedger, AssignmentReason, ContradictionReason, Literal, SATState, UndoableGuess,
    Variable, active_ledger, potential_guess, potential_unguess, unchecked_get, unchecked_mut,
};
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec::Vec;

#[cfg(debug_assertions)]
use crate::{record_assignment, validate_unassignment};

#[cfg(feature = "contracts")]
use contracts::debug_requires as requires;

impl SATState {
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    pub(crate) fn assign_forced(
        &mut self,
        guesses: &mut [UndoableGuess],
    ) -> Option<Option<ContradictionReason>> {
        let (lit, src) = if true {
            let (lit, src) = if let Some(&literal) = self.duals.unit_forces.last() {
                (literal, AssignmentReason::Dual(literal, literal))
            } else {
                let clause_index = self.store.unit_indices.any()?;
                let clause = self.clause_slice(clause_index);
                trace_learn!("forcing clause {clause:?}");
                (
                    self.store.clauses[clause_index as usize].unit_unassigned(),
                    AssignmentReason::Clause(clause_index),
                )
            };
            (lit, src)
        } else {
            let (lit, src) = if let Some(clause_index) = self.store.unit_indices.any() {
                let clause = self.clause_slice(clause_index);
                trace_learn!("forcing clause {clause_index} {clause:?}");
                (
                    self.store.clauses[clause_index as usize].unit_unassigned(),
                    AssignmentReason::Clause(clause_index),
                )
            } else {
                let literal = *self.duals.unit_forces.last()?;
                (literal, AssignmentReason::Dual(literal, literal))
            };
            (lit, src)
        };

        if let Some(contradiction) = self
            .duals
            .assignment_will_contradict(&self.assignments, lit)
        {
            return Some(Some(ContradictionReason::DualContradiction(
                lit,
                contradiction,
            )));
        }
        let var = lit.variable();
        let mut ref_assignments = AssignmentLedger::empty();
        core::mem::swap(
            &mut ref_assignments,
            active_ledger(guesses, &mut self.not_a_guess),
        );
        trace_assign!("assign forced {var:?} = {}", lit.is_true());
        ref_assignments.push_assignment(var, src);
        let contradiction_clause =
            self.make_assignment_with_implications(var, lit.is_true(), &mut ref_assignments);
        core::mem::swap(
            &mut ref_assignments,
            active_ledger(guesses, &mut self.not_a_guess),
        );
        Some(contradiction_clause.map(ContradictionReason::Clause))
    }

    #[must_use]
    #[cfg_attr(feature = "contracts", requires(self.store.clauses.iter().all(|c| c.invariant_clause_matches_assignments(&self.assignments))))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", ensures(self.store.clauses.iter().all(|c| c.invariant_clause_matches_assignments(&self.assignments))))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    pub(crate) fn make_assignment_with_implications(
        &mut self,
        var: Variable,
        value: bool,
        guess_tracker: &mut AssignmentLedger,
    ) -> Option<u32> {
        let literal = var.literal(value);

        let mut contradiction_index = None;

        contradiction_index = Self::make_assign_one(
            literal,
            &mut self.store,
            &mut self.assignments,
            #[cfg(debug_assertions)]
            &mut self.assign_order,
            &mut self.unassigned,
            &mut self.duals,
            &mut self.desatisfy_stack,
            &mut self.next_clause_guess_var,
        )
        .or(contradiction_index);

        let implication_count = self.duals.implication_graph[literal.lit_index()].len();
        if tracing_enabled!("happier::assign") && implication_count > 0 {
            trace_assign!(
                "implications for {literal:?}: {}",
                self.duals.implication_graph[literal.lit_index()]
                    .iter()
                    .map(|imp| format!("{imp:?}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
        for i in 0..implication_count {
            let implication = self.duals.implication_graph[literal.lit_index()][i];
            if unchecked_get(&self.assignments, implication.var_index()).is_some() {
                debug_assert_eq!(
                    self.assignments[implication.var_index()],
                    Some(implication.is_true())
                );
                continue;
            }

            guess_tracker.push_assignment(
                implication.variable(),
                AssignmentReason::Dual(literal.negate(), implication),
            );
            contradiction_index = Self::make_assign_one(
                implication,
                &mut self.store,
                &mut self.assignments,
                #[cfg(debug_assertions)]
                &mut self.assign_order,
                &mut self.unassigned,
                &mut self.duals,
                &mut self.desatisfy_stack,
                &mut self.next_clause_guess_var,
            )
            .or(contradiction_index);
        }

        contradiction_index
    }

    #[inline(always)]
    #[allow(
        clippy::too_many_arguments,
        reason = "disjoint borrows of solver state"
    )]
    pub(crate) fn make_assign_one(
        lit: Literal,
        store: &mut ClauseStore,
        assignments: &mut [Option<bool>],
        #[cfg(debug_assertions)] assign_order: &mut Vec<Literal>,
        unassigned: &mut usize,
        duals: &mut DualClauses,
        desatisfy_stack: &mut DesatisfyStack,
        next_clause_guess_var: &mut Option<Variable>,
    ) -> Option<u32> {
        let mut contradiction_index = None;

        let var = lit.variable();
        let value = lit.is_true();
        let var_index = var.index();

        #[cfg(feature = "trace")]
        STATS_ASSIGNMENTS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);

        debug_assert!(assignments[var_index].is_none());
        duals.finalize_assignment(var.literal(value));
        *unchecked_mut(assignments, var_index) = Some(value);
        #[cfg(debug_assertions)]
        record_assignment(assignments, assign_order, var, value);
        potential_unguess(
            assignments,
            &store.clause_presence,
            next_clause_guess_var,
            var,
        );

        *unassigned -= 1;

        let mut satisfied_clauses = Vec::new();
        let using_count = unchecked_get(&store.usages, var_index).len();
        for i in 0..using_count {
            let clause_index = unchecked_get(&store.usages, var_index).at(i);
            if store.assign_in_clause(clause_index, var, value, &mut contradiction_index) {
                satisfied_clauses.push(clause_index);
            }
        }

        let mut count = 0;
        let mut seen = BTreeSet::new();
        for clause_index in satisfied_clauses {
            let clause = unchecked_get(&store.clauses, clause_index as usize);
            for &lit in &clause.literals {
                let lit_var = lit.var_index();
                store.usages[lit_var].remove_big(clause_index);
                store.clause_presence[lit_var] -= 1;
                potential_unguess(
                    assignments,
                    &store.clause_presence,
                    next_clause_guess_var,
                    Variable(lit_var as u32),
                );
            }
            if !seen.insert(clause_index) {
                panic!("Clause {clause_index} satisfied twice in one assignment");
            }
            debug_assert!(
                !desatisfy_stack.stack.contains(&clause_index),
                "Clause {clause_index} satisfied twice previously"
            );
            desatisfy_stack.push_one(clause_index);
            count += 1;
        }
        desatisfy_stack.mark(lit, count);

        contradiction_index
    }

    #[inline(never)]
    pub(crate) fn rehydrate_satisfied(&mut self) {
        debug_assert!(!self.desatisfy_stack.is_empty());
        for clause_index in self.desatisfy_stack.pop_set() {
            let clause = unchecked_mut(&mut self.store.clauses, clause_index as usize);
            for &lit in &clause.literals {
                self.store.usages[lit.var_index()].insert(clause_index);
                self.store.clause_presence[lit.var_index()] += 1;
                potential_guess(
                    &self.assignments,
                    &self.store.clause_presence,
                    &mut self.next_clause_guess_var,
                    Variable(lit.var_index() as u32),
                );
            }
        }
    }

    fn make_unassignment_main(&mut self, var: Variable) -> bool {
        let var_index = var.index();
        debug_assert!(self.assignments[var_index].is_some());

        let value = self.assignments[var_index].take().unwrap();
        self.duals.finalize_unassignment(var.literal(value));
        self.unassigned += 1;
        potential_guess(
            &self.assignments,
            &self.store.clause_presence,
            &mut self.next_clause_guess_var,
            var,
        );
        self.rehydrate_satisfied();
        value
    }

    fn make_unassignment_secondary(&mut self, clause_index: u32, var: Variable, value: bool) {
        self.store.unassign_in_clause(clause_index, var, value);
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    pub(crate) fn make_unassignment(&mut self, var: Variable) {
        #[cfg(debug_assertions)]
        validate_unassignment(&mut self.assignments, &mut self.assign_order, var);
        let var_index = var.index();
        let value = self.make_unassignment_main(var);

        let users = self.store.usages[var_index].clauses.len();
        for i in 0..users {
            let clause_index = self.store.usages[var_index].clauses[i];
            // Skip clauses that are on the desatisfy stack - they'll be handled during rehydration
            if !self.desatisfy_stack.stacked.contains(clause_index as usize) {
                self.make_unassignment_secondary(clause_index, var, value);
            }
        }
    }

    #[must_use]
    #[cfg_attr(feature = "contracts", requires(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_tracking_all()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_next_guess_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_literal_usage_tracking()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_tracking_all()))]
    pub(crate) fn make_reassignment(
        &mut self,
        var: Variable,
        value: bool,
        guess_tracker: &mut AssignmentLedger,
    ) -> Option<u32> {
        self.rehydrate_satisfied();

        let root_var = var;

        let mut contradiction_index = None;
        let literal = var.literal(value);

        debug_assert!(self.assignments[var.index()].is_some());
        debug_assert_eq!(self.assignments[var.index()], Some(!value));
        #[cfg(debug_assertions)]
        validate_unassignment(&mut self.assignments, &mut self.assign_order, var);

        self.duals.finalize_reassignment(var.literal(value));
        self.assignments[var.index()] = Some(value);
        #[cfg(debug_assertions)]
        record_assignment(&mut self.assignments, &mut self.assign_order, var, value);
        potential_unguess(
            &self.assignments,
            &self.store.clause_presence,
            &mut self.next_clause_guess_var,
            var,
        );

        let mut satisfied_clauses = Vec::new();
        let using_count = self.store.usages[var.index()].len();
        for i in 0..using_count {
            let clause_index = self.store.usages[var.index()].at(i);
            if self
                .store
                .reassign_in_clause(clause_index, var, value, &mut contradiction_index)
            {
                satisfied_clauses.push(clause_index);
            }
        }

        let mut count = 0;
        let mut seen = BTreeSet::new();
        for clause_index in satisfied_clauses {
            let clause = unchecked_mut(&mut self.store.clauses, clause_index as usize);
            for &lit in &clause.literals {
                self.store.usages[lit.var_index()].remove_big(clause_index);
                self.store.clause_presence[lit.var_index()] -= 1;
                potential_unguess(
                    &self.assignments,
                    &self.store.clause_presence,
                    &mut self.next_clause_guess_var,
                    Variable(lit.var_index() as u32),
                );
            }
            if !seen.insert(clause_index) {
                panic!("Clause {clause_index} satisfied twice in one assignment");
            }
            if self.desatisfy_stack.stack.contains(&clause_index) {
                panic!("Clause {clause_index} satisfied twice previously");
            }
            self.desatisfy_stack.push_one(clause_index);
            count += 1;
        }
        self.desatisfy_stack.mark(literal, count);

        let implication_count = self.duals.implication_graph[literal.lit_index()].len();
        for i in 0..implication_count {
            let implication = self.duals.implication_graph[literal.lit_index()][i];
            let var = implication.variable();
            let value = implication.is_true();

            if unchecked_get(&self.assignments, var.index()).is_some() {
                debug_assert_eq!(self.assignments[var.index()], Some(value));
                continue;
            }

            trace_assign!("implication: {root_var:?} => {var:?} = {value}");
            guess_tracker
                .push_assignment(var, AssignmentReason::Dual(literal.negate(), implication));
            contradiction_index = Self::make_assign_one(
                var.literal(value),
                &mut self.store,
                &mut self.assignments,
                #[cfg(debug_assertions)]
                &mut self.assign_order,
                &mut self.unassigned,
                &mut self.duals,
                &mut self.desatisfy_stack,
                &mut self.next_clause_guess_var,
            )
            .or(contradiction_index);
        }

        contradiction_index
    }
}
