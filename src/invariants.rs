use crate::CowClause;
use crate::clause::{Clause, Clauseish, DualClauses, SoloClauses, UnitClause};
use crate::{ClauseStore, Literal, SATState, UndoableGuess, Variable};
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

macro_rules! std_println {
    ($($arg:tt)*) => {
        #[cfg(feature = "std")]
        { std::println!($($arg)*); }
    };
}

pub(crate) trait CowClauseInvariants {
    fn invariant_nonempty(&self) -> bool;
    fn invariant_no_duplicate_vars(&self) -> bool;
    fn invariant_well_formed_input(&self) -> bool;
}

impl<C: CowClause + ?Sized> CowClauseInvariants for C {
    fn invariant_nonempty(&self) -> bool {
        self.len() > 0
    }

    fn invariant_no_duplicate_vars(&self) -> bool {
        let mut vars: Vec<Variable> = (0..self.len())
            .map(|i| self.get_literal(i))
            .map(Literal::variable)
            .collect();
        vars.sort_unstable();
        vars.dedup();
        vars.len() == self.len()
    }

    fn invariant_well_formed_input(&self) -> bool {
        self.invariant_nonempty() && self.invariant_no_duplicate_vars()
    }
}

impl Clause {
    pub(crate) fn invariant_plausible_unassigned(&self) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        self.unassigned <= self.literals.len()
    }

    pub(crate) fn invariant_plausible_satisfying(&self) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        self.satisfying as usize + self.unassigned <= self.literals.len()
    }

    pub(crate) fn invariant_clause_matches_assignments(
        &self,
        assignments: &[Option<bool>],
    ) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        debug_assert!(self.invariant_literals_partitioned(assignments));
        debug_assert!(self.invariant_valid_satisfying(assignments));
        debug_assert!(self.invariant_valid_unassigned(assignments));
        debug_assert!(self.invariant_clause_self_consistent());
        self.invariant_literals_partitioned(assignments)
            && self.invariant_valid_satisfying(assignments)
            && self.invariant_valid_unassigned(assignments)
            && self.invariant_clause_self_consistent()
    }

    pub(crate) fn invariant_clause_self_consistent(&self) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        self.invariant_plausible_satisfying()
            && self.invariant_plausible_unassigned()
            && self.invariant_literals_sorted()
    }

    pub(crate) fn invariant_valid_unassigned(&self, assignments: &[Option<bool>]) -> bool {
        let actual_unassigned = self
            .literals
            .iter()
            .filter(|&&lit| assignments[lit.var_index()].is_none())
            .count();
        actual_unassigned == self.unassigned
    }

    pub(crate) fn invariant_valid_satisfying(&self, assignments: &[Option<bool>]) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        let actual_satisfying = self
            .literals
            .iter()
            .filter(|&&lit| {
                assignments[lit.var_index()]
                    .map(|assigned| assigned == lit.is_true())
                    .unwrap_or(false)
            })
            .count();
        actual_satisfying == self.satisfying as usize
    }

    pub(crate) fn invariant_literals_partitioned(&self, assignments: &[Option<bool>]) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        let (unassigned_slice, assigned_slice) = self.literals.split_at(self.unassigned);
        unassigned_slice
            .iter()
            .all(|&lit| assignments[lit.var_index()].is_none())
            && assigned_slice
                .iter()
                .all(|&lit| assignments[lit.var_index()].is_some())
    }

    pub(crate) fn invariant_literals_sorted(&self) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        if cfg!(feature = "clause-sorted") {
            let (unassigned_slice, assigned_slice) = self.literals.split_at(self.unassigned);
            unassigned_slice.is_sorted() && assigned_slice.is_sorted()
        } else {
            true
        }
    }

    pub(crate) fn invariant_has_variable(&self, var: Variable) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        if cfg!(feature = "clause-sorted") {
            let (unassigned_slice, assigned_slice) = self.literals.split_at(self.unassigned);
            unassigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .is_ok()
                || assigned_slice
                    .binary_search_by_key(&var, |&l| l.variable())
                    .is_ok()
        } else {
            self.literals.iter().any(|&lit| lit.variable() == var)
        }
    }

    pub(crate) fn invariant_has_assigned_var(&self, var: Variable) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        if cfg!(feature = "clause-sorted") {
            let assigned_slice = &self.literals[self.unassigned..];
            assigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .is_ok()
        } else {
            self.iter_assigned().any(|lit| lit.variable() == var)
        }
    }

    pub(crate) fn invariant_has_unassigned_var(&self, var: Variable) -> bool {
        if self.satisfying > 0 {
            return true;
        }
        if cfg!(feature = "clause-sorted") {
            let unassigned_slice = &self.literals[..self.unassigned];
            unassigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .is_ok()
        } else {
            self.iter_unassigned().any(|lit| lit.variable() == var)
        }
    }

    pub(crate) fn contract_unassigned_lit(&self, var: Variable) -> Literal {
        if cfg!(feature = "clause-sorted") {
            let unassigned_slice = &self.literals[..self.unassigned];
            let index = unassigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .unwrap();
            unassigned_slice[index]
        } else {
            self.iter_unassigned()
                .find(|&lit| lit.variable() == var)
                .unwrap()
        }
    }

    pub(crate) fn contract_assigned_lit(&self, var: Variable) -> Literal {
        if cfg!(feature = "clause-sorted") {
            let assigned_slice = &self.literals[self.unassigned..];
            let index = assigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .unwrap();
            assigned_slice[index]
        } else {
            self.iter_assigned()
                .find(|&lit| lit.variable() == var)
                .unwrap()
        }
    }
}

impl UnitClause {
    pub(crate) fn invariant_unassigned_is_unsatisfying(&self) -> bool {
        self.assigned || !self.satisfying
    }
}

impl ClauseStore {
    pub(crate) fn invariant_unit_indexes_tracking(&self) -> bool {
        for (i, clause) in self.clauses.iter().enumerate() {
            if clause.is_unitish() != self.unit_indices.contains(i as u32) {
                return false;
            }
        }
        true
    }
}

impl SoloClauses {
    pub(crate) fn invariant_forced_contradictions_tracked(&self) -> bool {
        for &lit in &self.forced_assignments {
            if self.forced_assignments.contains(&lit.negate())
                && (!self.forced_contradictions.contains(&lit)
                    || !self.forced_contradictions.contains(&lit.negate()))
            {
                return false;
            }
        }
        for &lit in &self.forced_contradictions {
            if !self.forced_assignments.contains(&lit)
                || !self.forced_assignments.contains(&lit.negate())
            {
                return false;
            }
        }
        true
    }
}

impl DualClauses {
    pub(crate) fn invariant_implication_backgraph(&self) -> bool {
        for implier in 0..self.implication_graph.len() {
            let mut seen = BTreeSet::new();
            for &implied in &self.implication_graph[implier] {
                if !seen.insert(implied) {
                    return false;
                }
            }
        }
        for implier in 0..self.implication_graph.len() {
            let mut seen = BTreeSet::new();
            for &implied in &self.inverse_implication[implier] {
                if !seen.insert(implied) {
                    return false;
                }
            }
        }

        for implier in 0..self.implication_graph.len() {
            let implier_lit = Literal(implier as u32);
            for &implied in &self.implication_graph[implier] {
                if !self.inverse_implication[implied.lit_index()].contains(&implier_lit) {
                    return false;
                }
            }
        }
        for implier in 0..self.inverse_implication.len() {
            let implier_lit = Literal(implier as u32);
            for &implied in &self.inverse_implication[implier] {
                if !self.implication_graph[implied.lit_index()].contains(&implier_lit) {
                    return false;
                }
            }
        }
        true
    }

    #[cfg(feature = "contracts")]
    pub(crate) fn invariant_implied_contradictions_propagated(&self) -> bool {
        for (i, implied) in self.implication_graph.iter().enumerate() {
            let lit = Literal(i as u32);
            for &implied_lit in implied {
                if self.will_contradict[implied_lit.lit_index()].is_some()
                    && self.will_contradict[lit.lit_index()].is_none()
                {
                    std_println!("{lit:?} implies {implied_lit:?}");
                    std_println!("{implied_lit:?} implies a contradiction");
                    std_println!("{lit:?} does not imply a contradiction");
                    std_println!("Self: {self:#?}");
                    return false;
                }
            }
        }

        for var in &self.forced_contradictions {
            if self.will_contradict[var.literal_pos().lit_index()].is_none()
                || self.will_contradict[var.literal_neg().lit_index()].is_none()
            {
                debug_assert!(false);
                return false;
            }
        }

        for (i, wc) in self.will_contradict.iter().enumerate() {
            if wc.is_none() {
                continue;
            }
            let lit = Literal(i as u32);
            if self.will_contradict[lit.negate().lit_index()].is_some()
                && !self.forced_contradictions.contains(&lit.variable())
            {
                debug_assert!(false);
                return false;
            }
        }

        for (i, wc) in self.will_contradict.iter().enumerate() {
            if wc.is_none() {
                continue;
            }
            let lit = Literal(i as u32);
            if self.possible_assignments[lit.var_index()].allows(lit.is_true()) {
                debug_assert!(false);
                return false;
            }
        }

        true
    }
}

impl SATState {
    pub(crate) fn invariant_next_guess_tracking(&self) -> bool {
        let mut expected_guess = None;
        for i in 0..self.assignments.len() {
            if self.assignments[i].is_some() {
                continue;
            }
            if self.store.clause_presence[i] > 0 {
                expected_guess = Some(Variable(i as u32));
                break;
            }
        }
        debug_assert_eq!(expected_guess, self.next_clause_guess_var);
        expected_guess == self.next_clause_guess_var
    }

    pub(crate) fn invariant_per_variable_state(&self) -> bool {
        self.assignments.len() == self.store.usages.len()
            && self.assignments.len() == self.store.clause_presence.len()
    }

    pub(crate) fn invariant_clause_tracking_all(&self) -> bool {
        let mut satisfied_clauses = 0;
        let mut clause_presence = vec![0u32; self.assignments.len()];
        let mut usages: Vec<Vec<u32>> = vec![Vec::new(); self.assignments.len()];
        let mut unsatisfied_clauses: Vec<u32> = Vec::new();
        let mut total_unsat_clauses = 0;

        for (clause_index, clause) in self.store.clauses.iter().enumerate() {
            let mut actual_satisfying = 0;
            for lit in clause.dyn_iter_all() {
                if let Some(assigned) = self.assignments[lit.var_index()]
                    && lit.matching(assigned)
                {
                    actual_satisfying += 1;
                }
            }

            debug_assert_eq!(actual_satisfying > 0, clause.satisfying > 0);
            if (actual_satisfying > 0) != (clause.satisfying > 0) {
                return false;
            }

            if actual_satisfying > 0 {
                satisfied_clauses += 1;
                let instances = self
                    .desatisfy_stack
                    .stack
                    .iter()
                    .filter(|&&i| i == clause_index as u32)
                    .count();
                debug_assert_eq!(1, instances);
                if 1 != instances {
                    return false;
                }
                continue;
            }

            total_unsat_clauses += 1;
            unsatisfied_clauses.push(clause_index as u32);
            for lit in clause.dyn_iter_all() {
                clause_presence[lit.var_index()] += 1;
                usages[lit.var_index()].push(clause_index as u32);
            }
        }

        if satisfied_clauses != self.desatisfy_stack.stack.len() {
            return false;
        }

        debug_assert_eq!(self.store.clause_presence, clause_presence);
        if self.store.clause_presence != clause_presence {
            return false;
        }

        for (expected, actual) in usages.iter().zip(self.store.usages.iter()) {
            let mut expected_sorted = expected.clone();
            expected_sorted.sort_unstable();
            let mut actual_sorted = actual.iter_big().collect::<Vec<_>>();
            actual_sorted.sort_unstable();
            debug_assert_eq!(expected_sorted, actual_sorted);
            if expected_sorted != actual_sorted {
                return false;
            }
        }

        let mut unsat_copy = self.store.unsatisfied_clauses.clone();
        unsatisfied_clauses.sort_unstable();

        for &clause_index in &unsatisfied_clauses {
            if !unsat_copy.contains(clause_index as usize) {
                return false;
            }
            unsat_copy.remove(clause_index as usize);
        }
        if unsat_copy.any().is_some() {
            return false;
        }

        debug_assert_eq!(total_unsat_clauses, self.store.unsatisfied);
        if self.store.unsatisfied != total_unsat_clauses {
            return false;
        }

        true
    }

    pub(crate) fn invariant_unassigned_tracking(&self) -> bool {
        let actual_unassigned = self
            .assignments
            .iter()
            .copied()
            .filter(Option::is_none)
            .count();
        actual_unassigned == self.unassigned
    }

    pub(crate) fn invariant_no_contradiction(&self) -> bool {
        !self.invariant_has_contradiction()
    }

    pub(crate) fn invariant_frame_owns_contradictions(&self, guess: &UndoableGuess) -> bool {
        let frame: BTreeSet<usize> = guess
            .assignments
            .iter()
            .map(|(v, _)| v.index())
            .chain(core::iter::once(guess.variable.index()))
            .collect();
        self.iter_all_clauses()
            .filter(|clause| clause.definitely_contradictory())
            .all(|clause| {
                clause
                    .literals
                    .iter()
                    .any(|lit| frame.contains(&lit.var_index()))
            })
    }

    pub(crate) fn invariant_solution_satisfies_all(&self) -> bool {
        let open = |lit: Literal| match self.assignments[lit.var_index()] {
            Some(value) => lit.matching(value),
            None => self.duals.possible_assignments[lit.var_index()].allows(lit.is_true()),
        };
        let bigs = self
            .iter_all_clauses()
            .all(|clause| clause.literals.iter().copied().any(open));
        let units = self.solos.forced_assignments.iter().copied().all(open);
        bigs && units
    }

    pub(crate) fn invariant_has_contradiction(&self) -> bool {
        self.iter_all_clauses()
            .any(|clause| clause.definitely_contradictory())
    }

    pub(crate) fn invariant_unit_indexes_tracking(&self) -> bool {
        self.store.invariant_unit_indexes_tracking()
    }

    pub(crate) fn invariant_literal_usage_tracking(&self) -> bool {
        let mut count = 0;
        for clause in self.iter_all_clauses() {
            if clause.satisfying_count() == 0 {
                count += 1;
            }
        }
        debug_assert_eq!(count, self.store.unsatisfied);
        self.store.unsatisfied == count
    }

    pub(crate) fn invariant_all_variables_accounted_for(&self) -> bool {
        self.iter_all_clauses()
            .flat_map(|clause| clause.dyn_iter_all())
            .all(|lit| lit.var_index() < self.assignments.len())
    }
}
