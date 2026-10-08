use crate::{SATState, Variable, unchecked_get};

#[cfg(feature = "contracts")]
use contracts::debug_requires as requires;

#[inline(always)]
pub(crate) fn potential_guess(
    assignments: &[Option<bool>],
    clause_presence: &[u32],
    next_clause_guess_var: &mut Option<Variable>,
    var: Variable,
) {
    if *unchecked_get(clause_presence, var.index()) > 0
        && unchecked_get(assignments, var.index()).is_none()
        && (next_clause_guess_var.is_none() || Some(var) < *next_clause_guess_var)
    {
        *next_clause_guess_var = Some(var);
    }
}

#[inline(always)]
pub(crate) fn potential_unguess(
    assignments: &[Option<bool>],
    clause_presence: &[u32],
    next_clause_guess_var: &mut Option<Variable>,
    var: Variable,
) {
    if Some(var) == *next_clause_guess_var
        && (*unchecked_get(clause_presence, var.index()) == 0
            || unchecked_get(assignments, var.index()).is_some())
    {
        *next_clause_guess_var = None;
        // we know that there should be none less than var
        for (i, &presence) in clause_presence.iter().enumerate().skip(var.index() + 1) {
            if presence > 0 && unchecked_get(assignments, i).is_none() {
                *next_clause_guess_var = Some(Variable(i as u32));
                break;
            }
        }
    }
}

impl SATState {
    #[cfg_attr(feature = "contracts", requires(self.invariant_next_guess_tracking()))]
    fn select_guess_from_clause(&self) -> Option<Variable> {
        if let Some(low_end) = self.next_clause_guess_var {
            let mut best_var = None;
            let mut best_score = (false, 0);
            for i in low_end.index()..self.assignments.len() {
                if self.assignments[i].is_some() {
                    continue;
                }
                let presence = self.store.clause_presence[i];
                let can_be_pos = self.duals.possible_assignments[i].can_be_pos();
                if (can_be_pos, presence) > best_score {
                    best_var = Some(Variable(i as u32));
                    best_score = (can_be_pos, presence);
                }
            }
            best_var
        } else {
            None
        }
    }

    fn select_guess_from_duals(&self) -> Option<Variable> {
        for i in 0..self.assignments.len() {
            if self.assignments[i].is_some() {
                continue;
            }
            let variable = Variable(i as u32);
            if !self.duals.implication_graph[variable.literal_pos().lit_index()].is_empty()
                || !self.duals.implication_graph[variable.literal_neg().lit_index()].is_empty()
            {
                debug_assert!(
                    self.duals
                        .assignment_will_contradict(&self.assignments, variable.literal(true))
                        .is_none()
                        || self
                            .duals
                            .assignment_will_contradict(&self.assignments, variable.literal(false))
                            .is_none()
                );
                return Some(variable);
            }
        }
        None
    }

    pub(crate) fn select_next_guess(&mut self) -> Option<Variable> {
        self.select_guess_from_clause()
            .or_else(|| self.select_guess_from_duals())
    }

    pub(crate) fn hinted_guess(
        &self,
        range: core::ops::Range<usize>,
        output: &[bool],
        guess_var: Variable,
    ) -> Option<bool> {
        let mut best_score = 0;
        let mut best_guess = None;
        for (var, solution) in &self.guess_hints {
            if output[var.index() - range.start] {
                continue;
            }
            let mut match_count = 0;
            let mut hard_mismatch = false;

            for (sol, assign) in solution.iter().zip(self.assignments.iter()) {
                match (sol, assign) {
                    (Some(a), Some(b)) if a == b => match_count += 1,
                    (Some(a), Some(b)) if a != b => {
                        hard_mismatch = true;
                        break;
                    }
                    _ => {}
                }
            }
            if hard_mismatch {
                continue;
            }

            if let Some(guess) = solution[guess_var.index()]
                && match_count > best_score
                && self
                    .duals
                    .assignment_will_contradict(&self.assignments, var.literal(guess))
                    .is_none()
            {
                best_score = match_count;
                best_guess = Some(guess);
            }
        }

        best_guess
    }
}
