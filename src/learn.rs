use crate::{AssignmentReason, ContradictionReason, Literal, SATState, UndoableGuess, Variable};
use alloc::vec::Vec;

#[cfg(feature = "contracts")]
use contracts::debug_requires as requires;

impl SATState {
    #[cfg_attr(feature = "contracts", requires(self.assignments[guess.variable.index()].is_some()))]
    pub(crate) fn learn_and_backtrack(
        &mut self,
        guesses: &mut Vec<UndoableGuess>,
        mut guess: UndoableGuess,
        reason: ContradictionReason,
    ) -> bool {
        let mut pseudo_clause = [Literal(0), Literal(0)];
        let clause = match reason {
            ContradictionReason::Blocked(_) => {
                trace_learn!("FAILED TO LEARN (blocked)");
                self.rollback_guess(guess, guesses);
                return false;
            }
            ContradictionReason::ForcedDual(_) => {
                trace_learn!("FAILED TO LEARN (forced dual)");
                self.rollback_guess(guess, guesses);
                return false;
            }
            ContradictionReason::Clause(index) => {
                let clause = self.clause_slice(index);
                debug_assert!(
                    clause
                        .iter()
                        .all(|&lit| self.assignments[lit.var_index()] == Some(!lit.is_true()))
                );
                clause
            }
            ContradictionReason::ForcedLiteral(literal) => {
                pseudo_clause[0] = literal;
                &pseudo_clause[0..1]
            }
            ContradictionReason::DualContradiction(left, rite) => {
                pseudo_clause[0] = left.negate();
                pseudo_clause[1] = rite;
                &pseudo_clause
            }
        };

        let mut new_clause = clause.to_vec();
        trace_learn!("new clause: {new_clause:?}");

        let mut modified = false;
        let mut pseudo_clause2 = [Literal(0), Literal(0)];
        let mut pseudo_big_clause = Vec::with_capacity(0);
        trace_learn!("guess: {guess:?}");

        let frame_vars: alloc::collections::BTreeSet<Variable> = core::iter::once(guess.variable)
            .chain(guess.ledger.assignments.iter().map(|(v, _)| *v))
            .collect();
        let at_conflict_level = |c: &[Literal]| {
            c.iter()
                .filter(|l| frame_vars.contains(&l.variable()))
                .count()
        };
        let mut hit_uip = at_conflict_level(&new_clause) == 1;

        for (assignment, forcing_clause) in guess.learning_iter() {
            if hit_uip {
                break;
            }
            let forcing_clause = match forcing_clause {
                AssignmentReason::Guess(refuted) => {
                    if let Some(position) = new_clause
                        .iter()
                        .position(|&lit| lit.variable() == assignment)
                    {
                        modified = true;
                        new_clause[position] = refuted;
                    } else {
                        trace_learn!("irrelevant assignment: {assignment:?} {forcing_clause:?}");
                        continue;
                    }

                    pseudo_big_clause.clear();
                    for guess in guesses.iter() {
                        let inv_lit = guess
                            .variable
                            .literal(self.assignments[guess.variable.index()].unwrap())
                            .negate();
                        pseudo_big_clause.push(inv_lit);
                    }
                    &pseudo_big_clause
                }
                AssignmentReason::Clause(clause_index) => {
                    if ContradictionReason::Clause(clause_index) == reason {
                        continue;
                    }
                    if let Some(position) = new_clause
                        .iter()
                        .position(|&lit| lit.variable() == assignment)
                    {
                        modified = true;
                        new_clause.swap_remove(position);
                    } else {
                        trace_learn!("irrelevant assignment: {assignment:?} {forcing_clause:?}");
                        continue;
                    }
                    self.clause_slice(clause_index)
                }
                AssignmentReason::Dual(left, rite) => {
                    if ContradictionReason::DualContradiction(left, rite) == reason {
                        continue;
                    }
                    if let Some(position) = new_clause
                        .iter()
                        .position(|&lit| lit.variable() == assignment)
                    {
                        modified = true;
                        new_clause.swap_remove(position);
                    } else {
                        trace_learn!("irrelevant assignment: {assignment:?} {forcing_clause:?}");
                        continue;
                    }
                    pseudo_clause2[0] = left;
                    pseudo_clause2[1] = rite;

                    &pseudo_clause2
                }
            };

            trace_learn!("force for {assignment:?}:");
            trace_learn!("forcing cl: {forcing_clause:?}");
            for &lit in forcing_clause {
                if lit.variable() == assignment {
                    continue;
                }
                if new_clause.contains(&lit) {
                    continue;
                }
                debug_assert!(!new_clause.contains(&lit.negate()));
                modified = true;
                new_clause.push(lit);
            }
            new_clause.sort_unstable_by_key(|&lit| (lit.var_index(), lit));
            new_clause.dedup();
            hit_uip = at_conflict_level(&new_clause) == 1;
            trace_learn!("new clause: {new_clause:?}");
        }

        new_clause.sort_unstable_by_key(|&lit| (lit.var_index(), lit));
        new_clause.dedup();

        self.minimize_learned(&mut new_clause, guesses, &guess);

        #[cfg(debug_assertions)]
        for i in 1..new_clause.len() {
            debug_assert_ne!(new_clause[i].variable(), new_clause[i - 1].variable());
        }

        if new_clause.is_empty() {
            trace_learn!("FAILED TO LEARN (empty learned)");
        }
        if !modified {
            trace_learn!("FAILED TO LEARN (could not create modified clause)");
        }

        if !new_clause.is_empty() && modified && cfg!(feature = "clause-learning") {
            let mut backup_clause = [None; 2];
            if new_clause.len() <= 2 {
                backup_clause[0] = Some(new_clause[0]);
                if new_clause.len() > 1 {
                    backup_clause[1] = Some(new_clause[1]);
                }
            }

            // now, we need to rollback until this clause becomes unit
            self.active_contradiction.clear();
            if let Some(learned) = self.add_learned_clause(new_clause) {
                if !self.active_contradiction.is_empty()
                    && let Some(index) = &learned
                    && let Some(pos) = self
                        .active_contradiction
                        .iter()
                        .position(|r| *r == ContradictionReason::Clause(*index))
                {
                    self.active_contradiction.remove(pos);
                }

                if tracing_enabled!("happier::learn") && !self.active_contradiction.is_empty() {
                    trace_learn!(
                        "contradiction after learning clause: {:?}",
                        self.active_contradiction
                    );
                    trace_learn!("self: {self:?}");
                    trace_learn!("guesses: {guesses:?}");
                    trace_learn!("guess: {guess:?}");
                    trace_learn!("possible: {:?}", self.duals.possible_assignments);
                }

                if !self.solos.forced_contradictions.is_empty()
                    || !self.duals.forced_contradictions.is_empty()
                {
                    self.rollback_guess_completely(guess);
                    return true;
                }

                for &contradiction in &self.active_contradiction {
                    debug_assert!(matches!(contradiction, ContradictionReason::Blocked(_)));
                }

                if tracing_enabled!("happier::learn") {
                    trace_learn!("self: {self:?}");
                    trace_learn!("guesses: {guesses:?}");
                    trace_learn!("guess: {guess:?}");
                }
                if let Some(clause_index) = learned {
                    let clause = self.clause_slice(clause_index);
                    trace_learn!("LEARNED CLAUSE: {:?}", clause);

                    let mut guess = guess;
                    let mut count = 0;
                    let mut first = true;

                    while first || self.clause_is_contradiction(clause_index) {
                        debug_assert!(
                            first
                                || self
                                    .store
                                    .unsatisfied_clauses
                                    .contains(clause_index as usize)
                        );
                        count += 1;
                        first = false;
                        self.rollback_guess_completely(guess);
                        if !self.clause_is_contradiction(clause_index) {
                            break;
                        }
                        if let Some(next) = guesses.pop() {
                            guess = next;
                        } else {
                            debug_assert!(
                                !self.clause_is_contradiction(clause_index),
                                "we should have found a unit clause by now"
                            );
                            break;
                        }
                    }

                    debug_assert_eq!(0, self.store.clauses[clause_index as usize].satisfying);
                    if self.store.clauses[clause_index as usize].unassigned == 1 {
                        while !guesses.is_empty() {
                            let next = guesses.last().unwrap();
                            let mut breaking = false;
                            let clause = self.clause_slice(clause_index);
                            if clause.iter().any(|&lit| lit.variable() == next.variable) {
                                breaking = true;
                            }
                            if !breaking {
                                for &(var, _) in &next.assignments {
                                    if clause.iter().any(|&l| l.variable() == var) {
                                        breaking = true;
                                        break;
                                    }
                                }
                            }
                            if breaking {
                                break;
                            }
                            count += 1;
                            let next = guesses.pop().unwrap();
                            self.rollback_guess_completely(next);
                        }
                    }

                    for &contradiction in &self.active_contradiction {
                        debug_assert!(matches!(contradiction, ContradictionReason::Blocked(_)));
                    }
                    self.active_contradiction.retain(|r| {
                        let ContradictionReason::Blocked(var) = r else {
                            unreachable!()
                        };
                        self.duals.possible_assignments[var.index()].impossible()
                    });

                    if !self.active_contradiction.is_empty() {
                        panic!("!");
                    }

                    trace_flow!("ROLLED BACK {count} STEPS TO LEARN CLAUSE");
                    true
                } else {
                    trace_learn!("LEARNED IMPLICATION: {backup_clause:?}");
                    self.rollback_guess_completely(guess);
                    self.active_contradiction.retain(|r| {
                        let ContradictionReason::Blocked(var) = r else {
                            unreachable!()
                        };
                        self.duals.possible_assignments[var.index()].impossible()
                    });

                    while !self.active_contradiction.is_empty()
                        && let Some(guess) = guesses.pop()
                    {
                        self.rollback_guess_completely(guess);
                        self.active_contradiction.retain(|r| {
                            let ContradictionReason::Blocked(var) = r else {
                                unreachable!()
                            };
                            self.duals.possible_assignments[var.index()].impossible()
                        });
                    }

                    true
                }
            } else {
                debug_assert!(self.solos.forced_contradictions.is_empty());
                trace_learn!("FAILED TO LEARN (not a new clause)");
                self.rollback_guess(guess, guesses);
                false
            }
        } else {
            self.rollback_guess(guess, guesses);
            false
        }
    }

    fn reason_for(
        &self,
        var: Variable,
        guesses: &[UndoableGuess],
        current: &UndoableGuess,
    ) -> Option<AssignmentReason> {
        if current.variable == var || guesses.iter().any(|g| g.variable == var) {
            return None;
        }
        core::iter::once(&self.not_a_guess)
            .chain(guesses.iter().map(|g| &g.ledger))
            .chain(core::iter::once(&current.ledger))
            .find_map(|l| {
                l.assignments
                    .iter()
                    .find(|(v, _)| *v == var)
                    .map(|(_, r)| *r)
            })
    }

    fn minimize_learned(
        &self,
        clause: &mut Vec<Literal>,
        guesses: &[UndoableGuess],
        current: &UndoableGuess,
    ) {
        if clause.len() < 2 {
            return;
        }

        let present: alloc::collections::BTreeSet<Literal> = clause.iter().copied().collect();
        let mut scratch = [Literal(0), Literal(0)];

        let before = clause.len();
        clause.retain(|&lit| {
            let Some(reason) = self.reason_for(lit.variable(), guesses, current) else {
                return true;
            };
            let antecedent: &[Literal] = match reason {
                AssignmentReason::Guess(_) => return true,
                AssignmentReason::Clause(index) => self.clause_slice(index),
                AssignmentReason::Dual(left, rite) => {
                    scratch[0] = left;
                    scratch[1] = rite;
                    &scratch
                }
            };
            !antecedent
                .iter()
                .all(|&a| a.variable() == lit.variable() || present.contains(&a))
        });

        if clause.len() != before {
            trace_learn!("MINIMIZED {before} -> {} literals", clause.len());
        }
    }

    #[cfg(debug_assertions)]
    pub(crate) fn validate_rollback_ledger(&self, base: usize) {
        let ledger: alloc::collections::BTreeSet<Variable> = self
            .not_a_guess
            .assignments
            .iter()
            .map(|(var, _)| *var)
            .collect();
        let unrecorded = self.assign_order[base.min(self.assign_order.len())..]
            .iter()
            .filter(|lit| !ledger.contains(&lit.variable()))
            .copied()
            .collect::<Vec<_>>();
        debug_assert!(
            unrecorded.is_empty(),
            "search assignments on trail with no rollback record: {unrecorded:?} \
             (trail: {:?}, presolve depth: {base}, ledger: {:?})",
            self.assign_order,
            self.not_a_guess.assignments
        );
    }
}
