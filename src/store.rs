use crate::clause::{Clause, Clauseish};
use crate::{BitVec, Literal, Variable, unchecked_get, unchecked_mut, unchecked_remove};
use alloc::vec::Vec;

#[cfg(feature = "serde")]
use bincode::{Decode, Encode};
#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct UnitTrackerBit {
    count_big: usize,
    next_big: usize,
    indices_big: BitVec,
}

impl UnitTrackerBit {
    pub(crate) fn new() -> Self {
        Self {
            count_big: 0,
            next_big: 0,
            indices_big: BitVec::new(),
        }
    }

    #[inline(always)]
    pub(crate) fn any(&self) -> Option<u32> {
        if self.count_big > 0 {
            self.indices_big.any().map(|i| i as u32)
        } else {
            None
        }
    }

    #[allow(dead_code)]
    pub(crate) fn contains(&self, clause_index: u32) -> bool {
        self.indices_big.contains(clause_index as usize)
    }

    #[inline(always)]
    pub(crate) fn insert(&mut self, clause_index: u32) {
        self.count_big += 1;
        self.indices_big.insert(clause_index as usize);
    }

    #[inline(always)]
    fn remove(&mut self, clause_index: u32) {
        self.count_big -= 1;
        self.indices_big.remove(clause_index as usize);
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.count_big
    }

    pub(crate) fn max_entries(&mut self, big: usize) {
        self.indices_big.resize(big);
    }
}

pub(crate) type UnitTracker = UnitTrackerBit;

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClauseList {
    pub(crate) clauses: Vec<u32>,
}

impl ClauseList {
    pub(crate) fn new() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    #[inline(always)]
    pub(crate) fn insert(&mut self, index: u32) {
        self.clauses.push(index);
    }

    #[inline(always)]
    pub(crate) fn remove_big(&mut self, index: u32) {
        unchecked_remove(&mut self.clauses, |&i| i == index);
    }

    #[cfg(feature = "contracts")]
    pub(crate) fn iter_big(&self) -> impl Iterator<Item = u32> + '_ {
        self.clauses.iter().copied()
    }

    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.clauses.len()
    }

    #[inline(always)]
    pub(crate) fn at(&self, i: usize) -> u32 {
        *unchecked_get(&self.clauses, i)
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct DesatisfyStack {
    pub(crate) stack: Vec<u32>,
    markers: Vec<(Literal, u32)>,
    pub(crate) stacked: BitVec,
}

impl DesatisfyStack {
    pub(crate) fn new() -> Self {
        Self {
            stack: Vec::new(),
            markers: Vec::new(),
            stacked: BitVec::new(),
        }
    }

    pub(crate) fn retroactive_one(
        &mut self,
        clause_index: u32,
        clause: &mut Clause,
        assignments: &[Option<bool>],
    ) {
        let mut satisfied = clause
            .literals
            .iter()
            .filter(|&&lit| {
                if let Some(assigned) = assignments[lit.var_index()] {
                    lit.matching(assigned)
                } else {
                    false
                }
            })
            .count();
        debug_assert!(satisfied > 0);
        let mut after_count = 0;
        for (i, &(assignment, count)) in self.markers.iter().enumerate().rev() {
            after_count += count;
            if let Some(literal) = clause
                .literals
                .iter()
                .find(|&&l| l.variable() == assignment.variable())
            {
                if *literal == assignment {
                    satisfied -= 1;
                }
                if satisfied == 0 {
                    self.markers[i].1 += 1;
                    self.stack
                        .insert(self.stack.len() - after_count as usize, clause_index);
                    self.stacked.insert(clause_index as usize);
                    return;
                } else {
                    clause.unassign(assignment.variable(), assignment.is_true());
                }
            }
        }
        unreachable!("clause should eventually be unsatisfied");
    }

    #[inline(always)]
    pub(crate) fn push_one(&mut self, clause_index: u32) {
        self.stack.push(clause_index);
        self.stacked.insert(clause_index as usize);
    }

    #[inline(always)]
    pub(crate) fn mark(&mut self, assignment: Literal, count: u32) {
        self.markers.push((assignment, count));
    }

    #[inline(always)]
    pub(crate) fn is_empty(&self) -> bool {
        self.markers.is_empty()
    }

    pub(crate) fn pop_set(&mut self) -> impl Iterator<Item = u32> + '_ {
        let (_, count) = self.markers.pop().unwrap();
        for &clause_index in &self.stack[self.stack.len() - count as usize..] {
            self.stacked.remove(clause_index as usize);
        }
        self.stack.drain(self.stack.len() - count as usize..)
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ClauseStore {
    pub(crate) clauses: Vec<Clause>,

    pub(crate) unsatisfied_clauses: BitVec,
    pub(crate) unsatisfied: usize,

    pub(crate) unit_indices: UnitTracker,

    pub(crate) clause_presence: Vec<u32>,
    pub(crate) usages: Vec<ClauseList>,
}

impl ClauseStore {
    pub(crate) fn new() -> Self {
        Self {
            clauses: Vec::with_capacity(1024),
            unsatisfied_clauses: BitVec::new(),
            unsatisfied: 0,
            unit_indices: UnitTracker::new(),
            clause_presence: Vec::with_capacity(256),
            usages: Vec::with_capacity(256),
        }
    }

    #[inline(always)]
    pub(crate) fn slice(&self, index: u32) -> &[Literal] {
        self.clauses[index as usize].as_slice()
    }

    #[inline(always)]
    pub(crate) fn is_contradiction(&self, index: u32) -> bool {
        self.clauses[index as usize].definitely_contradictory()
    }

    #[inline(always)]
    pub(crate) fn mark_unsatisfied(&mut self, clause_index: u32) {
        self.unsatisfied_clauses.insert(clause_index as usize);
        self.unsatisfied += 1;
    }

    #[inline(always)]
    pub(crate) fn reassign_in_clause(
        &mut self,
        clause_index: u32,
        var: Variable,
        value: bool,
        contradiction_index: &mut Option<u32>,
    ) -> bool {
        let Self {
            clauses,
            unsatisfied_clauses,
            unsatisfied,
            unit_indices,
            ..
        } = self;
        let clause = unchecked_mut(clauses, clause_index as usize);
        let pre_unit = 0 == clause.satisfying && 1 == clause.unassigned;
        let lit = clause.assigned_lit(var);
        let mut newly_satisfied = false;
        if value == lit.is_true() {
            clause.satisfying += 1;
            if 1 == clause.satisfying {
                unsatisfied_clauses.remove(clause_index as usize);
                *unsatisfied -= 1;
                newly_satisfied = true;
            }
        } else {
            clause.satisfying -= 1;
            if 0 == clause.satisfying {
                *unsatisfied += 1;
                unsatisfied_clauses.insert(clause_index as usize);
            }
        }
        let post_unit = 0 == clause.satisfying && 1 == clause.unassigned;
        if post_unit != pre_unit {
            if post_unit {
                unit_indices.insert(clause_index);
            } else {
                unit_indices.remove(clause_index);
            }
        }
        if 0 == clause.satisfying && 0 == clause.unassigned {
            *contradiction_index = Some(clause_index);
        }
        newly_satisfied
    }

    #[inline(always)]
    pub(crate) fn unassign_in_clause(&mut self, clause_index: u32, var: Variable, value: bool) {
        let clause = &mut self.clauses[clause_index as usize];
        let pre_sat = clause.satisfying_count() > 0;
        let pre_unit = 0 == clause.satisfying_count() && 1 == clause.unassigned_count();
        clause.unassign(var, value);
        let post_unit = 0 == clause.satisfying_count() && 1 == clause.unassigned_count();
        let post_sat = clause.satisfying_count() > 0;
        if pre_sat && !post_sat {
            self.mark_unsatisfied(clause_index);
        }
        if post_unit != pre_unit {
            if post_unit {
                self.unit_indices.insert(clause_index);
            } else {
                self.unit_indices.remove(clause_index);
            }
        }
    }

    #[inline(always)]
    pub(crate) fn assign_in_clause(
        &mut self,
        clause_index: u32,
        var: Variable,
        value: bool,
        contradiction_index: &mut Option<u32>,
    ) -> bool {
        let Self {
            clauses,
            unsatisfied_clauses,
            unsatisfied,
            unit_indices,
            ..
        } = self;
        let clause = unchecked_mut(clauses, clause_index as usize);
        debug_assert_eq!(0, clause.satisfying);
        debug_assert!(unsatisfied_clauses.contains(clause_index as usize));
        let is_satisfying = clause.assign(var, value);
        if is_satisfying {
            unsatisfied_clauses.remove(clause_index as usize);
            if clause.satisfying == 1 {
                *unsatisfied -= 1;
            }
            if clause.satisfying == 1 && clause.unassigned == 0 {
                unit_indices.remove(clause_index);
            }
            true
        } else if 0 == clause.satisfying {
            if clause.unassigned == 0 {
                unit_indices.remove(clause_index);
                *contradiction_index = Some(clause_index);
            } else if clause.unassigned == 1 {
                unit_indices.insert(clause_index);
            }
            false
        } else {
            false
        }
    }
}
