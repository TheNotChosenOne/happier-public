use crate::{Literal, Variable};
use alloc::vec::Vec;

#[cfg(feature = "serde")]
use bincode::{Decode, Encode};

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum AssignmentReason {
    Guess(Literal),
    Dual(Literal, Literal),
    Clause(u32),
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AssignmentLedger {
    pub(crate) assignments: Vec<(Variable, AssignmentReason)>,

    #[cfg(debug_assertions)]
    needs_undoing: bool,
}

#[cfg(debug_assertions)]
impl Drop for AssignmentLedger {
    fn drop(&mut self) {
        #[cfg(feature = "std")]
        let unwinding = std::thread::panicking();
        #[cfg(not(feature = "std"))]
        let unwinding = false;

        if self.needs_undoing && !self.assignments.is_empty() && !unwinding {
            panic!(
                "ledger dropped without rollback or merge; stranded assignments: {:?}",
                self.assignments
            );
        }
    }
}

impl AssignmentLedger {
    pub(crate) fn empty() -> Self {
        AssignmentLedger {
            assignments: Vec::with_capacity(0),
            #[cfg(debug_assertions)]
            needs_undoing: true,
        }
    }

    #[inline]
    pub(crate) fn mark_rolled_back(&mut self) {
        #[cfg(debug_assertions)]
        {
            self.needs_undoing = false;
        }
    }

    pub(crate) fn clear(&mut self) {
        self.assignments.clear();
    }

    pub(crate) fn rollback_drain(
        &mut self,
    ) -> impl Iterator<Item = (Variable, AssignmentReason)> + '_ {
        self.assignments.drain(..).rev()
    }

    pub(crate) fn learning_iter(&mut self) -> impl Iterator<Item = (Variable, AssignmentReason)> {
        self.assignments.iter().copied().rev()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    pub(crate) fn push_assignment(&mut self, var: Variable, reason: AssignmentReason) {
        debug_assert!(
            !self.assignments.iter().any(|(v, _)| *v == var),
            "variable {var:?} already assigned in this ledger {self:?}"
        );

        self.assignments.push((var, reason));
    }

    pub(crate) fn consume_assignments(&mut self, mut other: AssignmentLedger) {
        other.mark_rolled_back();
        self.assignments
            .extend(core::mem::take(&mut other.assignments));
    }

    pub(crate) fn consume(&mut self, mut other: UndoableGuess, assignments: &[Option<bool>]) {
        other.mark_rolled_back();
        let held = other
            .variable
            .literal(assignments[other.variable.index()].unwrap());
        self.assignments
            .push((other.variable, AssignmentReason::Guess(held)));
        self.assignments
            .extend(core::mem::take(&mut other.ledger.assignments));
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UndoableGuess {
    pub(crate) variable: Variable,
    pub(crate) ledger: AssignmentLedger,
}

impl UndoableGuess {
    pub(crate) fn new(variable: Variable) -> Self {
        UndoableGuess {
            variable,
            ledger: AssignmentLedger::empty(),
        }
    }
}

impl core::ops::Deref for UndoableGuess {
    type Target = AssignmentLedger;
    fn deref(&self) -> &AssignmentLedger {
        &self.ledger
    }
}

impl core::ops::DerefMut for UndoableGuess {
    fn deref_mut(&mut self) -> &mut AssignmentLedger {
        &mut self.ledger
    }
}

pub(crate) fn active_ledger<'a>(
    guesses: &'a mut [UndoableGuess],
    root: &'a mut AssignmentLedger,
) -> &'a mut AssignmentLedger {
    guesses.last_mut().map_or(root, |g| &mut g.ledger)
}

pub(crate) fn active_ledger_len(guesses: &[UndoableGuess], root: &AssignmentLedger) -> usize {
    guesses.last().map_or(root, |g| &g.ledger).assignments.len()
}
