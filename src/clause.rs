use crate::{
    ContradictionReason, Literal, Variable, unchecked_err, unchecked_find_swap, unchecked_get,
    unchecked_mut, unchecked_ok, unchecked_remove, unchecked_shift_left, unchecked_shift_right,
    unchecked_split,
};
use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

#[cfg(feature = "serde")]
use bincode::{Decode, Encode};
#[cfg(feature = "contracts")]
use contracts::{debug_ensures as ensures, debug_requires as requires};

pub trait Clauseish {
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn len(&self) -> usize;
    fn as_slice(&self) -> &[Literal];
    fn unassigned_count(&self) -> usize;
    fn satisfying_count(&self) -> usize;
    fn is_unit(&self) -> bool;
    fn is_unitish(&self) -> bool {
        self.unassigned_count() == 1 && self.satisfying_count() == 0
    }
    fn is_unassigned(&self, index: usize) -> bool;
    fn is_satisfying(&self, index: usize) -> Option<bool>;
    fn dyn_iter_all(&self) -> Box<dyn Iterator<Item = Literal> + '_>;
    fn dyn_iter_unassigned(&self) -> Box<dyn Iterator<Item = Literal> + '_>;
    fn dyn_iter_assigned(&self) -> Box<dyn Iterator<Item = Literal> + '_>;
    fn actual_unassigned(&self, assignments: &[Option<bool>]) -> usize;
    fn definitely_contradictory(&self) -> bool;
}

pub trait CowClause {
    fn to_owned(self) -> Vec<Literal>;
    fn len(&self) -> usize;
    fn get_literal(&self, i: usize) -> Literal;
    fn max_var(&self) -> Variable;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl CowClause for &[Literal] {
    fn to_owned(self) -> Vec<Literal> {
        self.to_vec()
    }
    fn len(&self) -> usize {
        <[Literal]>::len(self)
    }
    fn get_literal(&self, i: usize) -> Literal {
        self[i]
    }
    fn max_var(&self) -> Variable {
        self.iter().copied().max().map(Literal::variable).unwrap()
    }
}

impl CowClause for Vec<Literal> {
    fn to_owned(self) -> Vec<Literal> {
        self
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn get_literal(&self, i: usize) -> Literal {
        self[i]
    }
    fn max_var(&self) -> Variable {
        self.iter()
            .copied()
            .max()
            .map(Literal::variable)
            .unwrap_or(Variable(0))
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    // assigned literals are at the end of the vector
    pub(crate) literals: Vec<Literal>,
    pub(crate) unassigned: usize,
    pub(crate) satisfying: u32,
}

impl Clauseish for Clause {
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn len(&self) -> usize {
        self.literals.len()
    }

    fn as_slice(&self) -> &[Literal] {
        &self.literals
    }

    fn is_unit(&self) -> bool {
        self.unassigned == 1 && self.satisfying == 0
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    #[cfg_attr(feature = "contracts", requires(index < self.literals.len()))]
    fn is_unassigned(&self, index: usize) -> bool {
        index < self.unassigned
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    #[cfg_attr(feature = "contracts", requires(_index < self.literals.len()))]
    fn is_satisfying(&self, _index: usize) -> Option<bool> {
        None
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn unassigned_count(&self) -> usize {
        self.unassigned
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn satisfying_count(&self) -> usize {
        self.satisfying as usize
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn dyn_iter_all(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        Box::new(self.literals.iter().copied())
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn dyn_iter_unassigned(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        Box::new(self.literals.iter().take(self.unassigned).copied())
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn dyn_iter_assigned(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        Box::new(self.literals.iter().skip(self.unassigned).copied())
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_matches_assignments(assignments)))]
    fn actual_unassigned(&self, assignments: &[Option<bool>]) -> usize {
        self.literals
            .iter()
            .filter(|&&lit| assignments[lit.var_index()].is_none())
            .count()
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    fn definitely_contradictory(&self) -> bool {
        self.satisfying == 0 && self.unassigned == 0
    }
}

impl Clause {
    #[cfg_attr(feature = "contracts", requires(!literals.is_empty()))]
    #[cfg_attr(feature = "contracts", requires(literals.iter().copied().map(Literal::var_index).all(|idx| idx < assignments.len())))]
    #[cfg_attr(feature = "contracts", requires(literals.iter().map(|&lit| lit.variable()).collect::<alloc::collections::BTreeSet<_>>().len() == literals.len(), "no duplicate variables in clause"))]
    #[cfg_attr(feature = "contracts", ensures(ret.invariant_clause_matches_assignments(assignments)))]
    #[cfg_attr(feature = "contracts", ensures(ret.invariant_clause_self_consistent()))]
    pub fn new(mut literals: Vec<Literal>, assignments: &[Option<bool>]) -> Self {
        literals.sort_unstable_by_key(|&lit| assignments[lit.var_index()].is_some());
        let mut satisfying = 0;
        let mut assigned = 0;

        for &lit in &literals {
            if let Some(assigned_value) = assignments[lit.var_index()] {
                assigned += 1;
                if assigned_value == lit.is_true() {
                    satisfying += 1;
                }
            }
        }

        let unassigned = literals.len() - assigned;
        Self {
            literals,
            unassigned,
            satisfying,
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_has_variable(var), "variable must be in clause"))]
    #[cfg_attr(feature = "contracts", requires(self.literals.iter().any(|&lit| lit.variable() == var), "variable must be in clause"))]
    #[cfg_attr(feature = "contracts", ensures(ret.variable() == var, "returned literal matches variable"))]
    pub(crate) fn assigned_lit(&self, var: Variable) -> Literal {
        if cfg!(feature = "clause-sorted") {
            let assigned_slice = &self.literals[self.unassigned..];
            let index = assigned_slice
                .binary_search_by_key(&var, |&l| l.variable())
                .unwrap();
            assigned_slice[index]
        } else {
            let index = self
                .iter_assigned()
                .position(|lit| lit.variable() == var)
                .unwrap()
                + self.unassigned;
            self.literals[index]
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_has_assigned_var(var)))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_has_unassigned_var(var)))]
    #[allow(unused_parens)]
    #[cfg_attr(feature = "contracts", ensures(self.contract_unassigned_lit(var).is_true() == value -> old(self.satisfying) == self.satisfying + 1, "should track satisfying count correctly"))]
    #[cfg_attr(feature = "contracts", ensures(ret == (self.contract_unassigned_lit(var).is_true() == value)))]
    pub(crate) fn unassign(&mut self, var: Variable, value: bool) -> bool {
        if cfg!(feature = "clause-sorted") {
            let (unassigned_slice, assigned_slice) =
                unchecked_split(&self.literals, self.unassigned);
            let finding = assigned_slice.binary_search_by_key(&var, |&l| l.variable());
            let assigned_index = unchecked_ok(finding);
            let lit = *unchecked_get(assigned_slice, assigned_index);

            let finding = unassigned_slice.binary_search(&var.literal_neg());

            let unassigned_index = unchecked_err(finding);

            let upper_bound = self.unassigned + assigned_index;
            let total_moving = upper_bound - unassigned_index;
            debug_assert!(unassigned_index < self.literals.len());
            debug_assert!(unassigned_index <= upper_bound);
            debug_assert!(upper_bound < self.literals.len());
            unchecked_shift_right(&mut self.literals, unassigned_index, total_moving);

            *unchecked_mut(&mut self.literals, unassigned_index) = lit;

            self.unassigned += 1;
            if value == lit.is_true() {
                self.satisfying -= 1;
                true
            } else {
                false
            }
        } else {
            let pos = var.literal_pos();
            let neg = var.literal_neg();

            let length = self.literals.len();
            let lit = unchecked_find_swap(
                &mut self.literals,
                self.unassigned,
                length,
                self.unassigned,
                |l| l == pos || l == neg,
            );

            self.unassigned += 1;
            if lit.matching(value) {
                self.satisfying -= 1;
                true
            } else {
                false
            }
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_has_unassigned_var(var), "variable must be assigned"))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_has_assigned_var(var), "variable is now unassigned"))]
    #[allow(unused_parens)]
    #[cfg_attr(feature = "contracts", ensures(self.contract_assigned_lit(var).is_true() == value -> old(self.satisfying) + 1 == self.satisfying, "should track satisfying count correctly"))]
    #[cfg_attr(feature = "contracts", ensures(ret == (self.contract_assigned_lit(var).is_true() == value)))]
    pub(crate) fn assign(&mut self, var: Variable, value: bool) -> bool {
        if cfg!(feature = "clause-sorted") {
            let (unassigned_slice, assigned_slice) =
                unchecked_split(&self.literals, self.unassigned);

            let finding = unassigned_slice.binary_search_by_key(&var, |&l| l.variable());
            let unassigned_index = unchecked_ok(finding);

            let lit = *unchecked_get(unassigned_slice, unassigned_index);

            let finding = assigned_slice.binary_search(&var.literal_neg());
            let assigned_index = unchecked_err(finding);

            let upper_bound = self.unassigned + assigned_index;
            let total_moving = upper_bound - unassigned_index - 1;

            debug_assert!(unassigned_index < self.literals.len());
            debug_assert!(unassigned_index <= upper_bound);
            debug_assert!(upper_bound <= self.literals.len());

            unchecked_shift_left(&mut self.literals, unassigned_index, total_moving);

            *unchecked_mut(&mut self.literals, unassigned_index + total_moving) = lit;

            self.unassigned -= 1;
            if value == lit.is_true() {
                self.satisfying += 1;
                true
            } else {
                false
            }
        } else {
            let pos = var.literal_pos();
            let neg = var.literal_neg();

            let end = self.unassigned;
            self.unassigned -= 1;
            let lit = unchecked_find_swap(&mut self.literals, 0, end, self.unassigned, |l| {
                l == pos || l == neg
            });
            if lit.matching(value) {
                self.satisfying += 1;
                true
            } else {
                false
            }
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    #[cfg_attr(feature = "contracts", requires(self.unassigned == 1, "clause must have exactly one unassigned variable"))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_has_unassigned_var(ret.variable()), "variable is now unassigned"))]
    pub(crate) fn unit_unassigned(&self) -> Literal {
        debug_assert!(self.unassigned == 1);
        debug_assert!(self.satisfying == 0);
        self.literals[0]
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    pub fn has_one_unassigned(&self) -> bool {
        self.unassigned == 1
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    pub fn has_unassigned(&self) -> bool {
        self.unassigned > 0
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    pub fn iter_assigned(&self) -> impl Iterator<Item = Literal> + '_ {
        self.literals.iter().skip(self.unassigned).copied()
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    pub fn iter_unassigned(&self) -> impl Iterator<Item = Literal> + '_ {
        self.literals.iter().take(self.unassigned).copied()
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_clause_self_consistent(), "clause invariant holds"))]
    pub fn dyn_iter_all(&self) -> impl Iterator<Item = Literal> + '_ {
        self.literals.iter().copied()
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) struct UnitClause {
    literal: Literal,
    pub(crate) assigned: bool,
    pub(crate) satisfying: bool,
}

impl Clauseish for UnitClause {
    fn len(&self) -> usize {
        1
    }

    fn as_slice(&self) -> &[Literal] {
        core::slice::from_ref(&self.literal)
    }

    fn is_unit(&self) -> bool {
        !self.assigned
    }

    #[cfg_attr(feature = "contracts", requires(_index == 0))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn is_unassigned(&self, _index: usize) -> bool {
        !self.assigned
    }

    #[cfg_attr(feature = "contracts", requires(_index == 0))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn is_satisfying(&self, _index: usize) -> Option<bool> {
        Some(self.satisfying)
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn unassigned_count(&self) -> usize {
        if self.assigned { 0 } else { 1 }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn satisfying_count(&self) -> usize {
        self.satisfying as usize
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn dyn_iter_all(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        Box::new(core::iter::once(self.literal))
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn dyn_iter_unassigned(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        if self.assigned {
            Box::new(core::iter::empty())
        } else {
            Box::new(core::iter::once(self.literal))
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn dyn_iter_assigned(&self) -> Box<dyn Iterator<Item = Literal> + '_> {
        if self.assigned {
            Box::new(core::iter::once(self.literal))
        } else {
            Box::new(core::iter::empty())
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn actual_unassigned(&self, assignments: &[Option<bool>]) -> usize {
        assignments[self.literal.var_index()].is_none() as usize
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn definitely_contradictory(&self) -> bool {
        !self.satisfying && self.assigned
    }
}

#[allow(dead_code)]
impl UnitClause {
    #[allow(unused_parens)]
    #[cfg_attr(feature = "contracts", ensures(ret.invariant_unassigned_is_unsatisfying()))]
    pub fn new(literal: Literal, assignments: &[Option<bool>]) -> Self {
        if let Some(assigned) = assignments[literal.var_index()] {
            let satisfying = assigned == literal.is_true();
            Self {
                literal,
                assigned: true,
                satisfying,
            }
        } else {
            Self {
                literal,
                assigned: false,
                satisfying: false,
            }
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    fn assigned_lit(&self) -> Literal {
        self.literal
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    #[cfg_attr(feature = "contracts", requires(!self.assigned))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_is_unsatisfying()))]
    fn assign(&mut self) -> Literal {
        self.assigned = true;
        self.literal
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    #[cfg_attr(feature = "contracts", requires(self.assigned))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_unassigned_is_unsatisfying()))]
    fn unassign(&mut self) -> Literal {
        self.assigned = false;
        self.literal
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(!self.assigned))]
    #[cfg_attr(feature = "contracts", requires(!self.satisfying))]
    pub(crate) fn unit_unassigned(&self) -> Literal {
        self.literal
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    pub fn has_one_unassigned(&self) -> bool {
        !self.assigned
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    pub fn has_unassigned(&self) -> bool {
        !self.assigned
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    pub fn iter_assigned(&self) -> impl Iterator<Item = Literal> + '_ {
        if self.assigned {
            Some(self.literal).into_iter()
        } else {
            None.into_iter()
        }
    }

    #[inline(always)]
    #[cfg_attr(feature = "contracts", requires(self.invariant_unassigned_is_unsatisfying()))]
    pub fn dyn_iter_all(&self) -> impl Iterator<Item = Literal> + '_ {
        core::iter::once(self.literal)
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct SoloClauses {
    pub(crate) forced_assignments: BTreeSet<Literal>,
    pub(crate) forced_contradictions: BTreeSet<Literal>,
}

impl SoloClauses {
    #[cfg_attr(feature = "contracts", ensures(ret.invariant_forced_contradictions_tracked()))]
    pub(crate) fn new() -> Self {
        Self {
            forced_assignments: BTreeSet::new(),
            forced_contradictions: BTreeSet::new(),
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_forced_contradictions_tracked()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_forced_contradictions_tracked()))]
    pub(crate) fn insert(&mut self, literal: Literal) -> Option<Option<ContradictionReason>> {
        if self.forced_assignments.contains(&literal) {
            return None;
        }
        self.forced_assignments.insert(literal);
        if self.forced_assignments.contains(&literal.negate()) {
            self.forced_contradictions.insert(literal);
            self.forced_contradictions.insert(literal.negate());
            Some(Some(ContradictionReason::ForcedLiteral(literal)))
        } else {
            Some(None)
        }
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct PossibleAssignments {
    block_pos: u32,
    block_neg: u32,
}

impl core::fmt::Debug for PossibleAssignments {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.block_pos > 0 && self.block_neg > 0 {
            write!(f, "X")
        } else if self.block_pos > 0 {
            write!(f, "-")
        } else if self.block_neg > 0 {
            write!(f, "+")
        } else {
            write!(f, "±")
        }
    }
}

impl PossibleAssignments {
    pub(crate) fn new() -> Self {
        Self {
            block_pos: 0,
            block_neg: 0,
        }
    }

    pub(crate) fn any(&self) -> bool {
        debug_assert!(self.block_pos == 0 || self.block_neg == 0);
        0 == self.block_pos
    }

    pub(crate) fn can_be_pos(&self) -> bool {
        self.block_pos == 0
    }

    pub(crate) fn allows_any(&self) -> bool {
        self.block_pos == 0 || self.block_neg == 0
    }

    pub(crate) fn allows(&self, positive: bool) -> bool {
        if positive {
            self.block_pos == 0
        } else {
            self.block_neg == 0
        }
    }

    fn unblocked(&self) -> bool {
        self.block_pos == 0 && self.block_neg == 0
    }

    fn blocked(&self) -> bool {
        self.block_pos > 0 && self.block_neg > 0
    }

    fn is_possible(&self) -> bool {
        self.block_pos == 0 || self.block_neg == 0
    }

    pub(crate) fn impossible(&self) -> bool {
        self.block_pos > 0 && self.block_neg > 0
    }

    fn block(&mut self, positive: bool) {
        if positive {
            self.block_pos += 1;
        } else {
            self.block_neg += 1;
        }
    }

    fn unblock(&mut self, positive: bool) {
        if positive {
            debug_assert!(self.block_pos > 0);
            self.block_pos -= 1;
        } else {
            debug_assert!(self.block_neg > 0);
            self.block_neg -= 1;
        }
    }
}

#[cfg_attr(feature = "serde", derive(Encode, Decode))]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct DualClauses {
    pub(crate) implication_graph: Vec<Vec<Literal>>,
    pub(crate) inverse_implication: Vec<Vec<Literal>>,
    pub(crate) will_contradict: Vec<Option<Literal>>,
    pub(crate) forced_contradictions: BTreeSet<Variable>,
    pub(crate) possible_assignments: Vec<PossibleAssignments>,
    pub(crate) unit_forces: Vec<Literal>,
}

impl core::fmt::Debug for DualClauses {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.will_contradict.iter().any(|c| c.is_some()) {
            for (i, c) in self.will_contradict.iter().enumerate() {
                let implicator = Literal(i as u32);
                if let Some(implied) = c {
                    write!(f, "{implicator:?} => X{} ", implied.variable().0)?;
                }
            }
        }

        for contra in self.forced_contradictions.iter() {
            write!(f, "() => X{} ", contra.0)?;
        }

        for forced in self.unit_forces.iter() {
            write!(f, "FORCE {forced:?} ")?;
        }

        f.debug_struct("DualClauses")
            .field("implication_graph", &self.implication_graph)
            .field("inverse_implication", &self.inverse_implication)
            .field("possible_assignments", &self.possible_assignments)
            .field("will_contradict", &self.will_contradict)
            .finish()
    }
}

impl DualClauses {
    pub(crate) fn new() -> Self {
        Self {
            implication_graph: Vec::new(),
            inverse_implication: Vec::new(),
            will_contradict: Vec::new(),
            forced_contradictions: BTreeSet::new(),
            possible_assignments: Vec::new(),
            unit_forces: Vec::new(),
        }
    }

    pub(crate) fn add_one(&mut self) {
        self.add_n(1);
    }

    pub(crate) fn add_n(&mut self, n: usize) {
        self.implication_graph
            .resize(self.implication_graph.len() + 2 * n, Vec::with_capacity(0));
        self.will_contradict
            .resize(self.will_contradict.len() + 2 * n, None);
        self.inverse_implication.resize(
            self.inverse_implication.len() + 2 * n,
            Vec::with_capacity(0),
        );
        self.possible_assignments.resize(
            self.possible_assignments.len() + n,
            PossibleAssignments::new(),
        );
    }

    pub(crate) fn push_implication(
        &mut self,
        solos: &mut SoloClauses,
        left: Literal,
        rite: Literal,
        assignments: &[Option<bool>],
        changed: &mut bool,
        contradictions: &mut Vec<ContradictionReason>,
    ) {
        if left == rite {
            return;
        }
        self.implication_graph[left.lit_index()].push(rite);
        debug_assert!(!self.inverse_implication[rite.lit_index()].contains(&left));
        self.inverse_implication[rite.lit_index()].push(left);

        *changed = true;

        if assignments[rite.var_index()] == Some(rite.is_false()) {
            let possible = &mut self.possible_assignments[left.var_index()];
            possible.block(left.is_true());
            if possible.impossible() {
                contradictions.push(ContradictionReason::Blocked(left.variable()));
            }
        }

        if left.negate() == rite
            || self.implication_graph[left.lit_index()]
                .iter()
                .any(|l| l.negate() == rite)
        {
            self.will_contradict[left.lit_index()] = Some(rite);
            let possible = &mut self.possible_assignments[left.var_index()];
            let unblocked = possible.unblocked();
            possible.block(left.is_true());
            if possible.impossible() {
                contradictions.push(ContradictionReason::Blocked(left.variable()));
            }
            if unblocked && possible.blocked() {
                self.unit_forces.push(left.negate());
            } else if !unblocked && possible.impossible() {
                self.unit_forces
                    .retain(|&l| l.var_index() != left.var_index());
            }

            if self.will_contradict[left.negate().lit_index()].is_some() {
                self.forced_contradictions.insert(left.variable());
                contradictions.push(ContradictionReason::ForcedDual(left));
                self.unit_forces
                    .retain(|&l| l.var_index() != left.var_index());
            }

            if let Some(contradiction) = solos.insert(left.negate()).flatten() {
                contradictions.push(contradiction);
            }
        }
    }

    fn add_implication_for(
        &mut self,
        solos: &mut SoloClauses,
        left: Literal,
        rite: Literal,
        assignments: &[Option<bool>],
        changed: &mut bool,
        contradictions: &mut Vec<ContradictionReason>,
    ) {
        if left == rite {
            return;
        }
        let mut queue = vec![(left, rite)];
        while let Some((left, rite)) = queue.pop() {
            if self.implication_graph[left.lit_index()].contains(&rite) {
                continue;
            }
            for &impliers in &self.inverse_implication[left.lit_index()] {
                queue.push((impliers, rite));
            }
            for &implied in &self.implication_graph[rite.lit_index()] {
                queue.push((left, implied));
            }
            self.push_implication(solos, left, rite, assignments, changed, contradictions)
        }
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_implication_backgraph()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_implied_contradictions_propagated()))]
    #[cfg_attr(feature = "contracts", requires(assignments[literal.var_index()].is_none()))]
    pub(crate) fn assignment_will_contradict(
        &self,
        assignments: &[Option<bool>],
        literal: Literal,
    ) -> Option<Literal> {
        let lit_index = literal.lit_index();
        if let Some(contradiction) = self.will_contradict[lit_index] {
            return Some(contradiction);
        }
        for &implied in &self.implication_graph[lit_index] {
            let var_index = implied.var_index();
            if let Some(assigned) = assignments[var_index]
                && !implied.matching(assigned)
            {
                return Some(implied);
            }
        }
        None
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_implication_backgraph()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_implied_contradictions_propagated()))]
    #[cfg_attr(feature = "contracts", requires(assignments[literal.var_index()] == Some(!literal.is_true())))]
    pub(crate) fn reassignment_will_contradict(
        &self,
        assignments: &[Option<bool>],
        literal: Literal,
    ) -> Option<Literal> {
        let lit_index = literal.lit_index();
        if let Some(contradiction) = self.will_contradict[lit_index] {
            return Some(contradiction);
        }
        for &implied in &self.implication_graph[lit_index] {
            let var_index = implied.var_index();
            if let Some(assigned) = assignments[var_index]
                && !implied.matching(assigned)
            {
                return Some(implied);
            }
        }
        None
    }

    pub(crate) fn finalize_assignment(&mut self, literal: Literal) -> bool {
        let var_index = literal.var_index();
        let is_true = literal.is_true();
        let possible = unchecked_mut(&mut self.possible_assignments, var_index);
        debug_assert!(possible.allows(is_true));

        let unblocked = possible.unblocked();
        possible.block(!is_true);
        debug_assert!(possible.is_possible());
        if unblocked && possible.blocked() {
            self.unit_forces.push(literal.negate());
        } else if !unblocked && possible.impossible() {
            unchecked_remove(&mut self.unit_forces, |&l| {
                l.var_index() == literal.var_index()
            });
        }

        let mut contradiction = false;
        for implicators in unchecked_get(&self.inverse_implication, literal.negate().lit_index()) {
            let possible = unchecked_mut(&mut self.possible_assignments, implicators.var_index());
            let unblocked = possible.unblocked();
            possible.block(implicators.is_true());
            debug_assert!(possible.is_possible());
            if unblocked && possible.blocked() {
                self.unit_forces.push(implicators.negate());
            } else if !unblocked && possible.impossible() {
                unchecked_remove(&mut self.unit_forces, |&l| {
                    l.var_index() == implicators.var_index()
                });
            }

            contradiction |=
                !unchecked_get(&self.possible_assignments, implicators.var_index()).is_possible();
        }

        contradiction
    }

    pub(crate) fn finalize_unassignment(&mut self, literal: Literal) {
        let var_index = literal.var_index();
        let is_true = literal.is_true();

        unchecked_mut(&mut self.possible_assignments, var_index).unblock(!is_true);

        for implicators in unchecked_get(&self.inverse_implication, literal.negate().lit_index()) {
            unchecked_mut(&mut self.possible_assignments, implicators.var_index())
                .unblock(implicators.is_true());
        }
    }

    pub(crate) fn finalize_reassignment(&mut self, literal: Literal) -> bool {
        let var_index = literal.var_index();
        let is_true = literal.is_true();
        let possible = &mut self.possible_assignments[var_index];

        possible.unblock(is_true);
        debug_assert!(possible.allows(is_true));
        possible.block(!is_true);
        assert!(!possible.impossible());

        let mut contradiction = false;
        for implicators in &self.inverse_implication[literal.lit_index()] {
            self.possible_assignments[implicators.var_index()].unblock(implicators.is_true());
            contradiction |= !self.possible_assignments[implicators.var_index()].is_possible();
        }
        for implicators in &self.inverse_implication[literal.negate().lit_index()] {
            let possible = &mut self.possible_assignments[implicators.var_index()];
            possible.block(implicators.is_true());
            assert!(!possible.impossible());
            contradiction |= !self.possible_assignments[implicators.var_index()].is_possible();
        }
        contradiction
    }

    #[cfg_attr(feature = "contracts", requires(self.invariant_implication_backgraph()))]
    #[cfg_attr(feature = "contracts", requires(self.invariant_implied_contradictions_propagated()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_implication_backgraph()))]
    #[cfg_attr(feature = "contracts", ensures(self.invariant_implied_contradictions_propagated()))]
    pub(crate) fn expand_implication_graph(
        &mut self,
        solos: &mut SoloClauses,
        left: Literal,
        rite: Literal,
        assignments: &[Option<bool>],
        contradictions: &mut Vec<ContradictionReason>,
    ) -> bool {
        let contradictions_before = contradictions.len();
        let mut changed = false;
        let literals = [left, rite];
        for i in 0..2 {
            let left = literals[i];
            let rite = literals[1 - i];
            self.add_implication_for(
                solos,
                left.negate(),
                rite,
                assignments,
                &mut changed,
                contradictions,
            );
        }
        debug_assert!(contradictions.len() == contradictions_before || changed);
        changed
    }
}
