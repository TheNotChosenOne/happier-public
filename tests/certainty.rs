mod common;

use common::{easy_build, loud_solution_count};
use happier::{Control, SATState, just_satisfiable};
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::{Lit, TernaryVal};

fn solutions_of(solver: &mut SATState) -> usize {
    let cubes = solver.all_solutions();
    loud_solution_count(&cubes)
}

#[test]
fn presolve_solo_contradiction() {
    let mut solver = easy_build(0, "0");
    solver.add_clause(vec![happier::Variable::new(0).literal_neg()]);
    assert!(!solver.presolve());
    assert!(!solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn presolve_dual_implied_contradiction() {
    let mut solver = easy_build(
        1,
        "
        0
        ~0 1
        ~0 ~1
    ",
    );
    assert!(!solver.presolve());
    assert!(!solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn presolve_clause_contradiction_via_propagation() {
    let mut solver = easy_build(
        2,
        "
        0
        ~0 1 2
        ~1
        ~2
    ",
    );
    assert!(!solver.presolve());
    assert!(!solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn presolve_after_finished_solve() {
    let mut solver = easy_build(2, "0 1\n~1 2");
    assert!(solver.satisfiable(&mut just_satisfiable));
    assert!(solver.presolve());
    assert!(solver.satisfiable(&mut just_satisfiable));
    assert_eq!(vec![true, true, true], solver.can_pos(0..3));

    let mut unsat = easy_build(0, "0");
    unsat.add_clause(vec![happier::Variable::new(0).literal_neg()]);
    assert!(!unsat.satisfiable(&mut just_satisfiable));
    assert!(!unsat.presolve());
}

#[test]
fn presolve_is_idempotent() {
    let mut solver = easy_build(2, "0 1\n~1 2");
    assert!(solver.presolve());
    assert!(solver.presolve());
    assert!(solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn can_pos_unsat_all_false() {
    let mut solver = easy_build(
        2,
        "
        0 1 2
        0 1 ~2
        0 ~1 2
        0 ~1 ~2
        ~0 1 2
        ~0 1 ~2
        ~0 ~1 2
        ~0 ~1 ~2
    ",
    );
    assert_eq!(vec![false; 3], solver.can_pos(0..3));
}

#[test]
fn can_pos_solo_contradiction_all_false() {
    let mut solver = easy_build(1, "0\n~0");
    assert_eq!(vec![false; 2], solver.can_pos(0..2));
}

#[test]
fn can_pos_unsat_is_all_false_via_unsatisfied_big_clause() {
    let mut solver = easy_build(
        10,
        "
        ~8
        ~0 4
        ~10 ~0
        0 ~7
        10 ~4 ~7
        8 ~3 0
        7 3
        ~3 10
    ",
    );
    assert!(!solver.clone().satisfiable(&mut just_satisfiable));
    assert_eq!(vec![false; 11], solver.can_pos(0..11));
}

#[test]
fn can_pos_unsat_is_all_false_second_instance() {
    let mut solver = easy_build(
        10,
        "
        8 ~7 2
        ~4 ~8
        ~8 ~7
        ~9 2
        6
        9 ~0
        ~1 ~9
        7 9
        0 7
        1 ~0 10
        7 ~10
        ~2 8
    ",
    );
    assert!(!solver.clone().satisfiable(&mut just_satisfiable));
    assert_eq!(vec![false; 11], solver.can_pos(0..11));
}

#[test]
fn can_pos_unsat_is_all_false_third_instance() {
    let mut solver = easy_build(
        10,
        "
        ~0 ~2
        ~6 9
        3 8 ~9
        ~1 8
        3 ~7 2
        1 6
        ~7 1 4
        ~4
        ~1 10
        ~8 7
        ~8 4 9
        ~9 ~3
        ~1 ~10 0
    ",
    );
    assert!(!solver.clone().satisfiable(&mut just_satisfiable));
    assert_eq!(vec![false; 11], solver.can_pos(0..11));
}

#[test]
fn can_pos_negative_backbone() {
    let mut solver = easy_build(2, "~0\n0 1 2");
    assert_eq!(vec![false, true, true], solver.can_pos(0..3));
}

#[test]
fn can_pos_partial_range() {
    let mut solver = easy_build(2, "~1");
    assert_eq!(vec![false, true], solver.can_pos(1..3));
    assert_eq!(vec![true], solver.can_pos(0..1));
    assert_eq!(Vec::<bool>::new(), solver.can_pos(0..0));
}

#[test]
fn can_pos_after_satisfiable_without_unroll() {
    let mut solver = easy_build(2, "0 1\n~1 2");
    assert!(solver.satisfiable(&mut just_satisfiable));
    assert_eq!(vec![true, true, true], solver.can_pos(0..3));
}

#[test]
fn can_pos_incremental_narrowing() {
    let mut solver = easy_build(2, "0 1\n~1 2");
    assert_eq!(vec![true, true, true], solver.can_pos(0..3));
    solver.add_clause(vec![happier::Variable::new(0).literal_neg()]);
    assert_eq!(vec![false, true, true], solver.can_pos(0..3));
    solver.add_clause(vec![happier::Variable::new(2).literal_neg()]);
    assert_eq!(vec![false; 3], solver.can_pos(0..3));
}

#[test]
fn can_pos_sees_duals_added_after_a_solve() {
    let mut solver = SATState::new();
    solver.new_variable_at(8);
    solver.add_clause(vec![happier::Variable::new(3).literal_neg()]);
    solver.add_clause(vec![happier::Variable::new(7).literal_pos()]);
    solver.add_clause(vec![
        happier::Variable::new(7).literal_neg(),
        happier::Variable::new(3).literal_pos(),
        happier::Variable::new(6).literal_neg(),
    ]);
    assert!(solver.satisfiable(&mut just_satisfiable));
    solver.add_clause(vec![
        happier::Variable::new(6).literal_pos(),
        happier::Variable::new(8).literal_neg(),
    ]);
    let out = solver.can_pos(0..9);
    assert!(!out[8], "8 is false in every model: {out:?}");

    let mut check = solver.clone();
    check.add_clause(vec![happier::Variable::new(8).literal_pos()]);
    assert!(!check.satisfiable(&mut just_satisfiable));
}

#[test]
fn can_pos_retries_variables_wiped_by_backjump() {
    let spec: &[&[(u32, bool)]] = &[
        &[(3, true)],
        &[(2, true)],
        &[(0, false), (10, false), (3, false)],
        &[(10, false), (2, false), (0, true)],
        &[(1, false), (7, false), (0, false)],
    ];
    let mut solver = SATState::new();
    solver.new_variable_at(10);
    for clause in spec {
        let lits: Vec<happier::Literal> = clause
            .iter()
            .map(|&(v, p)| happier::Variable::new(v).literal(p))
            .collect();
        solver.add_clause(lits);
    }
    let out = solver.can_pos(0..11);
    assert!(out[7], "7=T is satisfiable (0=F, 10=F): {out:?}");
}

#[test]
fn can_pos_repeat_is_stable() {
    let mut solver = easy_build(3, "0 1\n~1 2\n~3 0");
    let first = solver.can_pos(0..4);
    let second = solver.can_pos(0..4);
    assert_eq!(first, second);
}

#[test]
fn control_stop_halts_the_tour() {
    let mut solver = easy_build(2, "0 1 2");
    let mut seen = 0;
    let result = solver.satisfiable(&mut |_| {
        seen += 1;
        Control::Stop
    });
    assert!(result);
    assert_eq!(1, seen);
}

#[test]
fn unconstrained_variables_solve_trivially() {
    let mut solver = SATState::new();
    solver.new_variable_at(4);
    assert!(solver.satisfiable(&mut just_satisfiable));
    assert_eq!(vec![true; 5], solver.can_pos(0..5));
}

#[test]
fn tautologies_are_dropped() {
    let v0 = happier::Variable::new(0);
    let v1 = happier::Variable::new(1);
    let mut solver = SATState::new();
    solver.new_variable_at(1);
    solver.add_clause(vec![v0.literal_pos(), v0.literal_neg()]);
    solver.add_clause(vec![v0.literal_pos(), v0.literal_neg(), v1.literal_pos()]);
    assert_eq!(4, solutions_of(&mut solver));
}

#[test]
fn duplicate_literals_collapse() {
    let v0 = happier::Variable::new(0);
    let v1 = happier::Variable::new(1);
    let mut solver = SATState::new();
    solver.new_variable_at(1);
    solver.add_clause(vec![v0.literal_pos(), v0.literal_pos()]);
    solver.add_clause(vec![v0.literal_pos(), v0.literal_pos(), v1.literal_neg()]);
    assert_eq!(vec![true, true], solver.can_pos(0..2));
    let mut check = solver.clone();
    check.add_clause(vec![v0.literal_neg()]);
    assert!(!check.satisfiable(&mut just_satisfiable));
}

#[test]
fn duplicate_clauses_are_added_once() {
    let solver = easy_build(2, "0 1 2\n0 1 2\n0 1 2");
    assert_eq!(1, solver.iter_all_clauses().count());
}

#[test]
fn new_variable_at_is_monotonic() {
    let mut solver = SATState::new();
    solver.new_variable_at(3);
    assert_eq!(4, solver.variable_count());
    solver.new_variable_at(1);
    assert_eq!(4, solver.variable_count());
    assert_eq!(4, solver.assignments().len());
}

#[test]
fn variable_and_literal_primitives() {
    let mut solver = SATState::new();
    assert_eq!(None, solver.max_known_variable());
    assert_eq!(0, solver.variable_count());
    solver.new_variable_at(6);
    assert_eq!(Some(happier::Variable::new(6)), solver.max_known_variable());
    assert_eq!(7, solver.variable_count());

    let v = happier::Variable::new(5);
    let (pos, neg) = v.literal_both();
    assert_eq!(v.literal_pos(), pos);
    assert_eq!(v.literal_neg(), neg);
    assert!(pos.is_true() && !pos.is_false());
    assert!(neg.is_false() && !neg.is_true());
    assert_eq!(pos.negate(), neg);
    assert_eq!(v, pos.variable());
    assert_eq!(v, neg.variable());
    assert_eq!(5, pos.var_index());
    assert_eq!(11, pos.lit_index());
    assert_eq!(10, neg.lit_index());
    assert!(pos.matching(true) && !pos.matching(false));
    assert!(neg.matching(false) && !neg.matching(true));
    assert_eq!("5", format!("{pos:?}"));
    assert_eq!("¬5", format!("{neg:?}"));
}

#[test]
fn rsat_lit_val_respects_literal_sign() {
    let mut solver = SATState::new();
    solver.add_unit(Lit::positive(0)).unwrap();
    solver.add_unit(Lit::negative(1)).unwrap();
    assert_eq!(SolverResult::Sat, solver.solve().unwrap());

    assert_eq!(TernaryVal::True, solver.lit_val(Lit::positive(0)).unwrap());
    assert_eq!(TernaryVal::False, solver.lit_val(Lit::negative(0)).unwrap());
    assert_eq!(TernaryVal::True, solver.lit_val(Lit::negative(1)).unwrap());
    assert_eq!(TernaryVal::False, solver.lit_val(Lit::positive(1)).unwrap());
    assert_eq!(
        TernaryVal::DontCare,
        solver.lit_val(Lit::positive(7)).unwrap()
    );
}

#[test]
fn rsat_solve_unsat() {
    let mut solver = SATState::new();
    solver.add_unit(Lit::positive(0)).unwrap();
    solver.add_unit(Lit::negative(0)).unwrap();
    assert_eq!(SolverResult::Unsat, solver.solve().unwrap());
}

#[test]
fn rsat_clause_adapter_carries_every_literal() {
    let clause: rustsat::types::Clause = vec![Lit::positive(0), Lit::negative(1), Lit::positive(2)]
        .as_slice()
        .into();
    let mut solver = SATState::new();
    solver.new_variable_at(2);
    solver.add_clause(happier::rsat::ClauseAdapter::new(&clause));
    assert_eq!(1, solver.iter_all_clauses().count());

    solver.add_unit(Lit::negative(0)).unwrap();
    solver.add_unit(Lit::positive(1)).unwrap();
    solver.add_unit(Lit::negative(2)).unwrap();
    assert_eq!(SolverResult::Unsat, solver.solve().unwrap());
}

#[test]
fn rsat_extend_owned_and_borrowed() {
    let mut cnf = rustsat::instances::Cnf::new();
    cnf.add_clause(vec![Lit::positive(0), Lit::positive(1)].as_slice().into());
    cnf.add_clause(vec![Lit::negative(1), Lit::positive(2)].as_slice().into());

    let mut borrowed = SATState::new();
    borrowed.extend(cnf.iter());
    assert_eq!(SolverResult::Sat, borrowed.solve().unwrap());

    let mut owned = SATState::new();
    owned.extend(cnf.iter().cloned());
    assert_eq!(SolverResult::Sat, owned.solve().unwrap());

    assert_eq!(3, borrowed.variable_count());
    assert_eq!(3, owned.variable_count());
}
