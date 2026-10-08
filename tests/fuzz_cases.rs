mod common;

use common::{easy_build, loud_solution_count, validate_solve};
use happier::{Control, SATState, just_satisfiable, tour_all_solutions};
use rustsat::solvers::Solve;
use rustsat::types::Var;

#[test]
fn fuzz_case_23() {
    let mut solver = easy_build(
        7,
        "
        5 ~6 ~4
        7 ~3 ~5
        ~0 6 5
        ~3 ~7 ~5
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(128, solution_count);
}

#[test]
fn fuzz_case_22() {
    let mut solver = easy_build(
        2,
        "
        ~0 ~1 ~2
           ~1  2
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(5, solution_count);
}

#[test]
fn fuzz_case_21() {
    let mut solver = easy_build(
        4,
        "
        ~1  3 ~4
        ~0  2  3
        ~0 ~2  3
        ~1 ~3 ~4
         4
        ~0  1 ~3
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(4, solution_count);
}

#[test]
fn fuzz_case_20() {
    let mut solver = easy_build(
        2,
        "
        ~0  2 ~1
        ~0 ~2 ~1
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(6, solution_count);
}

#[test]
fn fuzz_case_19() {
    let mut solver = easy_build(
        1,
        "
        ~0 1
         0
        ~1 0
        ~0 ~1
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(0, solution_count);
}

#[test]
fn fuzz_case_18() {
    let mut solver = easy_build(
        2,
        "
        ~0 ~1  2
            1
        ~0 ~1 ~2
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(2, solution_count);
}

#[test]
fn fuzz_case_17() {
    let mut solver = easy_build(
        3,
        "
        0    ~2  3
          ~1 ~2 ~3
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(12, solution_count);
}

#[test]
fn fuzz_case_16() {
    let mut solver = easy_build(
        4,
        "
        ~3 0 4 ~1
        ~3 ~4 ~2
    ",
    );
    let all_solutions = solver.all_solutions();
    for solution in all_solutions {
        print!("Solution: ");
        for (i, &v) in solution.iter().enumerate() {
            match v {
                Some(true) => print!(" {} ", i),
                Some(false) => print!("~{} ", i),
                None => print!("?{} ", i),
            }
        }
        println!();
    }
}

#[test]
fn fuzz_case_15() {
    let mut solver = easy_build(
        7,
        "
        ~6 0 7 ~1
        ~6 ~7 ~4
    ",
    );
    solver.satisfiable(&mut tour_all_solutions);
}

#[test]
fn fuzz_case_14() {
    let mut solver = easy_build(
        7,
        "
        7 ~5 3
        ~0 7 ~3 ~5
        ~5 ~7 ~2 ~5
    ",
    );
    solver.satisfiable(&mut tour_all_solutions);
    solver.unroll();
}

#[test]
fn fuzz_case_13() {
    let mut solver = SATState::new();
    let x1 = solver.new_variable_at(1);
    let x2 = solver.new_variable_at(2);
    let x4 = solver.new_variable_at(4);
    let x6 = solver.new_variable_at(6);
    let x7 = solver.new_variable_at(7);
    solver.add_clause(vec![x7.literal_pos(), x4.literal_pos(), x6.literal_neg()]);
    solver.add_clause(vec![
        x2.literal_neg(),
        x6.literal_neg(),
        x1.literal_neg(),
        x7.literal_neg(),
    ]);
    solver.satisfiable(&mut tour_all_solutions);
    solver.unroll();
}

#[test]
fn fuzz_case_12() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable_at(0);
    solver.add_clause(vec![x0.literal_neg()]);
    solver.satisfiable(&mut tour_all_solutions);
    solver.unroll();

    let x1 = solver.new_variable_at(1);
    let x2 = solver.new_variable_at(2);
    solver.add_clause(vec![x0.literal_neg()]);
    solver.add_clause(vec![x0.literal_neg(), x1.literal_neg(), x2.literal_neg()]);
    solver.satisfiable(&mut tour_all_solutions);
}

#[test]
fn fuzz_case_10() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let _ = solver.new_variable();
    let x2 = solver.new_variable();
    let x3 = solver.new_variable();
    let x4 = solver.new_variable();
    let x5 = solver.new_variable();
    let x6 = solver.new_variable();
    let x7 = solver.new_variable();
    solver.add_clause(vec![x0.literal_pos(), x2.literal_pos(), x5.literal_neg()]);
    solver.add_clause(vec![x3.literal_pos(), x7.literal_neg(), x6.literal_neg()]);
    solver.add_clause(vec![x4.literal_pos(), x3.literal_pos()]);
    solver.add_clause(vec![x4.literal_neg(), x7.literal_pos()]);
    solver.add_clause(vec![
        x4.literal_neg(),
        x7.literal_neg(),
        x4.literal_neg(),
        x6.literal_pos(),
    ]);
    solver.add_clause(vec![x2.literal_neg()]);
    solver.add_clause(vec![x6.literal_neg(), x7.literal_neg(), x4.literal_neg()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_9a() {
    let mut solver = easy_build(
        7,
        "
        7 ~1 ~6
        5 6 ~4
        ~6 ~1 ~7
        ",
    );
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_9b() {
    let mut solver = easy_build(
        4,
        "
        ~0 ~3  4
        ~1  2  3
        ~0 ~3 ~4
        ",
    );
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_8() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.new_variable();
    let x3 = solver.new_variable();
    solver.add_clause(vec![x3.literal_pos(), x1.literal_pos(), x0.literal_pos()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_7() {
    let mut solver = SATState::new();
    let x2 = solver.new_variable_at(2);
    solver.add_clause(vec![x2.literal_neg()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_6() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    let x4 = solver.new_variable();
    let x5 = solver.new_variable();
    let x6 = solver.new_variable();
    let x7 = solver.new_variable();
    solver.add_clause(vec![x6.literal_pos(), x6.literal_neg(), x1.literal_neg()]);
    solver.add_clause(vec![x5.literal_pos(), x4.literal_neg(), x0.literal_neg()]);
    solver.add_clause(vec![x7.literal_neg(), x6.literal_neg(), x1.literal_pos()]);
    solver.add_clause(vec![x1.literal_neg(), x6.literal_neg()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_5() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x0.literal_pos(), x1.literal_pos()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_case_4() {
    let mut solver = SATState::new();
    println!("Solver before: {:?}", solver);
    let x0 = solver.new_variable();
    println!("Solver after: {:?}", solver);
    solver.add_clause(vec![x0.literal_pos()]);
    println!("Solver after: {:?}", solver);
    assert!(solver.satisfiable(&mut tour_all_solutions));
    println!("Solver after: {:?}", solver);
    solver.unroll();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x0.literal_neg(), x1.literal_neg()]);
    assert!(solver.satisfiable(&mut tour_all_solutions));
    println!("Solver after: {:?}", solver);
}

#[test]
fn fuzz_disagreement_simplified() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x1.literal_pos(), x0.literal_pos()]);
    solver.add_clause(vec![x0.literal_neg(), x0.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn fuzz_case_2() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x0.literal_pos(), x1.literal_pos()]);
    solver.add_clause(vec![x0.literal_pos(), x1.literal_neg()]);
    println!("Solver before: {:?}", solver);
    println!("Solver before: {:?}", solver);
    let mut solutions = Vec::new();
    let solve_response = solver.satisfiable(&mut |state| {
        let assignment = state
            .assignments()
            .iter()
            .map(|&a| a.unwrap_or(false))
            .collect::<Vec<_>>();
        solutions.push(assignment);
        Control::Continue
    });
    assert!(solve_response, "should be satisfiable");
    solutions.sort_unstable();
    assert_eq!(solutions, vec![vec![true, false], vec![true, true],]);
}

#[test]
fn fuzz_case_3() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x0.literal_neg()]);
    solver.add_clause(vec![x1.literal_pos()]);

    println!("Solver before: {:?}", solver);
    validate_solve(&mut solver, true);
    println!("Solver  after: {:?}", solver);
    for i in 0..2 {
        let mut active = solver.clone();
        println!("Solver before: {:?}", solver);
        active.add_unit(Var::new(i as u32).pos_lit()).expect("!");
        active.presolve();
        active.satisfiable(&mut just_satisfiable);
    }
}

#[test]
fn learned_clause_repeats_a_variable() {
    let mut solver = easy_build(
        6,
        "
        ~0 ~1 ~6 ~2 ~5
         5  3
         3 ~5 ~4
         3  4
    ",
    );
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(62, solution_count, "62 of the 128 assignments satisfy this");

    let mut seen = std::collections::HashSet::new();
    let mut concrete = Vec::new();
    for solution in &all_solutions {
        common::assignment_to_solutions(solution, &mut concrete);
    }
    for assignment in &concrete {
        assert!(
            seen.insert(assignment.clone()),
            "solution tour visited {assignment:?} twice"
        );
    }
}

#[test]
fn readding_a_clause_under_a_contradiction() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    let x2 = solver.new_variable();

    solver.add_clause(vec![x0.literal_pos(), x1.literal_neg()]);
    solver.add_clause(vec![x2.literal_neg()]);
    solver.add_clause(vec![x2.literal_pos()]);
    solver.add_clause(vec![x0.literal_pos(), x1.literal_neg()]);

    assert!(
        !solver.satisfiable(&mut just_satisfiable),
        "~2 and 2 cannot both hold"
    );
}

#[test]
fn wrongly_reports_unsat() {
    let spec = "
         4 ~5 ~0
         3
        ~2 ~4 ~0
         4  5 ~3
        ~4 ~3 ~5
        ~1 ~0 ~4
         5 ~4
    ";

    let mut solver = easy_build(5, spec);
    assert!(
        solver.satisfiable(&mut just_satisfiable),
        "instance is satisfiable: ¬0 ?1 ?2 3 ¬4 5 are all solutions"
    );

    let mut solver = easy_build(5, spec);
    let all_solutions = solver.all_solutions();
    let solution_count = loud_solution_count(&all_solutions);
    assert_eq!(4, solution_count);
}

#[test]
fn abandoned_flip_drops_solutions() {
    let spec = "
         3 ~3
         3  0 ~1
         0 ~1 ~3
         4 ~2  0
         1 ~3
        ~2  4
    ";
    let mut solver = easy_build(4, spec);
    let all_solutions = solver.all_solutions();
    assert_eq!(12, loud_solution_count(&all_solutions));
}

#[test]
fn exhaustive_solve_poisons_later_forced_units() {
    let spec = "
         9 ~11
         4  1  9  2 11
    ";

    let mut exhausted = easy_build(11, spec);
    exhausted.presolve();
    exhausted.satisfiable(&mut |_| Control::Continue);
    exhausted.unroll();

    let mut early = easy_build(11, spec);
    early.presolve();
    early.satisfiable(&mut |_| Control::Stop);
    early.unroll();

    for variable in 0..12u32 {
        let mut probe = early.clone();
        probe
            .add_unit(Var::new(variable).pos_lit())
            .expect("add unit");
        probe.presolve();
        assert!(
            probe.satisfiable(&mut just_satisfiable),
            "forcing {variable} true after an early-stopped solve should stay SAT"
        );

        let mut probe = exhausted.clone();
        probe
            .add_unit(Var::new(variable).pos_lit())
            .expect("add unit");
        probe.presolve();
        assert!(
            probe.satisfiable(&mut just_satisfiable),
            "forcing {variable} true after an exhaustive solve wrongly reports UNSAT"
        );
    }
}
