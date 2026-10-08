mod common;

use common::{assignment_to_solutions, validate_solve};
use happier::{Control, SATState, Variable, just_satisfiable, tour_all_solutions};
use rustsat::solvers::Solve;

#[test]
fn empty() {
    let mut solver = SATState::new();
    validate_solve(&mut solver, true);
}

#[test]
fn unit_sat() {
    let mut solver = SATState::new();
    let var = solver.new_variable();
    solver.add_clause(vec![var.literal_pos()]);
    validate_solve(&mut solver, true);
}

#[test]
fn unit_sat_neg() {
    let mut solver = SATState::new();
    let var = solver.new_variable();
    solver.add_clause(vec![var.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn unit_posneg_sat() {
    let mut solver = SATState::new();
    let var = solver.new_variable();
    solver.add_clause(vec![var.literal_pos(), var.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn min_unsat() {
    let mut solver = SATState::new();
    let var = solver.new_variable();
    solver.add_clause(vec![var.literal_pos()]);
    solver.add_clause(vec![var.literal_neg()]);
    validate_solve(&mut solver, false);
}

#[test]
fn learned_clause_polarity_regression() {
    let mut solver = SATState::new();
    let v: Vec<_> = (0..12).map(|_| solver.new_variable()).collect();
    let pos = |i: usize| v[i].literal_pos();
    let neg = |i: usize| v[i].literal_neg();

    solver.add_clause(vec![pos(1)]);
    solver.add_clause(vec![neg(1), pos(7), neg(11)]);
    solver.add_clause(vec![neg(2), neg(5), neg(6)]);
    solver.add_clause(vec![neg(2), pos(6), pos(7)]);
    solver.add_clause(vec![pos(3), neg(5), neg(10)]);
    solver.add_clause(vec![neg(0), neg(7)]);
    solver.add_clause(vec![pos(0), neg(4), pos(7)]);
    solver.add_clause(vec![pos(0), pos(2)]);
    solver.add_clause(vec![pos(5), pos(11)]);
    solver.add_clause(vec![pos(0), neg(2), pos(9)]);
    solver.add_clause(vec![neg(5), pos(8), pos(10)]);
    solver.add_clause(vec![pos(0), neg(9)]);

    validate_solve(&mut solver, true);
}

#[test]
fn large_problem() {
    let mut solver = SATState::new();

    let variables = (0..32).map(|_| solver.new_variable()).collect::<Vec<_>>();

    for i in 0..32 {
        solver.add_clause(vec![
            variables[i].literal_pos(),
            variables[(i + 1) % 32].literal_neg(),
            variables[(i + 2) % 32].literal_neg(),
        ]);
    }

    let mut pos = 0;
    let mut index = 0;
    for _ in 0..230 {
        let mut clause = Vec::new();
        for _ in 0..5 {
            pos += 1;
            if 0 == pos % 3 {
                clause.push(variables[index].literal_neg());
            } else {
                clause.push(variables[index].literal_pos());
            }
            index = (index + 1) % variables.len();
        }
        solver.add_clause(clause);
    }

    println!("Solver: {solver:#?}");
    solver.presolve();
    solver.solve().expect("failed to solve");
}

#[test]
fn pigeonhole() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    solver.add_clause(vec![a.literal_pos()]);
    solver.add_clause(vec![b.literal_pos()]);
    solver.add_clause(vec![a.literal_neg(), b.literal_neg()]);
    validate_solve(&mut solver, false);
}

#[test]
fn triplet() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), b.literal_pos()]);
    solver.add_clause(vec![a.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![b.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![c.literal_neg()]);
    validate_solve(&mut solver, false);
}

#[test]
fn learning_1() {
    let mut solver = SATState::new();
    let _ = solver.new_variable();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), b.literal_pos(), c.literal_neg()]);
    solver.add_clause(vec![b.literal_pos(), d.literal_neg()]);
    println!("Solver: {solver:#?}");
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn backjump() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), b.literal_pos()]);
    solver.add_clause(vec![a.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![b.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![c.literal_neg(), d.literal_pos()]);
    solver.add_clause(vec![c.literal_neg(), d.literal_neg()]);
    solver.presolve();
    let presolved = solver.clone();
    assert!(!solver.satisfiable(&mut tour_all_solutions));
    solver.unroll();
    println!("Presolved: {presolved:#?}");
    println!("Solver: {solver:#?}");
}

#[test]
fn double_true() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let _b = solver.new_variable();
    let c = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), a.literal_pos()]);
    solver.add_clause(vec![c.literal_pos(), a.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn double_false() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    solver.add_clause(vec![b.literal_pos(), a.literal_pos(), a.literal_neg()]);
    solver.add_clause(vec![b.literal_neg(), b.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn learning_quad() {
    let mut solver = SATState::new();
    let v0 = solver.new_variable();
    let v1 = solver.new_variable();
    let v2 = solver.new_variable();
    let v5 = solver.new_variable();
    let v6 = solver.new_variable();
    solver.add_clause(vec![v2.literal_pos()]);
    solver.add_clause(vec![v0.literal_pos(), v5.literal_neg()]);
    solver.add_clause(vec![v0.literal_neg(), v6.literal_pos()]);
    solver.add_clause(vec![v0.literal_neg(), v6.literal_neg()]);
    solver.add_clause(vec![v0.literal_pos(), v1.literal_neg(), v5.literal_pos()]);
    let solutions = solver.all_solutions();
    println!("Final state: {solver:#?}");
    solver.unroll();
    for solution in &solutions {
        print!("Solution: ");
        for (i, &v) in solution.iter().enumerate() {
            print!("{}{} ", if v.unwrap_or(true) { " " } else { "~" }, i);
        }
        println!();
    }
    println!("solver: {solver:#?}");
    assert!(!solutions.is_empty());
}

#[test]
fn learning_triplet() {
    let mut solver = SATState::new();
    let _ = solver.new_variable();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![d.literal_neg(), b.literal_pos(), a.literal_neg()]);
    solver.add_clause(vec![c.literal_pos(), b.literal_pos(), a.literal_neg()]);
    solver.add_clause(vec![d.literal_pos(), c.literal_neg(), b.literal_pos()]);
    let solutions = solver.all_solutions();
    solver.unroll();
    for solution in &solutions {
        print!("Solution: ");
        for (i, &v) in solution.iter().enumerate() {
            print!("{}{} ", if v.unwrap_or(true) { " " } else { "~" }, i);
        }
        println!();
    }
    println!("solver: {solver:#?}");
    assert!(solver.satisfiable(&mut tour_all_solutions));
}

#[test]
fn fuzz_rehydrate() {
    let mut solver = SATState::new();
    let vars = (0..6).map(Variable::new).collect::<Vec<_>>();
    for i in 0..6 {
        solver.new_variable_at(i);
    }
    let clause = vec![
        vars[0].literal_neg(),
        vars[1].literal_neg(),
        vars[2].literal_neg(),
        vars[3].literal_neg(),
        vars[4].literal_neg(),
        vars[5].literal_neg(),
    ];
    solver.add_clause(clause);
    solver.presolve();
    let _ = solver.satisfiable(&mut just_satisfiable);
    solver.unroll();
}

#[test]
fn fuzz_learning() {
    let mut solver = SATState::new();
    let vars = (0..8).map(|_| solver.new_variable()).collect::<Vec<_>>();
    solver.add_clause(vec![vars[0].literal_pos(), vars[5].literal_neg()]);
    solver.add_clause(vec![vars[0].literal_pos(), vars[6].literal_pos()]);
    solver.add_clause(vec![vars[0].literal_pos(), vars[1].literal_neg()]);
    solver.add_clause(vec![vars[0].literal_neg(), vars[7].literal_pos()]);
    solver.add_clause(vec![vars[0].literal_neg(), vars[6].literal_neg()]);
    solver.add_clause(vec![
        vars[0].literal_neg(),
        vars[3].literal_pos(),
        vars[6].literal_pos(),
    ]);
    solver.add_clause(vec![
        vars[1].literal_pos(),
        vars[3].literal_pos(),
        vars[6].literal_neg(),
    ]);
    solver.add_clause(vec![
        vars[0].literal_pos(),
        vars[3].literal_neg(),
        vars[5].literal_pos(),
    ]);

    let solutions = solver.all_solutions();
    solver.unroll();

    for solution in &solutions {
        print!("Solution: ");
        for (i, &v) in solution.iter().enumerate() {
            print!("{}{} ", if v.unwrap_or(true) { " " } else { "~" }, i);
        }
        println!();
    }
}

#[test]
fn fuzz_simplest() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    solver.add_clause(vec![x0.literal_pos()]);
    validate_solve(&mut solver, true);
    let x1 = solver.new_variable();
    let x2 = solver.new_variable();
    solver.add_clause(vec![x0.literal_neg(), x1.literal_neg(), x2.literal_neg()]);
}

#[test]
fn all_solutions() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    solver.add_clause(vec![a.literal_pos()]);
    solver.add_clause(vec![a.literal_pos(), b.literal_pos()]);
    solver.add_clause(vec![a.literal_neg(), c.literal_pos()]);

    let mut solutions = Vec::new();
    assert!(solver.satisfiable(&mut |state| {
        assignment_to_solutions(state.assignments(), &mut solutions);
        Control::Continue
    }));
    solutions.sort_unstable();
    assert_eq!(
        solutions,
        vec![vec![true, false, true], vec![true, true, true],]
    );
}

#[test]
fn empty_solutions() {
    let mut solver = SATState::new();
    let _ = solver.new_variable();
    let mut solutions = Vec::new();
    assert!(solver.satisfiable(&mut |state| {
        println!("State: {state:#?}");
        assignment_to_solutions(state.assignments(), &mut solutions);
        Control::Continue
    }));
    solutions.sort_unstable();
    assert_eq!(
        vec![vec![false], vec![true],],
        solutions,
        "[expected] [actual] solutions mismatched"
    );
}

#[test]
fn fuzz_contradiction_case() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    let x2 = solver.new_variable();
    let x3 = solver.new_variable();

    // Clauses: (!x0|x1), (!x1|!x2), (x1), (!x1|x2), (x0|!x3)
    solver.add_clause(vec![x0.literal_neg(), x1.literal_pos()]);
    solver.add_clause(vec![x1.literal_neg(), x2.literal_neg()]);
    solver.add_clause(vec![x1.literal_pos()]);
    solver.add_clause(vec![x1.literal_neg(), x2.literal_pos()]);
    solver.add_clause(vec![x0.literal_pos(), x3.literal_neg()]);

    // This should be unsatisfiable due to contradiction on x2
    validate_solve(&mut solver, false);
}

#[test]
fn simple_forced_contradiction() {
    let mut solver = SATState::new();
    let x0 = solver.new_variable();
    let x1 = solver.new_variable();
    solver.add_clause(vec![x0.literal_pos()]);
    solver.add_clause(vec![x0.literal_neg(), x1.literal_pos()]);
    solver.add_clause(vec![x0.literal_neg(), x1.literal_neg()]);
    validate_solve(&mut solver, false);
}

#[test]
fn fuzzer_exact_case() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![a.literal_neg(), b.literal_pos()]);
    solver.add_clause(vec![b.literal_neg(), c.literal_neg()]);
    solver.add_clause(vec![b.literal_pos()]);
    solver.add_clause(vec![b.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![a.literal_pos(), d.literal_neg()]);
    validate_solve(&mut solver, false);
}

#[test]
fn fuzzer_actual_case() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![a.literal_neg(), b.literal_pos()]);
    solver.add_clause(vec![d.literal_neg(), c.literal_neg()]);
    solver.add_clause(vec![d.literal_pos(), a.literal_neg(), d.literal_pos()]);
    solver.add_clause(vec![d.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![a.literal_pos(), b.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn fuzzer_actual_case_rev() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();
    solver.add_clause(vec![a.literal_neg(), b.literal_pos()]);
    solver.add_clause(vec![d.literal_neg(), c.literal_pos()]);
    solver.add_clause(vec![d.literal_pos(), a.literal_neg(), d.literal_pos()]);
    solver.add_clause(vec![d.literal_neg(), c.literal_neg()]);
    solver.add_clause(vec![a.literal_pos(), b.literal_neg()]);
    validate_solve(&mut solver, true);
}

#[test]
fn incremental_add_after_sat_solve() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), b.literal_pos()]);

    assert!(solver.satisfiable(&mut just_satisfiable), "a | b is sat");

    solver.add_clause(vec![a.literal_neg()]);
    assert!(
        solver.satisfiable(&mut just_satisfiable),
        "(a | b) & ~a is still sat: ~a b"
    );

    solver.add_clause(vec![b.literal_neg()]);
    assert!(
        !solver.satisfiable(&mut just_satisfiable),
        "(a | b) & ~a & ~b is unsat"
    );
}

#[test]
fn incremental_add_after_unsat_solve() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    let c = solver.new_variable();
    let d = solver.new_variable();

    for bits in 0..8u8 {
        solver.add_clause(vec![
            if bits & 1 == 0 {
                a.literal_neg()
            } else {
                a.literal_pos()
            },
            if bits & 2 == 0 {
                b.literal_neg()
            } else {
                b.literal_pos()
            },
            if bits & 4 == 0 {
                c.literal_neg()
            } else {
                c.literal_pos()
            },
        ]);
    }

    assert!(
        !solver.satisfiable(&mut just_satisfiable),
        "all eight assignments of a, b, c are excluded"
    );

    solver.add_clause(vec![d.literal_pos()]);
    assert!(
        !solver.satisfiable(&mut just_satisfiable),
        "adding d to an unsat formula leaves it unsat"
    );
}

#[test]
fn incremental_resolve_without_adding() {
    let mut solver = SATState::new();
    let a = solver.new_variable();
    let b = solver.new_variable();
    solver.add_clause(vec![a.literal_pos(), b.literal_pos()]);

    assert!(solver.satisfiable(&mut just_satisfiable));
    assert!(solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn incremental_add_after_solve_via_rustsat() {
    use rustsat::instances::Cnf;
    use rustsat::solvers::SolverResult;
    use rustsat::types::Lit;

    let mut solver = SATState::new();
    let a = Lit::new(0, false);
    let b = Lit::new(1, false);

    let mut cnf = Cnf::new();
    cnf.add_clause(rustsat::clause![a, b]);
    solver.extend(cnf.iter().cloned());

    assert_eq!(SolverResult::Sat, solver.solve().unwrap());

    let mut more = Cnf::new();
    more.add_clause(rustsat::clause![!a]);
    solver.extend(more.iter().cloned());

    assert_eq!(
        SolverResult::Sat,
        solver.solve().unwrap(),
        "(a | b) & ~a is still sat"
    );
}
