#![no_main]

use arbitrary::Unstructured;
use happier::SATState;
use libfuzzer_sys::fuzz_target;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::{Lit, Var};
use rustsat_minisat::core::Minisat;
fn minisat_sat_with(cnf: &rustsat::instances::Cnf, unit: Lit) -> bool {
    let mut solver = Minisat::default();
    solver.extend(cnf.iter());
    solver.add_unit(unit).expect("add unit");
    match solver.solve().expect("minisat failed") {
        SolverResult::Sat => true,
        SolverResult::Unsat => false,
        SolverResult::Interrupted => panic!("minisat interrupted"),
    }
}

fn choose_n<'a, T>(
    unstructured: &mut Unstructured,
    items: &'a [T],
    n: usize,
) -> arbitrary::Result<Vec<&'a T>> {
    if n > items.len() {
        return Err(arbitrary::Error::NotEnoughData);
    }
    let mut chosen = Vec::with_capacity(n);
    let mut indices = (0..items.len()).collect::<Vec<usize>>();
    for _ in 0..n {
        let idx = unstructured.int_in_range(0..=(indices.len() - 1))?;
        let chosen_idx = indices.remove(idx);
        chosen.push(&items[chosen_idx]);
    }

    Ok(chosen)
}

#[derive(Debug)]
struct Constraints {
    clauses: Vec<Vec<(u8, bool)>>,
}

#[derive(Debug)]
struct Problem {
    stages: Vec<Constraints>,
}

impl Problem {
    fn new(unstructured: &mut Unstructured) -> arbitrary::Result<Self> {
        let valid_variables = (0..12).collect::<Vec<u8>>();
        let stage_count = unstructured.int_in_range(1..=5)?;
        let mut stages: Vec<Constraints> = Vec::with_capacity(stage_count);
        for _ in 0..stage_count {
            let clause_count = unstructured.int_in_range(1..=32)?;
            let mut clauses = Vec::with_capacity(clause_count);
            'outer: for _ in 0..clause_count {
                let literal_count = unstructured.int_in_range(1..=valid_variables.len())?;
                let mut clause = Vec::with_capacity(literal_count);

                for &var in choose_n(unstructured, &valid_variables, literal_count)? {
                    let is_positive = unstructured.arbitrary::<bool>()?;
                    clause.push((var, is_positive));
                }

                if !clauses.contains(&clause) {
                    for stage in &stages {
                        if stage.clauses.contains(&clause) {
                            continue 'outer;
                        }
                    }

                    clauses.push(clause);
                }
            }
            if !clauses.is_empty() {
                stages.push(Constraints { clauses });
            }
        }
        Ok(Problem { stages })
    }

    fn build_happier_clauses(&self, stage: usize) -> impl Iterator<Item = Vec<happier::Literal>> {
        self.stages[0..=stage].iter().flat_map(|stage| {
            stage.clauses.iter().map(|clause_data| {
                clause_data
                    .iter()
                    .map(|&(var_idx, is_positive)| {
                        if is_positive {
                            happier::Variable::new(var_idx as u32).literal_pos()
                        } else {
                            happier::Variable::new(var_idx as u32).literal_neg()
                        }
                    })
                    .collect()
            })
        })
    }

    fn build_rustsat_cnf(&self, stage: usize) -> rustsat::instances::Cnf {
        let mut cnf = rustsat::instances::Cnf::new();
        for stage in &self.stages[0..=stage] {
            for clause_data in &stage.clauses {
                let mut clause = Vec::new();
                for &(var_idx, is_positive) in clause_data {
                    let literal = if is_positive {
                        Lit::new(var_idx as u32, false)
                    } else {
                        Lit::new(var_idx as u32, true)
                    };
                    clause.push(literal);
                }
                if !clause.is_empty() {
                    cnf.add_clause(clause.as_slice().into());
                }
            }
        }
        cnf.normalize()
    }
}

fuzz_target!(|data: &[u8]| {
    let mut unstructured = Unstructured::new(data);

    let problem = match Problem::new(&mut unstructured) {
        Ok(p) => p,
        Err(_) => return,
    };

    if problem.stages.is_empty() {
        return;
    }

    let mut happier_solver = SATState::new();


    for i in 0..problem.stages.len() {
        println!("Adding stage {}/{}", i, problem.stages.len() - 1);
        for clause in problem.build_happier_clauses(i) {
            let max_var = clause
                .iter()
                .map(|lit| lit.variable().index())
                .max()
                .unwrap_or(0);
            happier_solver.new_variable_at(max_var);

            println!("Adding clause: {:?}", clause);
            happier_solver.add_clause(clause);
        }
        println!("Happier state: {happier_solver:?}");

        let rustsat_cnf = problem.build_rustsat_cnf(i);


        let mut minisat_solver = Minisat::default();
        minisat_solver.extend(rustsat_cnf.iter());

        happier_solver.presolve();
        let mut presolved_state = happier_solver.clone();

        println!("pre-solve: {happier_solver:?}");
        let happier_result = happier_solver.satisfiable(&mut |_model| happier::Control::Continue);
        println!("post-solve: {happier_solver:?}");

        happier_solver.unroll();

        let max_var = happier_solver.max_known_variable().map_or(0, |v| v.index());
        for i in 0..max_var {
            let mut active = happier_solver.clone();
            let unit = Var::new(i as u32).pos_lit();
            active.add_unit(unit).expect("!");
            active.presolve();
            let got = active.satisfiable(&mut happier::just_satisfiable);
            let expected = minisat_sat_with(&rustsat_cnf, unit);
            assert_eq!(
                expected, got,
                "forcing variable {i} true after a completed solve: happier={got} minisat={expected}\nproblem: {problem:?}"
            );
        }

        let minisat_result = minisat_solver.solve();
        println!(
            "happier / minisat results: {:?} / {:?}",
            happier_result, minisat_result
        );

        if let (h_result, Ok(m_result)) = (happier_result, minisat_result) {
            match (h_result, m_result) {
                (true, SolverResult::Sat) => {
                }
                (false, SolverResult::Unsat) => {
                }
                (true, SolverResult::Unsat) | (false, SolverResult::Sat) => {
                    panic!(
                        "Solver disagreement! Happier: {:?}, MiniSat: {:?}",
                        h_result, m_result
                    );
                }
                _ => {
                }
            }
        }

        if let Some(var) = presolved_state.max_known_variable() {
            let possy = presolved_state.can_pos(0..var.index());
            println!("Can pos: {:?}", possy);
        }
    }
});
