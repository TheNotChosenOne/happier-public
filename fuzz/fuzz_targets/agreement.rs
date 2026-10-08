#![no_main]

use arbitrary::Unstructured;
use happier::SATState;
use libfuzzer_sys::fuzz_target;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::{Lit, TernaryVal, Var};
use rustsat_minisat::core::Minisat;
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

fn expand_solutions(solutions: &[Vec<Option<bool>>], width: usize) -> Vec<Vec<bool>> {
    let mut expanded = Vec::new();
    for solution in solutions {
        let free: Vec<usize> = (0..width)
            .filter(|&i| solution.get(i).copied().flatten().is_none())
            .collect();
        assert!(free.len() < 24, "too many free variables to expand");
        for mask in 0u32..(1u32 << free.len()) {
            let mut concrete: Vec<bool> = (0..width)
                .map(|i| solution.get(i).copied().flatten().unwrap_or(false))
                .collect();
            for (bit, &position) in free.iter().enumerate() {
                concrete[position] = (mask >> bit) & 1 == 1;
            }
            expanded.push(concrete);
        }
    }
    expanded.sort_unstable();
    expanded
}

fn assignment_to_vec(assignment: rustsat::types::Assignment) -> Vec<Option<bool>> {
    let mut result = Vec::with_capacity(assignment.len());
    for i in 0..assignment.len() {
        let assigned = assignment.var_value(Var::new(i as u32));
        result.push(match assigned {
            TernaryVal::True => Some(true),
            TernaryVal::False => Some(false),
            _ => None,
        });
    }
    result
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
    println!("Happier state: {happier_solver:?}");
    println!("Problem: {problem:?}");

    for i in 0..problem.stages.len() {
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

        let rustsat_cnf = problem.build_rustsat_cnf(i);
        let var_count = rustsat_cnf
            .iter()
            .flat_map(|clause| clause.iter().map(|lit| lit.var()))
            .max()
            .unwrap_or(Var::new(0));

        println!("Input CNF: {:?}", rustsat_cnf);
        println!("Happier state: {happier_solver:?}");

        let mut minisat_solver = Minisat::default();
        minisat_solver.extend(rustsat_cnf.iter());

        happier_solver.presolve();

        let mut happier_solutions: Vec<Vec<Option<bool>>> = Vec::new();
        let happier_result = happier_solver.satisfiable(&mut |model| {
            let solution = model.solution(var_count).expect("failed to get solution");

            let solution = assignment_to_vec(solution);
            assert!(
                !happier_solutions.contains(&solution),
                "happier found duplicate solution"
            );
            assert!(
                happier_solutions.len() < 100_000,
                "too many solutions found by happier"
            );

            happier_solutions.push(solution);
            happier::Control::Continue
        });

        happier_solver.unroll();

        let mut minisat_solutions = Vec::new();
        let mut blockers: Vec<Vec<Lit>> = Vec::new();
        loop {
            let mut active = Minisat::default();
            let mut active_cnf = rustsat_cnf.clone();
            for clause in &blockers {
                active_cnf.add_clause(clause.as_slice().into());
            }
            active.extend(active_cnf);
            match active.solve().expect("solver failed") {
                SolverResult::Sat => {
                    let solution = active.solution(var_count).expect("failed to get solution");
                    let blocking_clause: Vec<Lit> = solution.iter().map(|lit| !lit).collect();
                    blockers.push(blocking_clause);
                    minisat_solutions.push(assignment_to_vec(solution));
                }
                SolverResult::Unsat => break,
                SolverResult::Interrupted => panic!("minisat was interrupted"),
            }
        }

        let minisat_result = minisat_solver.solve();
        println!(
            "happier / minisat results: {:?} / {:?}",
            happier_result, minisat_result
        );
        println!(
            "solutions: {} / {}",
            happier_solutions.len(),
            minisat_solutions.len()
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

        happier_solutions.sort_unstable();
        minisat_solutions.sort_unstable();

        println!("MiniSat solutions ({}):", minisat_solutions.len());
        dump_solutions(&minisat_solutions);
        println!("Happier solutions ({}):", happier_solutions.len());
        dump_solutions(&happier_solutions);
        println!("Happier state: {happier_solver:?}");

        let width = happier_solutions
            .iter()
            .chain(minisat_solutions.iter())
            .map(Vec::len)
            .max()
            .unwrap_or(0);
        let happier_models = expand_solutions(&happier_solutions, width);
        let minisat_models = expand_solutions(&minisat_solutions, width);

        assert_eq!(
            minisat_models.len(),
            happier_models.len(),
            "model counts differ: minisat {} vs happier {}",
            minisat_models.len(),
            happier_models.len()
        );
        assert_eq!(minisat_models, happier_models, "Solution sets differ");
    }
});

fn dump_solutions(solutions: &[Vec<Option<bool>>]) {
    for sol in solutions {
        let sol_str: String = sol
            .iter()
            .map(|v| match v {
                Some(true) => '1',
                Some(false) => '0',
                None => 'X',
            })
            .collect();
        println!("  {}", sol_str);
    }
}
