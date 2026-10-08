#![no_main]

use happier::SATState;
use libfuzzer_sys::fuzz_target;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::Lit;
use rustsat_minisat::core::Minisat;

#[derive(Debug)]
struct Problem {
    clauses: Vec<Vec<(u8, bool)>>,
}

impl Problem {
    fn new(unstructured: &[u8]) -> arbitrary::Result<Self> {
        let mut clauses = Vec::new();
        let mut active_clause = Vec::new();

        for byte in unstructured {
            if *byte == 0 {
                if !active_clause.is_empty() && !clauses.contains(&active_clause) {
                    clauses.push(active_clause);
                    active_clause = Vec::new();
                }
            } else {
                let byte = byte - 1;
                let negated = (byte & 0b1000) != 0;
                let number = byte & 0b111;
                active_clause.push((number, !negated));
            }
        }
        if !active_clause.is_empty() && !clauses.contains(&active_clause) {
            clauses.push(active_clause);
        }
        Ok(Problem { clauses })
    }

    fn build_happier_clauses(&self) -> impl Iterator<Item = Vec<happier::Literal>> {
        self.clauses.iter().map(|clause_data| {
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
    }

    fn build_rustsat_cnf(&self) -> rustsat::instances::Cnf {
        let mut cnf = rustsat::instances::Cnf::new();
        for clause_data in &self.clauses {
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
        cnf.normalize()
    }
}

fuzz_target!(|data: &[u8]| {
    let problem = match Problem::new(data) {
        Ok(p) => p,
        Err(_) => return,
    };

    if problem.clauses.is_empty() {
        return;
    }

    let mut happier_solver = SATState::new();
    for clause in problem.build_happier_clauses() {
        let max_var = clause
            .iter()
            .map(|lit| lit.variable().index())
            .max()
            .unwrap_or(0);
        happier_solver.new_variable_at(max_var);
        println!("Clause: {:?}", clause);
        happier_solver.add_clause(clause);
    }

    let rustsat_cnf = problem.build_rustsat_cnf();
    let mut minisat_solver = Minisat::default();
    minisat_solver.extend(rustsat_cnf.iter());
    let minisat_result = minisat_solver.solve();

    let happier_result = happier_solver.satisfiable(&mut |_model| happier::Control::Continue);
    if let (h_result, Ok(m_result)) = (happier_result, minisat_result) {
        match (h_result, m_result) {
            (true, SolverResult::Sat) => {
            }
            (false, SolverResult::Unsat) => {
            }
            (true, SolverResult::Unsat) | (false, SolverResult::Sat) => {
                println!("Solver: {happier_solver:?}");
                panic!("Solver disagreement! Happier: {h_result:?}, MiniSat: {m_result:?}",);
            }
            _ => {
            }
        }
    }
});
