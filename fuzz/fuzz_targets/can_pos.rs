#![no_main]


use arbitrary::Unstructured;
use happier::SATState;
use libfuzzer_sys::fuzz_target;
use rustsat::solvers::{Solve, SolverResult};
use rustsat::types::Lit;
use rustsat_minisat::core::Minisat;

#[derive(Debug)]
struct Stage {
    clauses: Vec<Vec<(u8, bool)>>,
    solve_first: bool,
    exhaustive: bool,
    query_clone: bool,
    requery: bool,
    presolve: bool,
    range: (u8, u8),
}

#[derive(Debug)]
struct Problem {
    stages: Vec<Stage>,
}

const MAX_VAR: u8 = 10;

impl Problem {
    fn new(u: &mut Unstructured) -> arbitrary::Result<Self> {
        let stage_count = u.int_in_range(1..=4)?;
        let mut stages = Vec::with_capacity(stage_count);
        for _ in 0..stage_count {
            let clause_count = u.int_in_range(0..=24)?;
            let mut clauses = Vec::with_capacity(clause_count);
            for _ in 0..clause_count {
                let literal_count = u.int_in_range(1..=4)?;
                let mut vars: Vec<u8> = Vec::with_capacity(literal_count);
                let mut clause = Vec::with_capacity(literal_count);
                for _ in 0..literal_count {
                    let var = u.int_in_range(0..=MAX_VAR)?;
                    if vars.contains(&var) {
                        continue;
                    }
                    vars.push(var);
                    clause.push((var, u.arbitrary::<bool>()?));
                }
                if !clauses.contains(&clause) {
                    clauses.push(clause);
                }
            }
            let range = if u.arbitrary::<bool>()? {
                (0, MAX_VAR + 1)
            } else {
                let start = u.int_in_range(0..=MAX_VAR)?;
                let end = u.int_in_range(start..=(MAX_VAR + 1))?;
                (start, end)
            };
            stages.push(Stage {
                clauses,
                solve_first: u.arbitrary()?,
                exhaustive: u.arbitrary()?,
                query_clone: u.arbitrary()?,
                requery: u.arbitrary()?,
                presolve: u.arbitrary()?,
                range,
            });
        }
        Ok(Problem { stages })
    }
}

fn minisat_sat_with(cnf: &rustsat::instances::Cnf, unit: Option<Lit>) -> bool {
    let mut solver = Minisat::default();
    solver.extend(cnf.iter());
    if let Some(lit) = unit {
        solver.add_unit(lit).expect("add unit");
    }
    match solver.solve().expect("minisat failed") {
        SolverResult::Sat => true,
        SolverResult::Unsat => false,
        SolverResult::Interrupted => panic!("minisat interrupted"),
    }
}

fn check_can_pos(
    solver: &mut SATState,
    cnf: &rustsat::instances::Cnf,
    stage: &Stage,
    problem: &Problem,
) {
    let (start, end) = stage.range;
    let (start, end) = (start as usize, end as usize);
    let end = end.min(solver.variable_count());
    let start = start.min(end);

    let output = solver.can_pos(start..end);
    assert_eq!(end - start, output.len(), "can_pos output length");

    for (i, &can) in output.iter().enumerate() {
        let var = (start + i) as u32;
        let expected = minisat_sat_with(cnf, Some(Lit::new(var, false)));
        assert_eq!(
            expected, can,
            "can_pos({start}..{end}) bit {i} (var {var}): happier={can} minisat={expected}\nstage: {stage:?}\nproblem: {problem:?}\nsolver: {solver:?}"
        );
    }

    if stage.requery {
        let again = solver.can_pos(start..end);
        assert_eq!(
            output, again,
            "repeated can_pos({start}..{end}) changed its answer\nstage: {stage:?}\nproblem: {problem:?}\nsolver: {solver:?}"
        );
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);
    let problem = match Problem::new(&mut u) {
        Ok(p) => p,
        Err(_) => return,
    };

    let mut solver = SATState::new();
    solver.new_variable_at(MAX_VAR as usize);
    let mut cnf = rustsat::instances::Cnf::new();

    for stage in &problem.stages {
        for clause in &stage.clauses {
            let lits: Vec<Lit> = clause
                .iter()
                .map(|&(var, pos)| Lit::new(var as u32, !pos))
                .collect();
            let rs_clause: rustsat::types::Clause = lits.as_slice().into();
            solver.add_clause_ref(&rs_clause).expect("add clause");
            cnf.add_clause(rs_clause);
        }

        if stage.presolve {
            solver.presolve();
        }

        if stage.solve_first {
            let expected = minisat_sat_with(&cnf, None);
            let got = if stage.exhaustive {
                solver.satisfiable(&mut happier::tour_all_solutions)
            } else {
                solver.satisfiable(&mut happier::just_satisfiable)
            };
            assert_eq!(
                expected, got,
                "satisfiable disagreement before can_pos\nstage: {stage:?}\nproblem: {problem:?}\nsolver: {solver:?}"
            );
            solver.unroll();
        }

        if stage.query_clone {
            let mut clone = solver.clone();
            check_can_pos(&mut clone, &cnf, stage, &problem);
        } else {
            check_can_pos(&mut solver, &cnf, stage, &problem);
        }
    }
});
