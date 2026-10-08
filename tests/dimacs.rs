mod common;

use common::validate_solve;
use happier::{SATState, just_satisfiable};
use rustsat::instances::BasicVarManager;
use rustsat::instances::SatInstance;
use rustsat::solvers::Solve;
use rustsat::types::Var;

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("test_cases/regression")
        .join(name)
}

#[test]
fn canpos_dimacs() {
    let sat_instance: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(fixture("canpos.cnf")).expect("failed to load DIMACS file");
    let cnf = sat_instance.cnf();
    let mut happier = SATState::new();
    happier.extend(cnf.iter());
    validate_solve(&mut happier, true);
}

#[test]
fn canpos2_dimacs() {
    let sat_instance: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(fixture("canpos2.cnf")).expect("failed to load DIMACS file");
    let cnf = sat_instance.cnf();
    let mut happier = SATState::new();
    happier.extend(cnf.iter());
    validate_solve(&mut happier, true);
    let can_pos = happier.can_pos(0..8);
    assert_eq!(
        can_pos,
        vec![false, false, false, true, true, false, false, false]
    );
}

#[test]
fn canpos3_dimacs() {
    let sat_instance: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(fixture("canpos3.cnf")).expect("failed to load DIMACS file");
    let cnf = sat_instance.cnf();
    let mut happier = SATState::new();
    happier.extend(cnf.iter());
    let can_pos = happier.can_pos(0..happier.variable_count());
    assert_eq!(
        can_pos,
        vec![
            false, false, true, true, true, true, false, false, false, true, true, true, true,
            false, true, true, true, true, true, true, true, true, true, true, true, true, true,
            true, true, true, true, true, true, true, true, true, true, true, true, true, true,
            true
        ]
    );
}

#[test]
fn unrolling_dimacs() {
    let sat_instance: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(fixture("unroll.cnf")).expect("failed to load DIMACS file");
    let cnf = sat_instance.cnf();
    let mut happier = SATState::new();
    happier.extend(cnf.iter());
    println!("Solver: {happier:#?}");
    validate_solve(&mut happier, true);

    for i in 0..16 {
        let mut active = happier.clone();
        let literal = Var::new(i as u32).pos_lit();
        println!("ADD CONSTRAINT: {literal}");
        active.add_unit(literal).expect("!");
        active.presolve();
        active.satisfiable(&mut just_satisfiable);
    }
}

#[test]
fn applied_dimacs() {
    let sat_instance: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(fixture("final_facts.cnf"))
            .expect("failed to load DIMACS file");
    let cnf = sat_instance.cnf();

    #[cfg(debug_assertions)]
    let rounds = 1;
    #[cfg(not(debug_assertions))]
    let rounds = 100_000;

    #[cfg(debug_assertions)]
    let warmups = 1;
    #[cfg(not(debug_assertions))]
    let warmups = 2000;

    let mut total_elapsed_mini = std::time::Duration::ZERO;
    for _ in 0..10 {
        let mut minisat = rustsat_minisat::simp::Minisat::default();
        minisat.extend(cnf.iter());
        let before = std::time::Instant::now();
        minisat.solve().expect("failed to solve with Minisat");
        let elapsed = before.elapsed();
        total_elapsed_mini += elapsed;
    }
    println!("Minisat took {:6}ns", total_elapsed_mini.as_nanos() / 10);

    let mut total_elapsed_happier = std::time::Duration::ZERO;
    let mut happier = SATState::new();
    happier.extend(cnf.iter());

    for _ in 0..warmups {
        let mut alt = happier.clone();
        alt.satisfiable(&mut just_satisfiable);
    }

    for _ in 0..rounds {
        let mut alt = happier.clone();
        let before = std::time::Instant::now();
        alt.satisfiable(&mut just_satisfiable);
        let elapsed = before.elapsed();
        total_elapsed_happier += elapsed;
    }

    println!("total duration: {:?}", total_elapsed_happier);

    let result = happier.satisfiable(&mut just_satisfiable);
    println!(
        "Happier took {:6}ns",
        total_elapsed_happier.as_nanos() / rounds
    );
    assert!(
        !result,
        "Happier should have found the same result as Minisat"
    );
}
