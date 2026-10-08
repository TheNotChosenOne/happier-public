mod common;

use common::loud_solution_count;
use happier::{SATState, Variable, just_satisfiable};

const VARS: usize = 9;

type Spec = Vec<Vec<(usize, bool)>>;

struct Lcg(u64);

impl Lcg {
    fn next(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % bound
    }
}

fn gen_instance(seed: u64) -> Spec {
    let mut rng = Lcg(seed);
    let clause_count = 4 + rng.next(24);
    let mut clauses = Vec::with_capacity(clause_count);
    for _ in 0..clause_count {
        let len = 1 + rng.next(4);
        let mut clause: Vec<(usize, bool)> = Vec::with_capacity(len);
        for _ in 0..len {
            let var = rng.next(VARS);
            if clause.iter().any(|&(v, _)| v == var) {
                continue;
            }
            clause.push((var, rng.next(2) == 1));
        }
        clauses.push(clause);
    }
    clauses
}

fn build(spec: &Spec) -> SATState {
    let mut solver = SATState::new();
    solver.new_variable_at(VARS - 1);
    for clause in spec {
        let lits: Vec<happier::Literal> = clause
            .iter()
            .map(|&(var, pos)| Variable::new(var as u32).literal(pos))
            .collect();
        solver.add_clause(lits);
    }
    solver
}

fn satisfies(spec: &Spec, model: usize) -> bool {
    spec.iter().all(|clause| {
        clause
            .iter()
            .any(|&(var, pos)| ((model >> var) & 1 == 1) == pos)
    })
}

fn oracle(spec: &Spec) -> (usize, Vec<bool>) {
    let mut count = 0;
    let mut can = vec![false; VARS];
    for model in 0..1usize << VARS {
        if satisfies(spec, model) {
            count += 1;
            for (var, slot) in can.iter_mut().enumerate() {
                *slot |= (model >> var) & 1 == 1;
            }
        }
    }
    (count, can)
}

#[test]
fn model_counts_and_can_pos_match_brute_force() {
    for seed in 0..60 {
        let spec = gen_instance(seed);
        let (expected_count, expected_can) = oracle(&spec);

        let mut counter = build(&spec);
        let cubes = counter.all_solutions();
        let count = loud_solution_count(&cubes);
        assert_eq!(
            expected_count, count,
            "model count diverged on seed {seed}: {spec:?}"
        );

        let mut poser = build(&spec);
        let can = poser.can_pos(0..VARS);
        assert_eq!(
            expected_can, can,
            "can_pos diverged on seed {seed}: {spec:?}"
        );

        let mut decider = build(&spec);
        assert_eq!(
            expected_count > 0,
            decider.satisfiable(&mut just_satisfiable),
            "satisfiable diverged on seed {seed}: {spec:?}"
        );
    }
}

#[test]
fn phase_transition_matches_brute_force() {
    for seed in 200..240 {
        let mut rng = Lcg(seed);
        let mut spec: Spec = Vec::new();
        while spec.len() < 43 {
            let mut clause: Vec<(usize, bool)> = Vec::new();
            while clause.len() < 3 {
                let var = rng.next(10);
                if clause.iter().any(|&(v, _)| v == var) {
                    continue;
                }
                clause.push((var, rng.next(2) == 1));
            }
            spec.push(clause);
        }

        let mut count = 0;
        let mut can = vec![false; 10];
        for model in 0..1usize << 10 {
            if satisfies(&spec, model) {
                count += 1;
                for (var, slot) in can.iter_mut().enumerate() {
                    *slot |= (model >> var) & 1 == 1;
                }
            }
        }

        let mut solver = SATState::new();
        solver.new_variable_at(9);
        for clause in &spec {
            let lits: Vec<happier::Literal> = clause
                .iter()
                .map(|&(var, pos)| Variable::new(var as u32).literal(pos))
                .collect();
            solver.add_clause(lits);
        }
        assert_eq!(
            count > 0,
            solver.clone().satisfiable(&mut just_satisfiable),
            "satisfiable diverged on seed {seed}: {spec:?}"
        );
        assert_eq!(
            can,
            solver.can_pos(0..10),
            "can_pos diverged on seed {seed}: {spec:?}"
        );
    }
}

#[test]
fn incremental_stages_match_brute_force() {
    for seed in 100..130 {
        let spec = gen_instance(seed);
        let mut solver = SATState::new();
        solver.new_variable_at(VARS - 1);
        let mut so_far: Spec = Vec::new();
        for clause in &spec {
            let lits: Vec<happier::Literal> = clause
                .iter()
                .map(|&(var, pos)| Variable::new(var as u32).literal(pos))
                .collect();
            solver.add_clause(lits);
            so_far.push(clause.clone());

            let (expected_count, expected_can) = oracle(&so_far);
            assert_eq!(
                expected_count > 0,
                solver.satisfiable(&mut just_satisfiable),
                "incremental satisfiable diverged on seed {seed} after {} clauses: {so_far:?}",
                so_far.len()
            );
            assert_eq!(
                expected_can,
                solver.can_pos(0..VARS),
                "incremental can_pos diverged on seed {seed} after {} clauses: {so_far:?}",
                so_far.len()
            );
        }
    }
}
