use happier::{SATState, Variable, just_satisfiable};

type Spec = Vec<Vec<(usize, bool)>>;

fn parse(s: &str) -> Spec {
    s.split('/')
        .filter_map(|clause| {
            let lits: Vec<(usize, bool)> = clause
                .split_whitespace()
                .map(|t| {
                    if let Some(rest) = t.strip_prefix('~') {
                        (rest.parse::<usize>().unwrap(), false)
                    } else {
                        (t.parse::<usize>().unwrap(), true)
                    }
                })
                .collect();
            (!lits.is_empty()).then_some(lits)
        })
        .collect()
}

fn build(spec: &Spec, vars: usize) -> SATState {
    let mut solver = SATState::new();
    solver.new_variable_at(vars - 1);
    for clause in spec {
        solver.add_clause(
            clause
                .iter()
                .map(|&(v, pos)| Variable::new(v as u32).literal(pos))
                .collect::<Vec<_>>(),
        );
    }
    solver
}

fn oracle(spec: &Spec, vars: usize) -> (bool, Vec<bool>) {
    let mut any = false;
    let mut can = vec![false; vars];
    for model in 0..1usize << vars {
        let ok = spec
            .iter()
            .all(|c| c.iter().any(|&(v, pos)| ((model >> v) & 1 == 1) == pos));
        if ok {
            any = true;
            for (v, slot) in can.iter_mut().enumerate() {
                *slot |= (model >> v) & 1 == 1;
            }
        }
    }
    (any, can)
}

const WITNESS_A: &str = "~3 ~1 ~2 / 3 ~1 ~2 / ~3 1 ~2 / 3 1 ~2 / ~3 ~1 2 / 3 ~1 2 / ~3 1 2 \
     / 3 1 2 / ~1 ~0 ~3 / ~0 ~3 ~2 / 8 6 4 / 7 5 8 / 4 9 8 / 5 6 9";

const WITNESS_B: &str = "~1 ~2 ~3 / 1 ~2 ~3 / ~1 2 ~3 / 1 2 ~3 / ~1 ~2 3 / 1 ~2 3 / ~1 2 3 \
     / 1 2 3 / ~0 2 3 / 5 8 9 / 5 9 7 / 7 4 9 / 6 9 4";

#[test]
fn witness_a_is_unsat_and_satisfiable_agrees() {
    let spec = parse(WITNESS_A);
    let (sat, can) = oracle(&spec, 10);
    assert!(!sat, "witness A must be UNSAT");
    assert_eq!(vec![false; 10], can);
    assert!(!build(&spec, 10).satisfiable(&mut just_satisfiable));
}

#[test]
fn witness_b_is_unsat_and_satisfiable_agrees() {
    let spec = parse(WITNESS_B);
    let (sat, can) = oracle(&spec, 10);
    assert!(!sat, "witness B must be UNSAT");
    assert_eq!(vec![false; 10], can);
    assert!(!build(&spec, 10).satisfiable(&mut just_satisfiable));
}

#[test]
fn witness_a_can_pos_matches_oracle() {
    let spec = parse(WITNESS_A);
    let (_, expected) = oracle(&spec, 10);
    assert_eq!(expected, build(&spec, 10).can_pos(0..10));
}

#[test]
fn witness_b_can_pos_matches_oracle() {
    let spec = parse(WITNESS_B);
    let (_, expected) = oracle(&spec, 10);
    assert_eq!(expected, build(&spec, 10).can_pos(0..10));
}
