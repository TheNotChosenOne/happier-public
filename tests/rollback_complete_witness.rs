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

const WITNESS: &str = "~0 ~2 / ~6 9 / 3 8 ~9 / ~1 8 / 3 ~7 2 / 1 6 7 / ~7 1 4 / ~4 \
     / ~1 10 / ~8 7 / ~8 4 9 / ~9 ~3 / ~1 ~10 0";

const VARS: usize = 11;

#[test]
fn witness_is_unsat_and_satisfiable_agrees() {
    let spec = parse(WITNESS);
    let (sat, can) = oracle(&spec, VARS);
    assert!(!sat, "witness must be UNSAT");
    assert_eq!(vec![false; VARS], can);
    assert!(!build(&spec, VARS).satisfiable(&mut just_satisfiable));
}

#[test]
fn witness_can_pos_matches_oracle() {
    let spec = parse(WITNESS);
    let (_, expected) = oracle(&spec, VARS);
    assert_eq!(expected, build(&spec, VARS).can_pos(0..VARS));
}
