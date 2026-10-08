use happier::{SATState, Variable, just_satisfiable, tour_all_solutions};

const VARS: usize = 11;

const SATISFIABLE_CORE: &[&[(usize, bool)]] = &[
    &[(10, false), (5, false), (2, true)],
    &[(10, false), (6, true)],
    &[(10, true)],
    &[(5, true)],
];

const REFUTING_CLAUSE: &[(usize, bool)] = &[(2, false), (6, false), (10, false)];

fn build(clauses: &[&[(usize, bool)]]) -> SATState {
    let mut solver = SATState::new();
    solver.new_variable_at(VARS - 1);
    for clause in clauses {
        add(&mut solver, clause);
    }
    solver
}

fn add(solver: &mut SATState, clause: &[(usize, bool)]) {
    solver.add_clause(
        clause
            .iter()
            .map(|&(v, pos)| Variable::new(v as u32).literal(pos))
            .collect::<Vec<_>>(),
    );
}

fn oracle(clauses: &[&[(usize, bool)]]) -> (bool, Vec<bool>) {
    let mut any = false;
    let mut can = vec![false; VARS];
    for model in 0..1usize << VARS {
        let ok = clauses
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

#[test]
fn can_pos_after_unrolling_a_refuted_solve() {
    let mut with_refutation: Vec<&[(usize, bool)]> = SATISFIABLE_CORE.to_vec();
    with_refutation.push(REFUTING_CLAUSE);
    let (sat, expected) = oracle(&with_refutation);
    assert!(!sat, "core plus the refuting clause must be UNSAT");
    assert_eq!(vec![false; VARS], expected);

    let mut solver = build(SATISFIABLE_CORE);
    assert!(solver.satisfiable(&mut tour_all_solutions));
    solver.unroll();

    add(&mut solver, REFUTING_CLAUSE);
    assert!(!solver.satisfiable(&mut just_satisfiable));
    solver.unroll();

    assert_eq!(expected, solver.can_pos(0..VARS));
}

#[test]
fn satisfiable_after_unrolling_a_refuted_solve() {
    let mut solver = build(SATISFIABLE_CORE);
    assert!(solver.satisfiable(&mut tour_all_solutions));
    solver.unroll();

    add(&mut solver, REFUTING_CLAUSE);
    assert!(!solver.satisfiable(&mut just_satisfiable));
    solver.unroll();

    assert!(!solver.satisfiable(&mut just_satisfiable));
}

#[test]
fn can_pos_after_unrolling_an_exhaustive_tour() {
    let (sat, expected) = oracle(SATISFIABLE_CORE);
    assert!(sat, "core alone must be SAT");

    let mut solver = build(SATISFIABLE_CORE);
    solver.satisfiable(&mut tour_all_solutions);
    solver.unroll();

    assert_eq!(expected, solver.can_pos(0..VARS));
    assert_eq!(expected, build(SATISFIABLE_CORE).can_pos(0..VARS));
}
