mod common;

use common::{assignment_to_solutions, easy_build};
use happier::Control;
use happier::dedup::{Cube, DisjointCubes};
use std::collections::HashSet;

fn weight(cubes: &[Cube]) -> usize {
    cubes
        .iter()
        .map(|c| 1usize << c.iter().filter(|v| v.is_none()).count())
        .sum()
}

#[test]
fn dedup_restores_the_partition_on_the_duplicating_tour() {
    let spec = "
        ~0 ~1 ~6 ~2 ~5
         5  3
         3 ~5 ~4
         3  4
    ";

    let mut solver = easy_build(6, spec);
    let mut reported: Vec<Cube> = Vec::new();
    solver.satisfiable(&mut |state| {
        reported.push(state.assignments().to_vec());
        Control::Continue
    });
    assert!(
        weight(&reported) > 62,
        "the raw tour no longer duplicates; this proving ground is obsolete"
    );

    let mut dedup = DisjointCubes::new();
    let served: Vec<Cube> = reported.iter().flat_map(|c| dedup.admit(c)).collect();

    assert_eq!(
        62,
        weight(&served),
        "62 of the 128 assignments satisfy this"
    );

    let mut concrete = Vec::new();
    for cube in &served {
        assignment_to_solutions(cube, &mut concrete);
    }
    let concrete_set: HashSet<&Vec<bool>> = concrete.iter().collect();
    assert_eq!(concrete.len(), concrete_set.len(), "served cubes overlap");

    let mut raw_concrete = Vec::new();
    for cube in &reported {
        assignment_to_solutions(cube, &mut raw_concrete);
    }
    let raw_set: HashSet<&Vec<bool>> = raw_concrete.iter().collect();
    assert_eq!(raw_set, concrete_set, "dedup changed the covered model set");

    let mut solver = easy_build(6, spec);
    assert_eq!(62, weight(&solver.all_solutions()));
}
