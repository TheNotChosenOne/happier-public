#![allow(dead_code)]

use happier::{Control, SATState};

pub fn validate_solve(solver: &mut SATState, expected: bool) {
    let mut untouched = solver.clone();

    solver.presolve();
    let presolved = solver.clone();
    let result = solver.satisfiable(&mut happier::just_satisfiable);
    println!("Result: {result}, Expected: {expected}");
    assert_eq!(result, expected);
    solver.unroll();

    let _ = presolved;

    let mut retouched = untouched.clone();
    let result = retouched.satisfiable(&mut happier::just_satisfiable);
    assert_eq!(result, expected);

    println!("MANUAL SOLUTIONS");
    let mut solutioner = untouched.clone();
    let mut solcan_pos = vec![false; untouched.variable_count()];
    let result = solutioner.satisfiable(&mut |state| {
        let assignment = state
            .assignments()
            .iter()
            .map(|&a| a.unwrap_or(true))
            .collect::<Vec<_>>();
        for i in 0..assignment.len() {
            solcan_pos[i] |= assignment[i];
        }
        if solcan_pos.iter().all(|&b| b) {
            return Control::Stop;
        }
        Control::Continue
    });
    assert_eq!(result, expected);

    println!("CAN_POS 1");
    let can_pos = untouched.can_pos(0..untouched.variable_count());
    untouched.unroll();
    println!("CAN_POS 2");
    let can_pos2 = untouched.can_pos(0..untouched.variable_count());

    println!(
        "    Can pos: {:?}",
        can_pos
            .iter()
            .map(|&b| if b { 1 } else { 0 })
            .collect::<Vec<_>>()
    );
    println!(
        "Sol can pos: {:?}",
        solcan_pos
            .iter()
            .map(|&b| if b { 1 } else { 0 })
            .collect::<Vec<_>>()
    );
    assert_eq!(
        solcan_pos, can_pos,
        "manually foudn solutions did not match can_pos"
    );
    assert_eq!(
        can_pos, can_pos2,
        "repeated can_pos did not find the same solutions"
    );
}

pub fn easy_build(max: usize, spec: &str) -> SATState {
    let max = max + 1;
    let mut solver = SATState::new();
    let vars = (0..max).map(|_| solver.new_variable()).collect::<Vec<_>>();
    for clause in spec.lines() {
        let lits = clause
            .split_whitespace()
            .map(|line| {
                let negated = line.starts_with('~');
                let index = if negated {
                    line[1..].parse::<usize>().unwrap_or(0)
                } else {
                    line.parse::<usize>().unwrap_or(0)
                };
                let var = vars[index];
                var.literal(!negated)
            })
            .collect::<Vec<_>>();
        if !lits.is_empty() {
            solver.add_clause(lits);
        }
    }
    solver
}

pub fn loud_solution_count(solutions: &[Vec<Option<bool>>]) -> usize {
    let mut solution_count = 0;
    for solution in solutions {
        let nones = solution.iter().filter(|v| v.is_none()).count();
        solution_count += 1 << nones;
        print!("Solution: ");
        for (i, &v) in solution.iter().enumerate() {
            match v {
                Some(true) => print!(" {} ", i),
                Some(false) => print!("~{} ", i),
                None => print!("?{} ", i),
            }
        }
        println!();
    }
    solution_count
}

pub fn assignment_to_solutions(assignments: &[Option<bool>], solutions: &mut Vec<Vec<bool>>) {
    let unassigned_count = assignments.iter().filter(|a| a.is_none()).count();
    let mut solution = assignments
        .iter()
        .map(|&a| a.unwrap_or(false))
        .collect::<Vec<_>>();
    if 0 == unassigned_count {
        solutions.push(solution);
        return;
    }

    use itertools::Itertools;
    let indices = assignments
        .iter()
        .enumerate()
        .filter(|(_, a)| a.is_none())
        .map(|(i, _)| i)
        .collect::<Vec<_>>();

    for indices in indices.iter().copied().powerset() {
        for &index in &indices {
            solution[index] = true;
        }
        solutions.push(solution.clone());
        for &index in &indices {
            solution[index] = false;
        }
    }
}
