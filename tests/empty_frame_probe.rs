use happier::{SATState, Variable};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};

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

fn build(spec: &Spec, vars: usize) -> SATState {
    let mut solver = SATState::new();
    solver.new_variable_at(vars - 1);
    for clause in spec {
        let lits: Vec<happier::Literal> = clause
            .iter()
            .map(|&(var, pos)| Variable::new(var as u32).literal(pos))
            .collect();
        if !lits.is_empty() {
            solver.add_clause(lits);
        }
    }
    solver
}

fn satisfies(spec: &Spec, model: usize) -> bool {
    spec.iter().all(|clause| {
        clause
            .iter()
            .any(|&(v, pos)| ((model >> v) & 1 == 1) == pos)
    })
}

fn oracle(spec: &Spec, vars: usize) -> (bool, Vec<bool>) {
    let mut any = false;
    let mut can = vec![false; vars];
    for model in 0..1usize << vars {
        if satisfies(spec, model) {
            any = true;
            for (var, slot) in can.iter_mut().enumerate() {
                *slot |= (model >> var) & 1 == 1;
            }
        }
    }
    (any, can)
}

#[derive(Default)]
struct Tally {
    instances: usize,
    violations: usize,
    mismatches: usize,
    other_panics: usize,
    violation_but_correct: usize,
}

static QUIET: AtomicUsize = AtomicUsize::new(0);

fn silence_panics() {
    if QUIET.fetch_add(1, Ordering::SeqCst) == 0 {
        std::panic::set_hook(Box::new(|_| {}));
    }
}

fn describe(spec: &Spec) -> String {
    spec.iter()
        .map(|clause| {
            clause
                .iter()
                .map(|&(v, pos)| if pos { format!("{v}") } else { format!("~{v}") })
                .collect::<Vec<_>>()
                .join(" ")
        })
        .collect::<Vec<_>>()
        .join(" / ")
}

fn check(spec: &Spec, vars: usize, label: &str, tally: &mut Tally) {
    assert!(vars <= 16, "oracle is 2^n, keep n small");
    tally.instances += 1;
    let (_sat, expected) = oracle(spec, vars);

    let mut solver = build(spec, vars);
    let outcome = catch_unwind(AssertUnwindSafe(|| solver.can_pos(0..vars)));

    match outcome {
        Ok(got) => {
            if got != expected {
                tally.mismatches += 1;
                println!(
                    "MISMATCH [{label}] n={vars} clauses: {}\n  expected {expected:?}\n  got      {got:?}",
                    describe(spec)
                );
            }
        }
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_default();
            if msg.contains("invariant_frame_owns_contradictions") {
                tally.violations += 1;
                println!(
                    "VIOLATION [{label}] n={vars} clauses: {}\n  oracle can_pos {expected:?}",
                    describe(spec)
                );
            } else {
                tally.other_panics += 1;
                println!(
                    "OTHER PANIC [{label}] n={vars}: {msg}\n  clauses: {}",
                    describe(spec)
                );
            }
        }
    }
}

fn probe_answer_despite_violation(_spec: &Spec, _vars: usize) -> Option<Vec<bool>> {
    None
}

fn report(name: &str, tally: &Tally) {
    println!(
        "[{name}] instances={} violations={} mismatches={} other_panics={} violation_but_correct={}",
        tally.instances,
        tally.violations,
        tally.mismatches,
        tally.other_panics,
        tally.violation_but_correct
    );
}

fn strategy_one(seed: u64, k: usize, n: usize) -> Spec {
    let mut rng = Lcg(seed);
    let mut spec: Spec = Vec::new();

    let a = rng.next(k);
    let mut b = rng.next(k);
    while b == a {
        b = rng.next(k);
    }
    let mut c = rng.next(k);
    while c == a || c == b {
        c = rng.next(k);
    }
    for pattern in 0..8 {
        spec.push(vec![
            (a, pattern & 1 == 1),
            (b, pattern & 2 == 2),
            (c, pattern & 4 == 4),
        ]);
    }
    for _ in 0..rng.next(4) {
        let mut clause = Vec::new();
        while clause.len() < 3 {
            let v = rng.next(k);
            if !clause.iter().any(|&(u, _)| u == v) {
                clause.push((v, rng.next(2) == 1));
            }
        }
        spec.push(clause);
    }

    let high = n - k;
    for _ in 0..2 + rng.next(3) {
        let mut clause = Vec::new();
        while clause.len() < 3.min(high) {
            let v = k + rng.next(high);
            if !clause.iter().any(|&(u, _)| u == v) {
                clause.push((v, true));
            }
        }
        spec.push(clause);
    }
    spec
}

#[test]
#[ignore = "~90s exploratory sweep; run explicitly with --ignored"]
fn strategy_one_disjoint_unsat_core_and_inert_tail() {
    silence_panics();
    let mut tally = Tally::default();
    let mut correct_despite_violation: Vec<(Spec, usize, Vec<bool>, Vec<bool>)> = Vec::new();

    for seed in 0..400u64 {
        for &(k, n) in &[(3usize, 9usize), (4, 10), (3, 12), (5, 11), (4, 14)] {
            let spec = strategy_one(seed, k, n);
            let before = tally.violations;
            check(&spec, n, "s1", &mut tally);
            if tally.violations > before {
                let (_, expected) = oracle(&spec, n);
                if let Some(got) = probe_answer_despite_violation(&spec, n)
                    && got == expected
                {
                    tally.violation_but_correct += 1;
                    correct_despite_violation.push((spec.clone(), n, expected, got));
                }
            }
        }
    }

    report("strategy_one", &tally);
    for (spec, n, expected, got) in &correct_despite_violation {
        println!(
            "VIOLATION-WITH-CORRECT-ANSWER n={n} clauses: {}\n  expected {expected:?} got {got:?}",
            describe(spec)
        );
    }
}

fn strategy_two(seed: u64, n: usize) -> Spec {
    let mut rng = Lcg(seed);
    let dense = 2 + rng.next(n / 2);
    let mut spec: Spec = Vec::new();

    let clause_count = 4 + rng.next(4 * dense.max(1));
    for _ in 0..clause_count {
        let mut clause = Vec::new();
        let want = 1 + rng.next(3.min(dense).max(1));
        let mut guard = 0;
        while clause.len() < want && guard < 32 {
            guard += 1;
            let v = rng.next(dense);
            if !clause.iter().any(|&(u, _)| u == v) {
                clause.push((v, rng.next(2) == 1));
            }
        }
        if !clause.is_empty() {
            spec.push(clause);
        }
    }

    let mut sparse: Vec<usize> = (dense..n).collect();
    while sparse.len() >= 3 {
        if rng.next(3) == 0 {
            sparse.remove(0);
            continue;
        }
        let clause: Vec<(usize, bool)> = sparse.drain(..3).map(|v| (v, rng.next(2) == 1)).collect();
        spec.push(clause);
    }
    spec
}

#[test]
#[ignore = "~90s exploratory sweep; run explicitly with --ignored"]
fn strategy_two_sparse_isolated_variables() {
    silence_panics();
    let mut tally = Tally::default();
    let mut correct_despite_violation: Vec<(Spec, usize, Vec<bool>, Vec<bool>)> = Vec::new();

    for seed in 1000..2000u64 {
        for &n in &[10usize, 12, 14] {
            let spec = strategy_two(seed, n);
            let before = tally.violations;
            check(&spec, n, "s2", &mut tally);
            if tally.violations > before {
                let (_, expected) = oracle(&spec, n);
                if let Some(got) = probe_answer_despite_violation(&spec, n)
                    && got == expected
                {
                    tally.violation_but_correct += 1;
                    correct_despite_violation.push((spec.clone(), n, expected, got));
                }
            }
        }
    }

    report("strategy_two", &tally);
    for (spec, n, expected, got) in &correct_despite_violation {
        println!(
            "VIOLATION-WITH-CORRECT-ANSWER n={n} clauses: {}\n  expected {expected:?} got {got:?}",
            describe(spec)
        );
    }
}

fn known_failures() -> Vec<Spec> {
    let parse = |s: &str| -> Spec {
        s.lines()
            .filter_map(|line| {
                let lits: Vec<(usize, bool)> = line
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
    };
    vec![
        parse(
            "~8
             ~0 4
             ~10 ~0
             0 ~7
             10 ~4 ~7
             8 ~3 0
             7 3
             ~3 10",
        ),
        parse(
            "8 ~7 2
             ~4 ~8
             ~8 ~7
             ~9 2
             6
             9 ~0
             ~1 ~9
             7 9
             0 7
             1 ~0 10
             7 ~10
             ~2 8",
        ),
        parse(
            "~0 ~2
             ~6 9
             3 8 ~9
             ~1 8
             3 ~7 2
             1 6
             ~7 1 4
             ~4
             ~1 10
             ~8 7
             ~8 4 9
             ~9 ~3
             ~1 ~10 0",
        ),
    ]
}

fn strategy_three(base: &Spec, seed: u64, n: usize) -> Spec {
    let mut rng = Lcg(seed);
    let mut spec = base.clone();

    match rng.next(4) {
        0 => {
            let i = rng.next(spec.len());
            let j = rng.next(spec[i].len());
            spec[i][j].1 = !spec[i][j].1;
        }
        1 => {
            let i = rng.next(spec.len());
            spec.remove(i);
        }
        2 => {
            let i = rng.next(spec.len());
            let v = rng.next(11);
            if !spec[i].iter().any(|&(u, _)| u == v) {
                let pos = rng.next(2) == 1;
                spec[i].push((v, pos));
            }
        }
        _ => {
            let mut clause = Vec::new();
            while clause.len() < 2 {
                let v = rng.next(11);
                if !clause.iter().any(|&(u, _)| u == v) {
                    clause.push((v, rng.next(2) == 1));
                }
            }
            spec.push(clause);
        }
    }

    let mut fresh: Vec<usize> = (11..n).collect();
    while fresh.len() >= 3 {
        let clause: Vec<(usize, bool)> = fresh.drain(..3).map(|v| (v, rng.next(2) == 1)).collect();
        spec.push(clause);
    }
    spec
}

#[test]
#[ignore = "~90s exploratory sweep; run explicitly with --ignored"]
fn strategy_three_padded_perturbations_of_known_failures() {
    silence_panics();
    let mut tally = Tally::default();
    let mut correct_despite_violation: Vec<(Spec, usize, Vec<bool>, Vec<bool>)> = Vec::new();

    let bases = known_failures();
    for (bi, base) in bases.iter().enumerate() {
        for seed in 0..300u64 {
            for &n in &[11usize, 14, 16] {
                let spec = strategy_three(base, seed * 7 + bi as u64, n);
                let before = tally.violations;
                check(&spec, n, "s3", &mut tally);
                if tally.violations > before {
                    let (_, expected) = oracle(&spec, n);
                    if let Some(got) = probe_answer_despite_violation(&spec, n)
                        && got == expected
                    {
                        tally.violation_but_correct += 1;
                        correct_despite_violation.push((spec.clone(), n, expected, got));
                    }
                }
            }
        }
    }

    report("strategy_three", &tally);
    for (spec, n, expected, got) in &correct_despite_violation {
        println!(
            "VIOLATION-WITH-CORRECT-ANSWER n={n} clauses: {}\n  expected {expected:?} got {got:?}",
            describe(spec)
        );
    }
}
