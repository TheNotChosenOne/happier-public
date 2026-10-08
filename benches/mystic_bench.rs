use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main, measurement::WallTime};
use happier::SATState;
use rustsat::instances::{BasicVarManager, SatInstance};
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Duration;

const DEFAULT_QUERY: std::ops::Range<usize> = 0..216;

const CORPUS: &str = "test_cases/mystic6x6";

const REPRESENTATIVE: [&str; 5] = [
    "000990_candidate.cnf",
    "000807_candidate.cnf",
    "000109_candidate.cnf",
    "000398_candidate.cnf",
    "000107_candidate.cnf",
];

struct Case {
    name: String,
    solver: SATState,
    query: std::ops::Range<usize>,
}

fn query_header(path: &Path) -> Option<std::ops::Range<usize>> {
    let content = std::fs::read_to_string(path).ok()?;
    for line in content.lines() {
        if let Some(rest) = line.strip_prefix("c query ") {
            let mut it = rest.split_whitespace();
            let start: usize = it.next()?.parse().ok()?;
            let end: usize = it.next()?.parse().ok()?;
            return Some(start..end);
        }
        if line.starts_with("p cnf") {
            break;
        }
    }
    None
}

fn load(dir: &Path) -> Vec<Case> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "cnf"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no instances in {}", dir.display());

    paths
        .iter()
        .map(|path| {
            let instance: SatInstance<BasicVarManager> = SatInstance::from_dimacs_path(path)
                .unwrap_or_else(|e| panic!("cannot parse {}: {e}", path.display()));

            let mut solver = SATState::new();
            solver.extend(instance.cnf().iter());

            Case {
                name: path.file_name().unwrap().to_string_lossy().into_owned(),
                solver,
                query: query_header(path).unwrap_or(DEFAULT_QUERY),
            }
        })
        .collect()
}

fn run(case: &Case) {
    let mut solver = case.solver.clone();
    black_box(solver.can_pos(case.query.clone()));
}

fn bench_case(group: &mut criterion::BenchmarkGroup<'_, WallTime>, case: &Case) {
    group.bench_with_input(BenchmarkId::from_parameter(&case.name), case, |b, case| {
        b.iter_batched_ref(
            || case.solver.clone(),
            |solver| black_box(solver.can_pos(case.query.clone())),
            criterion::BatchSize::PerIteration,
        )
    });
}

pub fn mystic_benchmark(c: &mut Criterion) {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(CORPUS);
    let cases = load(&dir);

    let mut group = c.benchmark_group("can_pos");
    group
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10));

    for name in REPRESENTATIVE {
        let case = cases
            .iter()
            .find(|c| c.name == name)
            .unwrap_or_else(|| panic!("representative instance {name} not in corpus"));
        bench_case(&mut group, case);
    }
    group.finish();

    let mut group = c.benchmark_group("can_pos_corpus");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(20));
    group.bench_function("all", |b| {
        b.iter(|| {
            for case in &cases {
                run(case);
            }
        })
    });
    group.finish();
}

criterion_group!(benches, mystic_benchmark);
criterion_main!(benches);
