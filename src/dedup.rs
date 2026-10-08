use alloc::vec;
use alloc::vec::Vec;
#[cfg(feature = "contracts")]
use contracts::debug_ensures as ensures;

pub type Cube = Vec<Option<bool>>;

#[cfg(feature = "contracts")]
fn cubes_disjoint(a: &[Option<bool>], b: &[Option<bool>]) -> bool {
    a.iter()
        .zip(b)
        .any(|(&x, &y)| matches!((x, y), (Some(x), Some(y)) if x != y))
}

#[derive(Debug, Clone, Default)]
pub struct DisjointCubes {
    served: Vec<Cube>,
}

impl DisjointCubes {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn served(&self) -> &[Cube] {
        &self.served
    }

    pub fn into_served(self) -> Vec<Cube> {
        self.served
    }

    #[cfg_attr(feature = "contracts", ensures(self.invariant_served_disjoint()))]
    pub fn admit(&mut self, cube: &[Option<bool>]) -> Vec<Cube> {
        debug_assert!(self.served.iter().all(|s| s.len() == cube.len()));
        let mut remainders = vec![cube.to_vec()];
        for served in &self.served {
            let mut survivors = Vec::with_capacity(remainders.len());
            for remainder in remainders {
                subtract_into(remainder, served, &mut survivors);
            }
            remainders = survivors;
            if remainders.is_empty() {
                break;
            }
        }
        self.served.extend(remainders.iter().cloned());
        remainders
    }

    #[cfg(feature = "contracts")]
    pub(crate) fn invariant_served_disjoint(&self) -> bool {
        (0..self.served.len()).all(|i| {
            (i + 1..self.served.len()).all(|j| cubes_disjoint(&self.served[i], &self.served[j]))
        })
    }
}

fn subtract_into(mut minuend: Cube, subtrahend: &[Option<bool>], out: &mut Vec<Cube>) {
    for (&m, &s) in minuend.iter().zip(subtrahend) {
        if let (Some(m), Some(s)) = (m, s)
            && m != s
        {
            out.push(minuend);
            return;
        }
    }

    for var in 0..minuend.len() {
        if minuend[var].is_none()
            && let Some(value) = subtrahend[var]
        {
            let mut remainder = minuend.clone();
            remainder[var] = Some(!value);
            out.push(remainder);
            minuend[var] = Some(value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const T: Option<bool> = Some(true);
    const F: Option<bool> = Some(false);
    const Q: Option<bool> = None;

    fn weight(cubes: &[Cube]) -> usize {
        cubes
            .iter()
            .map(|c| 1usize << c.iter().filter(|v| v.is_none()).count())
            .sum()
    }

    #[test]
    fn disjoint_cubes_pass_through_whole() {
        let mut dedup = DisjointCubes::new();
        assert_eq!(vec![vec![T, T, Q]], dedup.admit(&[T, T, Q]));
        assert_eq!(vec![vec![F, Q, Q]], dedup.admit(&[F, Q, Q]));
    }

    #[test]
    fn verbatim_replay_serves_nothing() {
        let mut dedup = DisjointCubes::new();
        dedup.admit(&[T, Q, F]);
        assert!(dedup.admit(&[T, Q, F]).is_empty());
    }

    #[test]
    fn narrower_replay_serves_nothing() {
        let mut dedup = DisjointCubes::new();
        dedup.admit(&[T, Q, Q]);
        assert!(dedup.admit(&[T, F, Q]).is_empty());
    }

    #[test]
    fn broader_replay_shatters_into_remainders() {
        let mut dedup = DisjointCubes::new();
        dedup.admit(&[T, T, T]);
        let served = dedup.admit(&[Q, Q, Q]);
        assert_eq!(7, weight(&served));
        assert_eq!(vec![vec![F, Q, Q], vec![T, F, Q], vec![T, T, F]], served);
    }

    #[test]
    fn partial_overlap_serves_only_the_difference() {
        let mut dedup = DisjointCubes::new();
        dedup.admit(&[T, Q, Q]);
        let served = dedup.admit(&[Q, Q, T]);
        assert_eq!(vec![vec![F, Q, T]], served);
        assert_eq!(4 + 2, weight(dedup.served()));
    }

    #[test]
    fn remainders_are_checked_against_every_served_cube() {
        let mut dedup = DisjointCubes::new();
        dedup.admit(&[T, Q, Q]);
        dedup.admit(&[F, T, Q]);
        assert_eq!(vec![vec![F, F, Q]], dedup.admit(&[Q, Q, Q]));
        assert_eq!(8, weight(dedup.served()));
    }
}
