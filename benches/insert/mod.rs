use criterion::{measurement::Measurement, BenchmarkGroup, BenchmarkId, Criterion, Throughput};
use interavl::IntervalTree;

use crate::Lfsr;

#[derive(Debug, Clone, Copy)]
struct BenchName {
    n_values: usize,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new("n_values", v.n_values)
    }
}

pub(super) fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("insert");

    for n_values in [1, 100, 1_000, 10_000] {
        bench_param(&mut g, n_values)
    }
}

/// Measure the time needed to insert `n_values` number of randomly generated
/// intervals into an empty tree.
fn bench_param<M>(g: &mut BenchmarkGroup<'_, M>, n_values: usize)
where
    M: Measurement,
{
    let bench_name = BenchName { n_values };
    g.throughput(Throughput::Elements(n_values as _)); // Keys inserted per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter_batched(
            || (IntervalTree::default(), Lfsr::default()),
            |(mut t, mut rand)| {
                for _i in 0..n_values {
                    let range = rand.next_range();
                    t.insert(range, 42_usize);
                }
                t
            },
            criterion::BatchSize::PerIteration,
        );
    });
}
