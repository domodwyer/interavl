use criterion::{
    measurement::Measurement, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
use interavl::IntervalTree;

use crate::Lfsr;

#[derive(Debug, Clone, Copy)]
struct BenchName {
    bench: &'static str,
    n_values: usize,
    n_lookups: usize,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new(
            format!("{}_values_{}_n_lookups", v.n_values, v.bench),
            v.n_lookups,
        )
    }
}

pub(super) fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("contains");

    // Tree size
    for n_values in [1_000, 10_000] {
        // Number of range lookups
        for n_lookups in [100, 1_000] {
            bench_param(&mut g, n_values, n_lookups)
        }
    }
}

/// For a tree containing `n_values`, perform two benchmarks that each perform
/// `n_lookups`, one run causing all hits, one run causing all misses.
fn bench_param<M>(g: &mut BenchmarkGroup<'_, M>, n_values: usize, n_lookups: usize)
where
    M: Measurement,
{
    // The tree must be at least as big as the number of lookups.
    assert!(n_values >= n_lookups);

    // Generate the tree.
    let mut rand = Lfsr::default();
    let mut t = IntervalTree::default();

    for _i in 0..n_values {
        let range = rand.next_range();
        t.insert(range, 42_usize);
    }

    // Perform a benchmark that continues using the LFSR to generate n_lookups
    // that will all miss.
    let bench_name = BenchName {
        bench: "misses",
        n_values,
        n_lookups,
    };

    // Perform a benchmark that looks up random ranges that do not exist in the
    // tree.
    g.throughput(Throughput::Elements(n_lookups as _)); // Lookups per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter_batched(
            // Provide the LFSR state after inserting n_values.
            //
            // It will now generate n_lookups of different ranges.
            || rand.clone(),
            |mut rand| {
                let mut any_hit = false;
                for _ in 0..n_lookups {
                    let range = rand.next_range();
                    any_hit |= t.contains_key(&range);
                }
                assert!(!any_hit)
            },
            BatchSize::SmallInput,
        )
    });

    let bench_name = BenchName {
        bench: "hits",
        n_values,
        n_lookups,
    };

    // Perform a benchmark that re-visits all the inserted values.
    g.throughput(Throughput::Elements(n_lookups as _)); // Lookups per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter_batched(
            // Reset the LFSR.
            //
            // It will now generate the same sequence of random ranges as what
            // was inserted into the tree originally.
            Lfsr::default,
            |mut rand| {
                let mut all_hit = true;
                for _ in 0..n_lookups {
                    let range = rand.next_range();
                    all_hit &= t.contains_key(&range);
                }
                assert!(all_hit);
            },
            BatchSize::SmallInput,
        )
    });
}
