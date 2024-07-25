use std::hint::black_box;

use criterion::{measurement::Measurement, BenchmarkGroup, BenchmarkId, Criterion, Throughput};
use interavl::IntervalTree;

use crate::Lfsr;

#[derive(Debug)]
struct BenchName {
    bench_name: &'static str,
    n_values: usize,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new(format!("{}/n_values", v.bench_name), v.n_values)
    }
}

pub(super) fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("iter");

    for n_values in [1, 100, 1_000, 10_000] {
        bench_param(&mut g, n_values)
    }
}

fn bench_param<M>(g: &mut BenchmarkGroup<'_, M>, n_values: usize)
where
    M: Measurement,
{
    // Generate the tree.
    let mut rand = Lfsr::default();
    let mut t = IntervalTree::default();

    for _i in 0..n_values {
        let range = rand.next_range();
        t.insert(range, 42_usize);
    }

    bench_iter(n_values, g, &t);
    bench_overlaps(n_values, g, &t);
}

fn bench_iter<M>(n_values: usize, g: &mut BenchmarkGroup<M>, t: &IntervalTree<usize, u16>)
where
    M: Measurement,
{
    let bench_name = BenchName {
        n_values,
        bench_name: "iter",
    };

    g.throughput(Throughput::Elements(n_values as _));
    // Values per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter(|| {
            let iter = t.iter();
            for v in iter {
                black_box(v);
            }
        })
    });
}

fn bench_overlaps<M>(n_values: usize, g: &mut BenchmarkGroup<M>, t: &IntervalTree<usize, u16>)
where
    M: Measurement,
{
    let bench_name = BenchName {
        n_values,
        bench_name: "overlaps",
    };

    g.throughput(Throughput::Elements(n_values as _));
    // Values per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter(|| {
            let iter = t.overlaps(&(42..100));
            for v in iter {
                black_box(v);
            }
        })
    });
}
