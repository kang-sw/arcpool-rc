use std::time::Instant;

use criterion::{criterion_group, criterion_main, Criterion};

criterion_main!(poc);
criterion_group!(poc, at_size_1k, at_size_10k, at_size_100k);

fn at_size_1k(b: &mut Criterion) {
    at_size(b, 10_00);
}

fn at_size_10k(b: &mut Criterion) {
    at_size(b, 10_000);
}

fn at_size_100k(b: &mut Criterion) {
    at_size(b, 100_000);
}

fn at_size(b: &mut Criterion, nsample: usize) {
    let mut group = b.benchmark_group(format!("average remove-insertion at size {}", nsample));

    group.bench_function("linear", |b| {
        let pool =
            lockfree_object_pool::LinearObjectPool::<[usize; 8]>::new(Default::default, |_| ());

        let mut items = Vec::with_capacity(nsample);
        items.resize_with(items.capacity(), || pool.pull());

        b.iter(|| {
            items.swap_remove(rand::random::<usize>() % items.len());
            items.push(pool.pull());
        });
    });

    group.bench_function("arcpool", |b| {
        let pool = arcpool::Pool::<[usize; 8]>::builder().finish();

        let mut items = Vec::with_capacity(nsample);
        items.resize_with(items.capacity(), || pool.checkout());

        b.iter(|| {
            items.swap_remove(rand::random::<usize>() % items.len());
            items.push(pool.checkout());
        });
    });

    const NTHREAD: usize = 8;

    group.bench_function("mt/linear", |b| {
        b.iter_custom(|iter| {
            let pool =
                lockfree_object_pool::LinearObjectPool::<[usize; 8]>::new(Default::default, |_| ());

            let mut items = Vec::with_capacity(nsample);
            items.resize_with(items.capacity(), || pool.pull());

            let start_at = Instant::now();
            std::thread::scope(|sp| {
                for _ in 0..NTHREAD {
                    let iter_sub = iter / NTHREAD as u64;
                    let pool = &pool;
                    let mut items = items
                        .drain(0..(iter_sub as usize).min(items.len()))
                        .collect::<Vec<_>>();

                    sp.spawn(move || {
                        for _ in 0..iter_sub {
                            if !items.is_empty() {
                                items.swap_remove(rand::random::<usize>() % items.len());
                            }
                            items.push(pool.pull());
                        }
                    });
                }
            });

            start_at.elapsed()
        });
    });

    group.bench_function("mt/arcpool", |b| {
        b.iter_custom(|iter| {
            let pool = arcpool::Pool::<[usize; 8]>::builder().finish();

            let mut items = Vec::with_capacity(nsample);
            items.resize_with(items.capacity(), || pool.checkout());

            let start_at = Instant::now();
            std::thread::scope(|sp| {
                for _ in 0..NTHREAD {
                    let iter_sub = iter / NTHREAD as u64;
                    let pool = &pool;
                    let mut items = items
                        .drain(0..(iter_sub as usize).min(items.len()))
                        .collect::<Vec<_>>();

                    sp.spawn(move || {
                        for _ in 0..iter_sub {
                            if !items.is_empty() {
                                items.swap_remove(rand::random::<usize>() % items.len());
                            }

                            items.push(pool.checkout());
                        }
                    });
                }
            });

            start_at.elapsed()
        });
    });

    group.finish();
}
