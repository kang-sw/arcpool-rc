//! CLONED FROM [lockfree-object-pool benchmark
//! suite](https://github.com/EVaillant/lockfree-object-pool/tree/master/benches)

#[macro_use]
extern crate criterion;

use criterion::Criterion;
use rand::{Rng, SeedableRng};

mod bench_tools;

#[macro_use]
mod bench_generic;

struct AllocBenchElem {
    _data: Vec<u8>,
}

impl Default for AllocBenchElem {
    fn default() -> Self {
        Self {
            _data: Vec::with_capacity(16384),
        }
    }
}

impl sharded_slab::Clear for AllocBenchElem {
    fn clear(&mut self) {}
}

fn bench_alloc(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocation");
    bench_alloc_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync
    );
    bench_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        1
    );
    bench_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<AllocBenchElem>::new(32, Default::default),
        2
    );
    bench_alloc_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        3
    );
    group.finish();
}

fn bench_alloc_recycle(c: &mut Criterion) {
    let mut group = c.benchmark_group("recycling allocation");

    bench_recycle_alloc_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        1
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<AllocBenchElem>::new(32, Default::default),
        2
    );
    bench_recycle_alloc_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        3
    );
    group.finish();
}

fn bench_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("free");
    bench_free_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync
    );
    bench_free_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        1
    );
    bench_free_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<AllocBenchElem>::new(32, Default::default),
        2
    );
    bench_free_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        3
    );
    group.finish();
}

fn bench_alloc_mt(c: &mut Criterion) {
    let mut group = c.benchmark_group("multi thread allocation");
    bench_alloc_mt_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync
    );
    bench_alloc_mt_impl_!(
        group,
        "arcpool sync mode with lock config",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .with_page_allocation_lock(true)
            .finish(),
        4_sync
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        1
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<AllocBenchElem>::new(32, Default::default),
        2
    );
    bench_alloc_mt_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        3
    );
    group.finish();
}

fn bench_free_mt(c: &mut Criterion) {
    let mut group = c.benchmark_group("multi thread free");
    bench_free_mt_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync
    );
    bench_free_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        1
    );
    bench_free_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_mt_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        1
    );
    bench_free_mt_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<AllocBenchElem>::new(32, Default::default),
        2
    );
    bench_free_mt_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        3
    );
    group.finish();
}

fn bench_forward_multi_thread(c: &mut Criterion, nb_writter: usize, nb_readder: usize) {
    let mut group = c.benchmark_group(format!(
        "forward msg from pull (nb_writter:{} nb_readder:{})",
        nb_writter, nb_readder
    ));
    bench_forward_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<AllocBenchElem>::builder()
            .with_initializer(Default::default)
            .finish(),
        nb_readder,
        nb_writter,
        4_sync
    );
    bench_forward_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<AllocBenchElem>::new(Default::default),
        nb_readder,
        nb_writter,
        1
    );
    bench_forward_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        nb_readder,
        nb_writter,
        1
    );
    bench_forward_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        nb_readder,
        nb_writter,
        1
    );
    bench_forward_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<AllocBenchElem>::new(Default::default, |_v| {}),
        nb_readder,
        nb_writter,
        1
    );
    bench_forward_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<AllocBenchElem>::new(),
        nb_readder,
        nb_writter,
        3
    );
    group.finish();
}

fn bench_forward_multi_thread55(c: &mut Criterion) {
    bench_forward_multi_thread(c, 5, 5);
}

fn bench_forward_multi_thread15(c: &mut Criterion) {
    bench_forward_multi_thread(c, 1, 5);
}

fn bench_forward_multi_thread51(c: &mut Criterion) {
    bench_forward_multi_thread(c, 5, 1);
}

fn bench_forward_multi_thread11(c: &mut Criterion) {
    bench_forward_multi_thread(c, 1, 1);
}

// ========================================================== Dereference Benchmark ===|

#[derive(Default, Clone)]
struct ElemAccessBenchArg {
    value: u64,
}

impl sharded_slab::Clear for ElemAccessBenchArg {
    fn clear(&mut self) {}
}

fn bench_element_access(c: &mut Criterion, n: usize) {
    let mut group = c.benchmark_group(format!("element access: {n} "));

    macro_rules! bench_element_access_impl_ {
        ($group:expr, $name:literal, $expression:expr, $pull_impl:tt, $deref_impl:tt) => {
            $group.bench_function($name, |b| {
                let pool = $expression;

                let mut items = Vec::new();
                let mut rand = rand::rngs::StdRng::from_seed([0; 32]);

                for _ in 0..n {
                    items.push(pull_!(pool, $pull_impl));
                }

                b.iter(|| {
                    let pos1 = rand.gen_range(0..n);
                    let item1 = &items[pos1];
                    let item2 = &items[items.len() - pos1 - 1];

                    // Don't let the random generation be significant factor
                    for _ in 0..10000 {
                        std::hint::black_box(
                            deref_!(item1, $deref_impl).value + deref_!(item2, $deref_impl).value,
                        );
                    }
                })
            });
        };
    }

    group.bench_function("crate 'hecs'", |b| {
        let mut pool = hecs::World::new();

        let mut items = Vec::new();
        let mut rand = rand::rngs::StdRng::from_seed([0; 32]);

        for _ in 0..n {
            items.push(pool.spawn((ElemAccessBenchArg::default(),)));
        }

        let mut query = pool.query::<&ElemAccessBenchArg>();
        let view = query.view();

        b.iter(|| {
            let pos1 = rand.gen_range(0..n);
            let item1 = &items[pos1];
            let item2 = &items[items.len() - pos1 - 1];

            // Don't let the random generation be significant factor
            for _ in 0..10000 {
                std::hint::black_box(
                    view.get(*item1).unwrap().value + view.get(*item2).unwrap().value,
                );
            }
        })
    });

    bench_element_access_impl_!(
        group,
        "arcpool sync mode",
        arcpool::Pool::<ElemAccessBenchArg>::builder()
            .with_initializer(Default::default)
            .finish(),
        4_sync,
        any
    );

    bench_element_access_impl_!(
        group,
        "crate 'lockfree-object-pool' / none",
        lockfree_object_pool::NoneObjectPool::<ElemAccessBenchArg>::new(Default::default),
        1,
        any
    );
    bench_element_access_impl_!(
        group,
        "crate 'lockfree-object-pool' / mutex",
        lockfree_object_pool::MutexObjectPool::<ElemAccessBenchArg>::new(Default::default, |_v| {}),
        1,
        any
    );
    bench_element_access_impl_!(
        group,
        "crate 'lockfree-object-pool' / spin_lock",
        lockfree_object_pool::SpinLockObjectPool::<ElemAccessBenchArg>::new(
            Default::default,
            |_v| {}
        ),
        1,
        any
    );
    bench_element_access_impl_!(
        group,
        "crate 'lockfree-object-pool' / linear",
        lockfree_object_pool::LinearObjectPool::<ElemAccessBenchArg>::new(
            Default::default,
            |_v| {}
        ),
        1,
        any
    );
    bench_element_access_impl_!(
        group,
        "crate 'object-pool'",
        object_pool::Pool::<ElemAccessBenchArg>::new(32, Default::default),
        2,
        any
    );
    bench_element_access_impl_!(
        group,
        "crate 'sharded-slab'",
        sharded_slab::Pool::<ElemAccessBenchArg>::new(),
        3,
        any
    );

    group.finish();
}

fn bench_element_access128(c: &mut Criterion) {
    bench_element_access(c, 128);
}

fn bench_element_access1024(c: &mut Criterion) {
    bench_element_access(c, 1024);
}

fn bench_element_access16384(c: &mut Criterion) {
    bench_element_access(c, 16384);
}

criterion_group!(
    forward_multi_thread,
    bench_forward_multi_thread55,
    bench_forward_multi_thread15,
    bench_forward_multi_thread51,
    bench_forward_multi_thread11
);
criterion_group!(
    element_access,
    bench_element_access128,
    bench_element_access1024,
    bench_element_access16384
);
criterion_group!(multi_thread, bench_alloc_mt, bench_free_mt);
criterion_group!(mono_thread, bench_alloc_recycle, bench_alloc, bench_free,);
criterion_main!(
    mono_thread,
    element_access,
    multi_thread,
    forward_multi_thread
);
