//! CLONED FROM [lockfree-object-pool benchmark
//! suite](https://github.com/EVaillant/lockfree-object-pool/tree/master/benches)

#[macro_use]
extern crate criterion;

use criterion::Criterion;

mod bench_tools;

#[macro_use]
mod bench_generic;

struct AllocBenchElem {
    _data: Vec<u8>,
}

impl Default for AllocBenchElem {
    fn default() -> Self {
        Self {
            _data: Vec::with_capacity(4096),
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

fn bench_element_access(c: &mut Criterion) {}

criterion_group!(
    forward_multi_thread,
    bench_forward_multi_thread55,
    bench_forward_multi_thread15,
    bench_forward_multi_thread51,
    bench_forward_multi_thread11
);
criterion_group!(multi_thread, bench_alloc_mt, bench_free_mt);
criterion_group!(mono_thread, bench_alloc_recycle, bench_alloc, bench_free,);
criterion_main!(mono_thread, multi_thread, forward_multi_thread);
