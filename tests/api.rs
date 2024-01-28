#[test]
fn basic_api() {
    test_pool_api(arcpool::Pool::builder().finish());
    test_pool_api(
        arcpool::Pool::builder()
            .with_default_page_size(1024)
            .finish(),
    );
    test_pool_api(
        arcpool::Pool::builder()
            .with_default_page_size(4096)
            .with_page_allocation_lock(true)
            .finish(),
    );
    test_pool_api(
        arcpool::Pool::builder()
            .with_page_allocation_lock(true)
            .finish(),
    );
}

fn test_pool_api(pool: arcpool::Pool<String>) {
    let arg = pool.checkout();

    arg.get_mut().unwrap().push_str("hello, world!");
    drop(arg);

    // Check internal logic: Reuse recent first
    let arg = pool.checkout();
    assert_eq!(*arg, "hello, world!");

    let _back = pool.checkout();
    let arg = pool.checkout();

    // Check downgrade works
    arg.get_mut().unwrap().push_str("second, world!");
    let weak_arg = arg.downgrade();

    // Check if upgrade works well.
    assert!(weak_arg.upgrade().is_some());

    // Check if reusing expired slot works well
    {
        let arg_addr = arg.as_ptr();
        drop(arg);

        assert!(weak_arg.upgrade().is_none());

        let arg = pool.checkout();
        assert_eq!(arg.as_ptr(), arg_addr);
    }

    // Check drop logic works well
    drop(pool);
}
