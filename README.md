# Arcpool

Arcpool is a Rust crate designed for efficient memory utilization and optimization in concurrent
programming environments. It provides a memory pool utility that facilitates better management of
memory allocation and recycling, especially in applications where memory allocation/deallocation is
frequent and performance is critical.

## Features

- **Efficient Memory Management:** Minimizes overheads associated with frequent
  allocation/deallocation.
- **Concurrency-Friendly:** Designed to operate safely and efficiently in multithreaded contexts.
- **Optimized for Reuse:** Encourages reuse of memory blocks, reducing the cost of memory
  operations.
- **Full of unverified Unsafe code** Use this at your own risk ... I will. 🤣

## Usage

To use Arcpool in your Rust project, add it as a dependency in your `Cargo.toml` file:

```toml
[dependencies]
arcpool = "0.1.0"
```

Then, import and use it in your Rust files:

```rust
use arcpool::Pool;

fn main() {
	let pool = Pool::<Vec<u8>>::builder()
		.with_default_page_size(128)
		.with_initializer(|| Vec::with_capacity(1024))
		.with_cleanup(Vec::clear)
		.build();
	
	let ptr = pool.checkout();
	
	// For non-send items. Returned handle will be marked as !Send + !Sync
	let ptr_local = pool.checkout_local();
}
```

## Examples

Here is a basic example of how to use Arcpool:

```rust
// TODO:
```

More examples can be found in the [examples
directory](https://github.com/kang-sw/arcpool-rs/tree/main/examples).

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
arcpool = "0.1.0"
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

