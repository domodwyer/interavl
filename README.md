[![crates.io](https://img.shields.io/crates/v/interavl.svg)](https://crates.io/crates/interavl)
[![docs.rs](https://docs.rs/interavl/badge.svg)](https://docs.rs/interavl)

# Interavl

This crate implements an [interval tree] backed by an augmented, balanced binary
search tree (an [AVL tree] - inter**avl** - get it?!)

<p align="center">
<img src="https://assets.itsallbroken.com/github/interavl.png" />
</p>

The `IntervalTree` maps half-open intervals to opaque values, and provides
efficient querying of all stored `(interval, value)` tuples that match a variety
of temporal relations described by [Allen's interval algebra].

## Use It

```rust
use interavl::IntervalTree;

// Initialise an empty tree.
let mut t = IntervalTree::default();

// Insert interval & value tuples into the tree.
//
// Intervals can be composed of any type that implements "Ord" such
// as timestamps, strings, etc.
t.insert(24..80, "Bob");
t.insert(10..100, "Doris");
t.insert(40..55, "Frank");
t.insert(100..400, "Nigel");

// Find which intervals overlap with a query interval:
for (interval, name) in t.iter_overlaps(&(42..50)) {
	println!("{name} overlaps (matching interval is {interval:?})");
}
```

## Performance

Lookup operations against an `IntervalTree` are _fast_, executing against
millions / billions of keys per second:

| Tree Size     | Build Tree | Lookup Value | Stabbing Query |
| ------------- | ---------- | ------------ | -------------- |
| 100 tuples    | 1.5µs      | 6ns          | 39ns           |
| 1,000 tuples  | 31µs       | 8ns          | 67ns           |
| 10,000 tuples | 777us      | 9ns          | 115ns          |

Interval stabbing and membership queries are particularly fast due to the use of
subtree pruning to reduce the search space.[^filter-perf]

* _Build Tree_: insert the N keys listed into an empty tree (inclusive of random
  value generation)
* _Lookup Value_: find an interval in the tree and return the value for it
* _Stabbing Query_: yield all intervals that overlap with a given query interval

The above measurements capture the single-threaded performance of operations
against a tree containing varying numbers of keys on a M1 MacBook Pro.

The benchmarks to generate these numbers are included in this repo (run `cargo
bench`).

[Interval Tree]: https://en.wikipedia.org/wiki/Interval_tree
[AVL tree]: https://en.wikipedia.org/wiki/AVL_tree
[Allen's interval algebra]:
    https://en.wikipedia.org/wiki/Allen%27s_interval_algebra

[^filter-perf]: Interval stabbing filters ~53 billion intervals per second.
