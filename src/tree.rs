use std::{fmt::Debug, ops::Range};

use crate::{
    interval::Interval,
    iter::{
        ContainsPruner, DuringPruner, FinishesPruner, MeetsPruner, MetByPruner, OverlapsPruner,
        OwnedIter, PrecededByPruner, PrecedesPruner, PruningIter, RefIter, StartsPruner,
    },
    node::{remove_recurse, Node, RemoveResult},
};

/// An [`IntervalTree`] stores `(interval, value)` tuple mappings, enabling
/// efficient lookup and querying of intervals that match a variety of temporal
/// relations described by [Allen's interval algebra].
///
/// This [`IntervalTree`] stores half-open intervals `[start, end)`.
///
/// Point queries can be expressed using a 0-length query interval (an example
/// for point `42` is the empty interval `[42, 42)`).
///
/// # Read Optimised
///
/// This [`IntervalTree`] is backed by an augmented AVL tree, and is optimised
/// for read / search performance.
///
/// The internal tree structure is modified during inserts to ensure the tree
/// always remains balanced. This bound on the worst-case tree height maintains
/// a logarithmic worst-case lookup time complexity at the cost of constant-time
/// subtree rotations during insert operations.
///
/// ## Node Metadata & `R: Clone`
///
/// Tree nodes maintain additional metadata to enable efficient pruning of
/// entire subtrees during lookup operations. This metadata requires the
/// interval bound type `R` to implement [`Clone`] which may be invoked during
/// insert operations.
///
/// If cloning `R` is prohibitively expensive consider using a reference-counted
/// type (such as [`Arc`] or [`Rc`]) to provide a [`Clone`] implementation
/// without needing to copy the actual content.
///
/// ## Invalid Intervals
///
/// This implementation will accept invalid intervals such as `[42, 0)` without
/// panicking but iteration results are undefined for these invalid intervals.
///
/// [Allen's interval algebra]:
///     https://en.wikipedia.org/wiki/Allen%27s_interval_algebra
/// [`Arc`]: std::sync::Arc
/// [`Rc`]: std::rc::Rc
#[derive(Debug, Clone)]
pub struct IntervalTree<R, V>(Option<Box<Node<R, V>>>);

impl<R, V> Default for IntervalTree<R, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

// TODO(dom): entry + entry_mut -> Vec

impl<R, V> IntervalTree<R, V>
where
    R: Ord + Clone + Debug,
{
    /// Insert an `(interval, value)` tuple into the tree.
    ///
    /// If the interval already existed in the tree, [`Some`] is returned with
    /// the old value.
    pub fn insert(&mut self, range: Range<R>, value: V) -> Option<V> {
        let interval = Interval::from(range);
        match self.0 {
            Some(ref mut v) => v.insert(interval, value),
            None => {
                self.0 = Some(Box::new(Node::new(interval, value)));
                None
            }
        }
    }

    /// Return a reference to the value associated with the specified `range`,
    /// if any.
    pub fn get(&self, range: &Range<R>) -> Option<&V> {
        self.0.as_ref().and_then(|v| v.get(range))
    }

    /// Return a mutable reference to the value associated with the specified
    /// `range`, if any.
    pub fn get_mut(&mut self, range: &Range<R>) -> Option<&mut V> {
        self.0.as_mut().and_then(|v| v.get_mut(range))
    }

    /// Returns `true`` if the tree contains a value for the specified interval.
    pub fn contains_key(&self, range: &Range<R>) -> bool {
        self.get(range).is_some()
    }

    /// Remove the interval and associated value from the tree.
    ///
    /// Returns [`None`] if `range` was not present in the tree.
    pub fn remove(&mut self, range: &Range<R>) -> Option<V> {
        match remove_recurse(&mut self.0, range)? {
            RemoveResult::Removed(v) => Some(v),
            RemoveResult::ParentUnlink => unreachable!(),
        }
    }

    /// Iterate over references of all `(interval, value)` tuples stored in this
    /// tree.
    ///
    /// # Ordering
    ///
    /// The returned [`Iterator`] yields values from lowest to highest ordered
    /// by the interval lower bound, with ties broken by the upper bound.
    pub fn iter(&self) -> impl Iterator<Item = (&Range<R>, &V)> {
        self.0
            .iter()
            .flat_map(|v| RefIter::new(v))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which overlap
    /// with the specified query range (an "interval stabbing" query).
    ///
    /// The diagram below shows two intervals where `X` overlaps the query range
    /// `Y`, and `Y` overlaps `X`:
    ///
    /// ```text
    ///                           X
    ///                   ■■■■■■■■■■■■■■■■■
    ///
    ///                               ■■■■■■■■■■■■■■■■■
    ///                                       Y
    /// ```
    ///
    pub fn iter_overlaps<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, OverlapsPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which precede
    /// the specified query range.
    ///
    /// The diagram below shows two intervals where `X` precedes the query range
    /// `Y`:
    ///
    /// ```text
    ///                        X
    ///                ■■■■■■■■■■■■■■■■■
    ///
    ///                                    ■■■■■■■■■■■■■■■■■
    ///                                            Y
    /// ```
    ///
    pub fn iter_precedes<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, PrecedesPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are
    /// preceded by the specified query range.
    ///
    /// The diagram below shows two intervals where `X` is preceded by the query
    /// range `Y`:
    ///
    /// ```text
    ///                                            X
    ///                                    ■■■■■■■■■■■■■■■■■
    ///
    ///                ■■■■■■■■■■■■■■■■■
    ///                        Y
    /// ```
    ///
    pub fn iter_preceded_by<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, PrecededByPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which meet the
    /// specified query range.
    ///
    /// The diagram below shows two intervals where `X` meets the query range
    /// `Y`:
    ///
    /// ```text
    ///                           X
    ///                   ■■■■■■■■■■■■■■■■■
    ///
    ///                                    ■■■■■■■■■■■■■■■■■
    ///                                            Y
    /// ```
    ///
    pub fn iter_meets<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, MeetsPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are met
    /// by the specified query range.
    ///
    /// The diagram below shows two intervals where `X` is met by the query
    /// range `Y`:
    ///
    /// ```text
    ///                                            X
    ///                                    ■■■■■■■■■■■■■■■■■
    ///
    ///                   ■■■■■■■■■■■■■■■■■
    ///                           Y
    /// ```
    ///
    pub fn iter_met_by<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, MetByPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are
    /// started by the specified query range.
    ///
    /// The diagram below shows two intervals where `X` starts the query range
    /// `Y`:
    ///
    /// ```text
    ///                                   X
    ///                           ■■■■■■■■■■■■■■■■■
    ///
    ///                           ■■■■■■■■■■■
    ///                                Y
    /// ```
    ///
    pub fn iter_starts<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, StartsPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are
    /// finished by the specified query range.
    ///
    /// The diagram below shows two intervals where `X` finishes the query range
    /// `Y`:
    ///
    /// ```text
    ///                                X
    ///                        ■■■■■■■■■■■■■■■■■
    ///
    ///                              ■■■■■■■■■■■
    ///                                   Y
    /// ```
    ///
    pub fn iter_finishes<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, FinishesPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are
    /// during the specified query range.
    ///
    /// The diagram below shows two intervals where `X` is during the query
    /// range `Y`:
    ///
    /// ```text
    ///                                X
    ///                           ■■■■■■■■■■■
    ///
    ///                        ■■■■■■■■■■■■■■■■■
    ///                                Y
    /// ```
    ///
    pub fn iter_during<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, DuringPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    /// Return all `(interval, value)` tuples that have intervals which are
    /// contained by the specified query range.
    ///
    /// The diagram below shows two intervals where `X` contains the query range
    /// `Y`:
    ///
    /// ```text
    ///                                X
    ///                        ■■■■■■■■■■■■■■■■■
    ///
    ///                           ■■■■■■■■■■■
    ///                                Y
    /// ```
    ///
    pub fn iter_contains<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.0
            .iter()
            .flat_map(|v| PruningIter::new(v, range, ContainsPruner))
            .map(|v| (v.interval().as_range(), v.value()))
    }
}

/// Take ownership of this [`IntervalTree`] instance and iterate over all
/// `(interval, value)` tuples stored in it.
///
/// # Ordering
///
/// The returned [`Iterator`] yields values from lowest to highest ordered by
/// the interval lower bound, with ties broken by the upper bound.
impl<R, V> std::iter::IntoIterator for IntervalTree<R, V> {
    type Item = (Range<R>, V);
    type IntoIter = OwnedIter<R, V>;

    fn into_iter(self) -> Self::IntoIter {
        OwnedIter::new(self.0)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::{atomic::AtomicUsize, Arc},
    };

    use proptest::prelude::*;

    use super::*;
    use crate::test_utils::{arbitrary_range, Lfsr, NodeFilterCount};

    #[test]
    fn test_insert_contains() {
        let mut t = IntervalTree::default();

        t.insert(42..45, 1);
        t.insert(22..23, 2);
        t.insert(25..29, 3);

        assert!(t.contains_key(&(42..45)));
        assert!(t.contains_key(&(22..23)));
        assert!(t.contains_key(&(25..29)));

        // Does not contain slight bounding variations of the first insert.
        assert!(!t.contains_key(&(42..46)));
        assert!(!t.contains_key(&(42..44)));
        assert!(!t.contains_key(&(41..45)));
        assert!(!t.contains_key(&(43..45)));

        validate_tree_structure(&t);
    }

    /// Ensure inserting references as the tree value is supported.
    #[test]
    fn test_insert_refs() {
        let mut t = IntervalTree::default();

        t.insert(42..45, "bananas");
        assert!(t.contains_key(&(42..45)));

        validate_tree_structure(&t);
    }

    const N_VALUES: usize = 200;

    #[derive(Debug)]
    enum Op {
        Insert(Range<usize>, usize),
        Get(Range<usize>),
        ContainsKey(Range<usize>),
        Update(Range<usize>, usize),
        Remove(Range<usize>),
    }

    fn arbitrary_op() -> impl Strategy<Value = Op> {
        // A small value domain encourages multiple operations to act on the
        // same value.
        prop_oneof![
            (arbitrary_range(), any::<usize>()).prop_map(|(r, v)| Op::Insert(r, v)),
            (arbitrary_range(), any::<usize>()).prop_map(|(r, v)| Op::Update(r, v)),
            arbitrary_range().prop_map(Op::Get),
            arbitrary_range().prop_map(Op::ContainsKey),
            arbitrary_range().prop_map(Op::Remove),
        ]
    }

    proptest! {
        /// Insert values into the tree and assert contains() returns true for
        /// each.
        #[test]
        fn prop_insert_contains(
            a in prop::collection::hash_set(arbitrary_range(), 0..N_VALUES),
            b in prop::collection::hash_set(arbitrary_range(), 0..N_VALUES),
        ) {
            let mut t = IntervalTree::default();

            // Assert contains does not report the values in "a" as existing.
            for v in &a {
                assert!(!t.contains_key(v));
            }

            // Insert all the values in "a"
            for v in &a {
                t.insert(v.clone(), 42);
            }

            // Ensure contains() returns true for all of them
            for v in &a {
                assert!(t.contains_key(v));
            }

            // Assert the values in the control set (the random values in "b"
            // that do not appear in "a") return false for contains()
            for v in b.difference(&a) {
                assert!(!t.contains_key(v));
            }

            validate_tree_structure(&t);
        }

        /// Insert (range, value) tuples into the tree and assert the mapping
        /// behaves the same as a hashmap (a control model).
        #[test]
        fn prop_range_to_value_mapping(
            values in prop::collection::hash_map(arbitrary_range(), any::<usize>(), 0..N_VALUES),
        ) {
            let mut t = IntervalTree::default();
            let mut control = HashMap::with_capacity(values.len());

            // Insert all the values, ensuring the tree and the control map
            // return the same "this was new" signals.
            for (range, v) in &values {
                assert_eq!(t.insert(range.clone(), v), control.insert(range, v));
            }

            validate_tree_structure(&t);

            // Validate that reading the value for a given key returns the
            // expected result.
            for range in values.keys() {
                assert_eq!(t.get(range), control.get(range));
            }

            // Then validate that all the stored values match when removing.
            for (range, v) in control {
                assert_eq!(t.remove(range).unwrap(), v);
            }

            validate_tree_structure(&t);
        }

        /// Insert values into the tree and delete them after, asserting they
        /// are removed and the extracted values are returned.
        #[test]
        fn prop_insert_contains_remove(
            values in prop::collection::hash_set(arbitrary_range(), 0..N_VALUES),
        ) {
            let mut t = IntervalTree::default();

            // Insert all the values.
            for v in &values {
                t.insert(v.clone(), 42);
            }

            validate_tree_structure(&t);

            // Ensure contains() returns true for all of them and remove all
            // values that were inserted.
            for v in &values {
                // Remove the node (that should exist).
                assert!(t.contains_key(v));
                assert_eq!(t.remove(v), Some(42));

                // Attempting to remove the value a second time is a no-op.
                assert!(!t.contains_key(v));
                assert_eq!(t.remove(v), None);

                // At all times, the tree must be structurally sound.
                validate_tree_structure(&t);
            }

            assert_eq!(t.remove(&(N_VALUES..N_VALUES+1)), None);
        }

        #[test]
        fn prop_tree_operations(
            ops in prop::collection::vec(arbitrary_op(), 1..50),
        ) {
            let mut t = IntervalTree::default();
            let mut model = HashMap::new();

            for op in ops {
                match op {
                    Op::Insert(range, v) => {
                        assert_eq!(t.insert(range.clone(), v), model.insert(range, v));
                    },
                    Op::Update(range, value) => {
                        // Both return the Some(v) or None
                        assert_eq!(t.get_mut(&range), model.get_mut(&range));
                        // Update if Some
                        if let Some(v) = t.get_mut(&range) {
                            *v = value;
                            *model.get_mut(&range).unwrap() = value;
                        }
                        // Must match after
                        assert_eq!(t.get(&range), model.get(&range));
                    },
                    Op::Get(range) => {
                        assert_eq!(t.get(&range), model.get(&range));
                    },
                    Op::ContainsKey(range) => {
                        assert_eq!(t.contains_key(&range), model.contains_key(&range));
                    },
                    Op::Remove(range) => {
                        assert_eq!(t.remove(&range), model.remove(&range));
                    },
                }

                // At all times, the tree must uphold the AVL tree invariants.
                validate_tree_structure(&t);
            }

            for (range, _v) in model {
                assert!(t.contains_key(&range));
            }
        }

        /// Insert values into the tree and assert the returned tuples are
        /// ordered by their interval start/end matching the Interval Ord
        /// implementation, and all tuples are yielded.
        #[test]
        fn prop_iter(
            values in prop::collection::hash_map(
                arbitrary_range(), any::<usize>(),
                0..N_VALUES
            ),
        ) {
            let mut t = IntervalTree::default();

            for (range, value) in &values {
                t.insert(range.clone(), *value);
            }

            // Collect all tuples from the iterator.
            let tuples = t.iter().collect::<Vec<_>>();

            // The yield ordering is stable.
            {
                let tuples2 = t.iter().collect::<Vec<(&Range<usize>, &usize)>>();
                assert_eq!(tuples, tuples2);
            }

            // Assert the tuples are ordered consistently with how the Interval
            // orders ranges (lowest to highest, by start bounds and tie-broken
            // by end bounds).
            for window in tuples.windows(2) {
                let a = Interval::from(window[0].0.clone());
                let b = Interval::from(window[1].0.clone());
                assert!(a < b);
            }

            // And all input tuples appear in the iterator output.
            let tuples = tuples
                .into_iter()
                .map(|(r, v)| (r.clone(), *v))
                .collect::<HashMap<_, _>>();

            assert_eq!(tuples, values);
        }

        /// Validate the owned iterator yields all tuples ordered from lowest to
        /// highest.
        #[test]
        fn prop_into_iter(
            values in prop::collection::hash_map(
                arbitrary_range(), any::<usize>(),
                0..N_VALUES
            ),
        ) {
            let mut t = IntervalTree::default();

            for (range, value) in &values {
                t.insert(range.clone(), *value);
            }

            // Collect all tuples from the iterator.
            let tuples = t.into_iter().collect::<Vec<(Range<usize>, usize)>>();

            // Assert the tuples are ordered consistently with how the Interval
            // orders ranges (lowest to highest, by start bounds and tie-broken
            // by end bounds).
            for window in tuples.windows(2) {
                let a = Interval::from(window[0].0.clone());
                let b = Interval::from(window[1].0.clone());
                assert!(a < b);
            }

            // And all input tuples appear in the iterator output.
            let tuples = tuples
                .into_iter()
                .map(|(r, v)| (r.clone(), v))
                .collect::<HashMap<_, _>>();

            assert_eq!(tuples, values);
        }
    }

    macro_rules! assert_pruning_stats {
        (
            $t:ident,
            $ty:ty,
            want_yield = $want_yield:literal,
            want_visited = $want_visited:literal
        ) => {
            paste::paste! {{
                // Walk the tree with each pruning iter, and record the number of nodes
                // that were visited after pruning.
                let n_filtered = Arc::new(AtomicUsize::new(0));
                let iter = PruningIter::new(
                    $t.0.as_deref().unwrap(),
                    &Range { start: 42, end: 1042 },
                    NodeFilterCount::new($ty, Arc::clone(&n_filtered)),
                );

                // Validate the expected number of nodes are yielded.
                let n_yielded = iter.count();
                assert_eq!(n_yielded, $want_yield, "yield count differs for {}", stringify!($ty));

                // And the number of nodes that were filtered after subtree pruning.
                let n_filtered = n_filtered.load(std::sync::atomic::Ordering::Relaxed);
                assert_eq!(n_filtered, $want_visited, "visited count differs for {}", stringify!($ty));
            }}
        };
    }

    /// Quantify the effectiveness of subtree pruning against a nominal tree.
    #[test]
    fn test_pruning_effectiveness() {
        const N: usize = (u16::MAX as usize - 1) / 2;

        let mut t: IntervalTree<_, usize> = IntervalTree::default();

        // Generate a tree of random, but valid intervals.
        let mut a = Lfsr::new(42);
        let mut b = Lfsr::new(24);

        for i in 0..N {
            let a = a.next();
            let b = b.next();

            let r = Range {
                start: a.min(b),
                end: a.max(b),
            };

            t.insert(r, i);
        }

        assert_pruning_stats!(t, OverlapsPruner, want_yield = 1043, want_visited = 1044);
        assert_pruning_stats!(t, PrecedesPruner, want_yield = 1, want_visited = 49);
        assert_pruning_stats!(
            t,
            PrecededByPruner,
            want_yield = 31722,
            want_visited = 32759
        );
        assert_pruning_stats!(t, MeetsPruner, want_yield = 0, want_visited = 49);
        assert_pruning_stats!(t, MetByPruner, want_yield = 1, want_visited = 32759);
        assert_pruning_stats!(t, StartsPruner, want_yield = 0, want_visited = 49);
        assert_pruning_stats!(t, FinishesPruner, want_yield = 0, want_visited = 32759);
        assert_pruning_stats!(t, DuringPruner, want_yield = 24, want_visited = 1045);
        assert_pruning_stats!(t, ContainsPruner, want_yield = 48, want_visited = 49);
    }

    /// Generate a proptest that asserts the [`IntervalTree`] returns the same
    /// tuples for a given interval iterator when compared to a control /
    /// brute-force filter implementation.
    macro_rules! test_algebraic_iter {
        ($name:tt) => {
            paste::paste! {
                proptest! {
                    #[test]
                    fn [<prop_algebraic_iter_ $name>](
                        query in arbitrary_range().prop_filter("invalid query interval", is_sane_interval),
                        values in prop::collection::vec(
                            arbitrary_range(),
                            0..10
                        ),
                    ) {
                        // Collect all the "values" that precede with "query".
                        //
                        // This forms the expected set of results.
                        let control = values
                            .iter()
                            .filter(|&v| is_sane_interval(v))
                            .filter(|&v| Interval::from(v.clone()).$name(&query))
                            .collect::<HashSet<_>>();

                        // Populate the tree.
                        let mut t = IntervalTree::default();
                        for range in &values {
                            t.insert(range.clone(), 42);
                        }

                        // Collect the iterator tuples.
                        let got = t
                            .[<iter_ $name>](&query)
                            .map(|v| v.0)
                            .filter(|&v| is_sane_interval(v))
                            .collect::<HashSet<_>>();

                        // And assert the sets match.
                        assert_eq!(got, control);
                    }
                }
            }
        };
    }

    /// Returns true if `r` is a valid interval.
    fn is_sane_interval<R>(r: &Range<R>) -> bool
    where
        R: Ord,
    {
        r.start <= r.end
    }

    test_algebraic_iter!(overlaps);
    test_algebraic_iter!(precedes);
    test_algebraic_iter!(preceded_by);
    test_algebraic_iter!(meets);
    test_algebraic_iter!(met_by);
    test_algebraic_iter!(starts);
    test_algebraic_iter!(finishes);
    test_algebraic_iter!(during);
    test_algebraic_iter!(contains);

    /// Assert the BST, AVL and interval tree properties of tree nodes, ensuring
    /// the tree is well-formed.
    fn validate_tree_structure<R, V>(t: &IntervalTree<R, V>)
    where
        R: Ord + PartialEq + Debug + Clone,
        V: Debug,
    {
        let root = match t.0.as_deref() {
            Some(v) => v,
            None => return,
        };

        // Perform a pre-order traversal of the tree.
        let mut stack = vec![root];
        while let Some(n) = stack.pop() {
            // Prepare to visit the children
            stack.extend(n.left().iter().chain(n.right().iter()));

            // Invariant 1: the left child always contains a value strictly
            // less than this node.
            assert!(n
                .left()
                .map(|v| v.interval() < n.interval())
                .unwrap_or(true));

            // Invariant 2: the right child always contains a value striggctly
            // greater than this node.
            assert!(n
                .right()
                .map(|v| v.interval() > n.interval())
                .unwrap_or(true));

            // Invariant 3: the height of this node is always +1 of the
            // maximum child height.
            let left_height = n.left().map(|v| v.height());
            let right_height = n.right().map(|v| v.height());
            let want_height = left_height
                .max(right_height)
                .map(|v| v + 1) // This node is +1 of the child, if any
                .unwrap_or_default(); // Otherwise it is at height 0

            assert_eq!(
                n.height(),
                want_height,
                "expect node with interval {:?} to have height {}, has {}",
                n.interval(),
                want_height,
                n.height(),
            );

            // Invariant 4: the absolute height difference between the left
            // subtree and right subtree (the "balance factor") cannot
            // exceed 1.
            let balance = left_height
                .and_then(|l| right_height.map(|r| l as i64 - r as i64))
                .unwrap_or_default()
                .abs();
            assert!(
                balance <= 1,
                "balance={balance}, node={n:?}, stack={stack:?}"
            );

            // Invariant 5: the subtree max of "n" must be equal to either the
            // largest of the two child subtree maxes, or its own upper bound.
            //
            // This indirectly validates that the subtree max of "n" is
            // greater-than-or-equal-to that of the left and right child's
            // subtree max value.
            let child_max = n
                .left()
                .map(|v| v.subtree_max())
                .max(n.right().map(|v| v.subtree_max()));
            let want_max = child_max.max(Some(n.interval().end())).unwrap();
            assert_eq!(want_max, n.subtree_max());
        }
    }
}
