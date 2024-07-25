use std::{fmt::Debug, ops::Range};

use crate::{
    interval::Interval,
    iter::Iter,
    node::{remove_recurse, Node, RemoveResult},
};

#[derive(Debug, Clone)]
pub struct IntervalTree<T, R>(Option<Box<Node<T, R>>>);

impl<T, R> Default for IntervalTree<T, R> {
    fn default() -> Self {
        Self(Default::default())
    }
}

// TODO(dom): iter, range iter

// TODO(dom): entry + entry_mut -> Vec

impl<T, R> IntervalTree<T, R>
where
    R: Ord,
{
    pub fn insert(&mut self, range: Range<R>, value: T) -> Option<T>
    where
        R: Clone,
    {
        let interval = Interval::from(range);
        match self.0 {
            Some(ref mut v) => v.insert(interval, value),
            None => {
                self.0 = Some(Box::new(Node::new(interval, value)));
                None
            }
        }
    }

    pub fn get(&self, range: &Range<R>) -> Option<&T> {
        self.0.as_ref().and_then(|v| v.get(range))
    }

    pub fn contains(&self, range: &Range<R>) -> bool {
        self.get(range).is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Range<R>, &T)> {
        self.0
            .iter()
            .flat_map(|v| Iter::new(v))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    pub fn overlaps<'a>(
        &'a self,
        range: &'a Range<R>,
    ) -> impl Iterator<Item = (&Range<R>, &T)> + 'a {
        self.0
            .iter()
            .flat_map(|v| Iter::new(v))
            .filter(|v| v.interval().overlaps(range))
            .map(|v| (v.interval().as_range(), v.value()))
    }

    pub fn remove(&mut self, range: &Range<R>) -> Option<T>
    where
        R: Clone + Debug,
    {
        match remove_recurse(&mut self.0, range)? {
            RemoveResult::Removed(v) => Some(v),
            RemoveResult::ParentUnlink => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use proptest::prelude::*;

    use super::*;
    use crate::test_utils::arbitrary_range;

    #[test]
    fn test_insert_contains() {
        let mut t = IntervalTree::default();

        t.insert(42..45, 1);
        t.insert(22..23, 2);
        t.insert(25..29, 3);

        assert!(t.contains(&(42..45)));
        assert!(t.contains(&(22..23)));
        assert!(t.contains(&(25..29)));

        // Does not contain slight bounding variations of the first insert.
        assert!(!t.contains(&(42..46)));
        assert!(!t.contains(&(42..44)));
        assert!(!t.contains(&(41..45)));
        assert!(!t.contains(&(43..45)));

        validate_tree_structure(&t);
    }

    /// Ensure inserting references as the tree value is supported.
    #[test]
    fn test_insert_refs() {
        let mut t = IntervalTree::default();

        t.insert(42..45, "bananas");
        assert!(t.contains(&(42..45)));

        validate_tree_structure(&t);
    }

    const N_VALUES: usize = 200;

    #[derive(Debug)]
    enum Op {
        Insert(Range<usize>, usize),
        Get(Range<usize>),
        Contains(Range<usize>),
        Remove(Range<usize>),
    }

    fn arbitrary_op() -> impl Strategy<Value = Op> {
        // A small value domain encourages multiple operations to act on the
        // same value.
        prop_oneof![
            (arbitrary_range(), any::<usize>()).prop_map(|(r, v)| Op::Insert(r, v)),
            arbitrary_range().prop_map(Op::Get),
            arbitrary_range().prop_map(Op::Contains),
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
                assert!(!t.contains(v));
            }

            // Insert all the values in "a"
            for v in &a {
                t.insert(v.clone(), 42);
            }

            // Ensure contains() returns true for all of them
            for v in &a {
                assert!(t.contains(v));
            }

            // Assert the values in the control set (the random values in "b"
            // that do not appear in "a") return false for contains()
            for v in b.difference(&a) {
                assert!(!t.contains(v));
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
                assert!(t.contains(v));
                assert_eq!(t.remove(v), Some(42));

                // Attempting to remove the value a second time is a no-op.
                assert!(!t.contains(v));
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
                    Op::Get(range) => {
                        assert_eq!(
                            t.get(&range),
                            model.get(&range),
                            "tree contains() = {:?}, model.contains() = {:?}",
                            t.get(&range),
                            model.get(&range)
                        );
                    },
                    Op::Contains(range) => {
                        assert_eq!(
                            t.contains(&range),
                            model.contains_key(&range),
                            "tree contains() = {}, model.contains() = {}",
                            t.contains(&range),
                            model.contains_key(&range)
                        );
                    },
                    Op::Remove(range) => {
                        let t_got = t.remove(&range);
                        let model_got = model.remove(&range);
                        assert_eq!(
                            t_got,
                            model_got,
                            "tree remove() = {:?}, model.remove() = {:?}",
                            t_got,
                            model_got,
                        );
                    },
                }

                // At all times, the tree must uphold the AVL tree invariants.
                validate_tree_structure(&t);
            }

            for (range, _v) in model {
                assert!(t.contains(&range));
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
                t.insert(range.clone(), value);
            }

            // Collect all tuples from the iterator.
            let tuples = t.iter().collect::<Vec<_>>();

            // The yield ordering is stable.
            {
                let tuples2 = t.iter().collect::<Vec<_>>();
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
                .map(|(r, v)| (r.clone(), **v))
                .collect::<HashMap<_, _>>();

            assert_eq!(tuples, values);
        }

        /// Ensure that the "overlaps" iter yields only ranges that overlap with
        /// the query range.
        #[test]
        fn prop_overlaps(
            query in arbitrary_range(),
            values in prop::collection::vec(
                arbitrary_range(),
                0..10
            ),
        ) {
            // Collect all the "values" that overlap with "query".
            //
            // This forms the expected set of results.
            let control = values
                .iter()
                .filter(|v| Interval::from((*v).clone()).overlaps(&query))
                .collect::<HashSet<_>>();

            // Populate the tree.
            let mut t = IntervalTree::default();
            for range in &values {
                t.insert(range.clone(), 42);
            }

            // Extract all the overlapping ranges.
            let got = t.overlaps(&query).map(|v| v.0).collect::<HashSet<_>>();

            // And assert the sets match.
            assert_eq!(got, control);
        }
    }

    /// Assert the BST, AVL and interval tree properties of tree nodes, ensuring
    /// the tree is well-formed.
    fn validate_tree_structure<T, R>(t: &IntervalTree<T, R>)
    where
        R: Ord + PartialEq + Debug + Clone,
        T: Debug,
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
