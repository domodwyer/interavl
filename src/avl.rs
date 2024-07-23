use std::cmp::Ordering;

use crate::node::{remove_recurse, Node, RemoveResult};

#[derive(Debug, Default)]
pub(crate) struct IntervalTree(Option<Box<Node>>);

// TODO(dom): iter, range iter

impl IntervalTree {
    pub(crate) fn insert(&mut self, value: usize) -> bool {
        match self.0 {
            Some(ref mut v) => v.insert(value),
            None => {
                self.0 = Some(Box::new(Node::new(value)));
                true
            }
        }
    }

    pub(crate) fn contains(&self, value: usize) -> bool {
        self.0
            .as_ref()
            .map(|v| v.contains(value))
            .unwrap_or_default()
    }

    pub(crate) fn remove(&mut self, value: usize) -> Option<usize> {
        match remove_recurse(&mut self.0, value)? {
            RemoveResult::Removed(v) => Some(v),
            RemoveResult::ParentUnlink => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use proptest::prelude::*;

    use super::*;
    use crate::dot::print_dot;

    #[test]
    fn test_insert_contains() {
        let mut t = IntervalTree::default();

        t.insert(42);
        t.insert(22);
        t.insert(25);

        assert!(t.contains(42));
        assert!(t.contains(22));
        assert!(t.contains(25));

        assert!(!t.contains(26));
        assert!(!t.contains(43));
        assert!(!t.contains(41));

        validate_tree_structure(&t);
    }

    #[test]
    fn test_insert_remove_contains() {
        const N: usize = 50;

        let mut t = IntervalTree::default();

        for i in 0..N {
            t.insert(i);
        }

        for i in 0..(N / 2) {
            t.remove(i);
        }

        for i in 0..(N / 2) {
            assert!(!t.contains(i));
        }

        for i in (N / 2)..N {
            assert!(t.contains(i));
        }

        validate_tree_structure(&t);
    }

    #[test]
    fn test_update_after_subtree_min_extract() {
        let values = [
            28, 44, 49, 16, 2, 29, 30, 7, 48, 46, 26, 31, 11, 21, 6, 19, 33, 42, 36, 0, 41, 23, 43,
            5, 14,
        ];

        let mut t = IntervalTree::default();

        // Insert all the values.
        for &v in &values {
            t.insert(v);
        }

        validate_tree_structure(&t);

        // Ensure contains() returns true for all of them and remove all
        // values that were inserted.
        for &v in &values {
            // Remove the node (that should exist).
            assert!(t.contains(v));
            assert_eq!(t.remove(v), Some(v));

            // Attempting to remove the value a second time is a no-op.
            assert!(!t.contains(v));
            assert_eq!(t.remove(v), None);

            // At all times, the tree must be structurally sound.
            validate_tree_structure(&t);
        }
    }

    const N_VALUES: usize = 200;

    #[derive(Debug)]
    enum Op {
        Insert(usize),
        Contains(usize),
        Remove(usize),
    }

    fn arbitrary_op() -> impl Strategy<Value = Op> {
        // A small value domain encourages multiple operations to act on the
        // same value.
        prop_oneof![
            (0..15_usize).prop_map(Op::Insert),
            (0..15_usize).prop_map(Op::Contains),
            (0..15_usize).prop_map(Op::Remove),
        ]
    }

    proptest! {
        /// Insert values into the tree and assert contains() returns true for
        /// each.
        #[test]
        fn prop_insert_contains(
            a in prop::collection::hash_set(0..N_VALUES, 0..N_VALUES),
            b in prop::collection::hash_set(0..N_VALUES, 0..N_VALUES),
        ) {
            let mut t = IntervalTree::default();

            // Assert contains does not report the values in "a" as existing.
            for &v in &a {
                assert!(!t.contains(v));
            }

            // Insert all the values in "a"
            for &v in &a {
                t.insert(v);
            }

            // Ensure contains() returns true for all of them
            for &v in &a {
                assert!(t.contains(v));
            }

            // Assert the values in the control set (the random values in "b"
            // that do not appear in "a") return false for contains()
            for &v in b.difference(&a) {
                assert!(!t.contains(v));
            }

            validate_tree_structure(&t);
        }

        /// Insert values into the tree and delete them after, asserting they
        /// are removed and the extracted values are returned.
        #[test]
        fn prop_insert_contains_remove(
            values in prop::collection::hash_set(0..N_VALUES, 0..N_VALUES),
        ) {
            let mut t = IntervalTree::default();

            // Insert all the values.
            for &v in &values {
                t.insert(v);
            }

            validate_tree_structure(&t);

            // Ensure contains() returns true for all of them and remove all
            // values that were inserted.
            for &v in &values {
                // Remove the node (that should exist).
                assert!(t.contains(v));
                assert_eq!(t.remove(v), Some(v));

                // Attempting to remove the value a second time is a no-op.
                assert!(!t.contains(v));
                assert_eq!(t.remove(v), None);

                // At all times, the tree must be structurally sound.
                validate_tree_structure(&t);
            }

            assert_eq!(t.remove(N_VALUES+1), None);
        }

        #[test]
        fn prop_tree_operations(
            ops in prop::collection::vec(arbitrary_op(), 1..50),
        ) {
            let mut t = IntervalTree::default();
            let mut model = HashSet::new();

            for op in ops {
                match op {
                    Op::Insert(v) => {
                        let did_insert_tree = t.insert(v);
                        let did_insert_model = model.insert(v);
                        assert_eq!(did_insert_tree, did_insert_model);
                    },
                    Op::Contains(v) => {
                        assert_eq!(
                            t.contains(v),
                            model.contains(&v),
                            "tree contains() = {}, model.contains() = {}",
                            t.contains(v),
                            model.contains(&v)
                        );
                    },
                    Op::Remove(v) => {
                        let t_got = t.remove(v);
                        let model_got = model.remove(&v);
                        assert_eq!(
                            t_got.is_some(),
                            model_got,
                            "tree remove() = {:?}, model.remove() = {}",
                            t_got,
                            model_got,
                        );
                    },
                }

                // At all times, the tree must uphold the AVL tree invariants.
                validate_tree_structure(&t);
            }

            for v in model {
                assert!(t.contains(v));
            }
        }
    }

    /// Assert the BST and AVL properties of tree nodes, ensuring the tree
    /// is well-formed.
    fn validate_tree_structure(t: &IntervalTree) {
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
            assert!(n.left().map(|v| v.value() < n.value()).unwrap_or(true));

            // Invariant 2: the right child always contains a value striggctly
            // greater than this node.
            assert!(n.right().map(|v| v.value() > n.value()).unwrap_or(true));

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
                "expect node with value {} to have height {}, has {}",
                n.value(),
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
        }
    }
}
