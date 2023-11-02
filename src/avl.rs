use crate::node::Node;

#[derive(Debug, Default)]
pub(crate) struct IntervalTree(Option<Box<Node>>);

impl IntervalTree {
    pub(crate) fn insert(&mut self, value: usize) {
        match self.0 {
            Some(ref mut v) => v.insert(value),
            None => self.0 = Some(Box::new(Node::new(value))),
        }
    }

    pub(crate) fn contains(&self, value: usize) -> bool {
        self.0
            .as_ref()
            .map(|v| v.contains(value))
            .unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
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
    }

    const N_VALUES: usize = 50;

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
        }

        /// Assert the BST and AVL properties of tree nodes, ensuring the tree
        /// is well-formed.
        #[test]
        fn prop_node_invariants(
            values in prop::collection::vec(any::<usize>(), 1..N_VALUES),
        ) {
            let mut t = IntervalTree::default();
            for v in values {
                t.insert(v);
            }

            // Perform a pre-order traversal of the tree.
            let mut stack = vec![t.0.as_deref().unwrap()];
            while let Some(n) = stack.pop() {
                // Prepare to visit the children
                stack.extend(n.left().iter().chain(n.right().iter()));

                // Invariant 1: the left child always contains a value strictly
                // less than this node.
                assert!(n.left().map(|v| v.value() < n.value()).unwrap_or(true));

                // Invariant 2: the right child always contains a value strictly
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

                assert_eq!(n.height(), want_height);

                // Invariant 4: the absolute height difference between the left
                // subtree and right subtree (the "balance factor") cannot
                // exceed 1.
                let balance = left_height
                    .and_then(|l| right_height.map(|r| l as i64 - r as i64))
                    .unwrap_or_default()
                    .abs();
                assert!(balance <= 1, "balance={balance}");
            }
        }
    }
}
