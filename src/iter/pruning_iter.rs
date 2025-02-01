use std::ops::Range;

use crate::node::Node;

pub(crate) trait PruningOracle<R, V> {
    /// Returns true when the right node and subtree rooted at `subtree_root`
    /// should be descended into and evaluated.
    fn visit_right(&self, subtree_root: &Node<R, V>, query: &Range<R>) -> bool;

    /// Returns true if `n` satisfies the pruning logic and should be yielded to
    /// the caller.
    fn filter_yield(&self, n: &Node<R, V>, query: &Range<R>) -> bool;
}

/// An [`Iterator`] that performs a depth-first, in-order walk of a subtree and
/// yields [`Node`] instances that match a pruning predicate.
#[derive(Debug)]
pub(crate) struct PruningIter<'a, R, V, T> {
    query: &'a Range<R>,
    stack: Vec<&'a Node<R, V>>,
    pruner: T,
}

impl<'a, R, V, T> PruningIter<'a, R, V, T>
where
    R: Ord,
    T: PruningOracle<R, V>,
{
    pub(crate) fn new(root: &'a Node<R, V>, query: &'a Range<R>, pruner: T) -> Self {
        let mut this = Self {
            stack: vec![],
            query,
            pruner,
        };

        // Descend down the left side of the tree, pushing all the internal
        // nodes onto the stack until the left-most leaf is reached.
        this.push_subtree(root);

        this
    }

    fn push_subtree(&mut self, subtree_root: &'a Node<R, V>) {
        let mut ptr = Some(subtree_root);

        while let Some(v) = ptr {
            self.stack.push(v);
            ptr = v.left();
        }
    }
}

impl<'a, R, V, T> Iterator for PruningIter<'a, R, V, T>
where
    R: Ord,
    T: PruningOracle<R, V>,
{
    type Item = &'a Node<R, V>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let v = self.stack.pop()?;

            if !self.pruner.visit_right(v, self.query) {
                // Prune this node and the right subtree from the search.
                continue;
            }

            // Push the right subtree to be visited next.
            if let Some(right) = v.right() {
                self.push_subtree(right);
            }

            // Yield this node if it satisfies the pruning predicate.
            if self.pruner.filter_yield(v, self.query) {
                return Some(v);
            }
        }
    }
}
