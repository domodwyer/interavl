use std::{fmt::Debug, ops::Range};

use crate::node::Node;

#[derive(Debug)]
pub(crate) struct OverlapsIter<'a, R, V> {
    query: &'a Range<R>,
    stack: Vec<&'a Node<R, V>>,
}

impl<'a, R, V> OverlapsIter<'a, R, V>
where
    R: Ord,
{
    pub(crate) fn new(root: &'a Node<R, V>, query: &'a Range<R>) -> Self {
        let mut this = Self {
            stack: vec![],
            query,
        };

        // Descend down the left side of the tree, pushing all the internal
        // nodes onto the stack until the left-most leaf is reached.
        this.push_subtree(root);

        this
    }

    fn push_subtree(&mut self, subtree_root: &'a Node<R, V>) {
        let mut ptr = Some(subtree_root);

        while let Some(v) = ptr {
            if self.query.start >= *v.subtree_max() {
                // Prune this subtree rooted at "v" from the search.
                //
                // All intervals in this subtree are strictly less than the
                // query range.
                break;
            }

            self.stack.push(v);
            ptr = v.left();
        }
    }
}

impl<'a, R, V> Iterator for OverlapsIter<'a, R, V>
where
    R: Ord,
{
    type Item = &'a Node<R, V>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let v = self.stack.pop()?;

            if self.query.end <= *v.interval().start() {
                // Prune this node and the right subtree from the search.
                //
                // All values in the right subtree are strictly greater than the
                // query range.
                continue;
            }

            // Push the right subtree to be visited next.
            if let Some(right) = v.right() {
                self.push_subtree(right);
            }

            // Yield this node if it overlaps with the query range.
            if v.interval().overlaps(self.query) {
                return Some(v);
            }
        }
    }
}
