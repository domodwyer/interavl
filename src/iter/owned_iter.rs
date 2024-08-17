use std::ops::Range;

use crate::node::Node;

/// An iterator of owned [`Node`] instances as the underlying tree `into_iter()`
/// impl.
#[derive(Debug)]
pub struct OwnedIter<T, R> {
    stack: Vec<Box<Node<T, R>>>,
}

impl<T, R> OwnedIter<T, R> {
    pub(crate) fn new(root: Option<Box<Node<T, R>>>) -> Self {
        let mut this = Self { stack: vec![] };

        // Descend down the left side of the tree.
        if let Some(root) = root {
            this.push_subtree(root);
        }

        this
    }

    fn push_subtree(&mut self, subtree_root: Box<Node<T, R>>) {
        let mut ptr = Some(subtree_root);

        while let Some(mut v) = ptr {
            ptr = v.take_left();
            self.stack.push(v);
        }
    }
}

impl<T, R> Iterator for OwnedIter<T, R> {
    type Item = (Range<R>, T);

    fn next(&mut self) -> Option<Self::Item> {
        let mut v = self.stack.pop()?;

        // Descend down the left side of the right hand child of this node, if
        // any.
        if let Some(right) = v.take_right() {
            self.push_subtree(right);
        }

        Some(v.into_tuple())
    }
}
