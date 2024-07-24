use std::ops::Range;

use crate::node::Node;

#[derive(Debug)]
pub(crate) struct Iter<'a, T, R> {
    stack: Vec<&'a Node<T, R>>,
}

impl<'a, T, R> Iter<'a, T, R> {
    pub(crate) fn new(root: &'a Node<T, R>) -> Self {
        let mut this = Self { stack: vec![] };

        // Descend down the left side of the tree.
        this.push_subtree(root);

        this
    }

    fn push_subtree(&mut self, subtree_root: &'a Node<T, R>) {
        let mut ptr = Some(subtree_root);

        while let Some(v) = ptr {
            self.stack.push(v);
            ptr = v.left();
        }
    }
}

impl<'a, T, R> Iterator for Iter<'a, T, R> {
    type Item = &'a Node<T, R>;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.stack.pop()?;

        // Descend down the left side of the right hand child of this node, if
        // any.
        if let Some(right) = v.right() {
            self.push_subtree(right);
        }

        Some(v)
    }
}
