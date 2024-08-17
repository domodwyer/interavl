use crate::node::Node;

#[derive(Debug)]
pub(crate) struct RefIter<'a, R, V> {
    stack: Vec<&'a Node<R, V>>,
}

impl<'a, R, V> RefIter<'a, R, V> {
    pub(crate) fn new(root: &'a Node<R, V>) -> Self {
        let mut this = Self { stack: vec![] };

        // Descend down the left side of the tree.
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

impl<'a, R, V> Iterator for RefIter<'a, R, V> {
    type Item = &'a Node<R, V>;

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
