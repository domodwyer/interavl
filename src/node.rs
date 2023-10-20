use std::cmp::Ordering;

#[derive(Debug)]
pub(crate) struct Node {
    value: usize,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    pub(crate) fn new(value: usize) -> Self {
        Self {
            value,
            left: None,
            right: None,
        }
    }

    pub(crate) fn insert(&mut self, value: usize) {
        let node = match value.cmp(&self.value) {
            Ordering::Less => &mut self.left,
            Ordering::Equal => return,
            Ordering::Greater => &mut self.right,
        };

        match node {
            Some(v) => v.insert(value),
            None => *node = Some(Box::new(Node::new(value))),
        }
    }

    pub(crate) fn value(&self) -> usize {
        self.value
    }

    pub(crate) fn left(&self) -> Option<&Node> {
        self.left.as_deref()
    }

    pub(crate) fn right(&self) -> Option<&Node> {
        self.right.as_deref()
    }
}
