use std::cmp::Ordering;

#[derive(Debug, Clone)]
pub(crate) struct Node {
    value: usize,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,

    /// The node's height.
    ///
    /// A leaf has a height of 0.
    ///
    /// A u8 holds a maximum value of 255, meaning it can represent the height
    /// of a balanced tree of up to 5.78×10⁷⁶ entries.
    height: u8,
}

impl Node {
    pub(crate) fn new(value: usize) -> Self {
        Self {
            value,
            left: None,
            right: None,
            height: 0,
        }
    }

    pub(crate) fn insert(self: &mut Box<Self>, value: usize) {
        let node = match value.cmp(&self.value) {
            Ordering::Less => &mut self.left,
            Ordering::Equal => return,
            Ordering::Greater => &mut self.right,
        };

        match node {
            Some(v) => {
                v.insert(value);
            }
            None => {
                // Insert the value as a new immediate descendent of self.
                *node = Some(Box::new(Node::new(value)));

                // Inserting this new child node cannot skew the tree in the
                // direction of the new addition such that it requires the tree
                // be rebalanced as, at most, it creates an absolute difference
                // of 1 in this direction (from balanced, or slightly skewed in
                // the opposite direction).
                //
                // Update this node and skip the rebalancing checks.
                update_height(self);
                return;
            }
        }

        // Update this node's height.
        update_height(self);

        // Determine the balance factor of the subtree rooted at self and
        // correct it if the absolute difference in height between branches is
        // > 1.
        //
        // If the balance factor is now 2/-2, then the above insertion has added
        // to an already 1/-1 skewed subtree - therefore the subtree the value
        // was applied to can be used to infer which subtree is now unbalanced
        // as a result.
        match (balance(self), self.left.as_ref(), self.right.as_ref()) {
            (2, Some(l), _) if value < l.value => {
                *self = rotate_right(self.clone());
            }
            (2, Some(l), _) if value > l.value => {
                self.left = Some(rotate_left(self.left.take().unwrap()));
                *self = rotate_right(self.clone());
            }
            (-2, _, Some(r)) if value > r.value => {
                *self = rotate_left(self.clone());
            }
            (-2, _, Some(r)) if value < r.value => {
                self.right = Some(rotate_right(self.right.take().unwrap()));
                *self = rotate_left(self.clone());
            }
            _ => { /* The tree is well balanced */ }
        };

        // Invariant: the absolute difference between tree heights ("balance
        // factor") cannot exceed 1.
        debug_assert!(balance(self).abs() <= 1);
    }

    pub(crate) fn contains(&self, value: usize) -> bool {
        let node = match value.cmp(&self.value) {
            Ordering::Less => self.left.as_ref(),
            Ordering::Equal => return true,
            Ordering::Greater => self.right.as_ref(),
        };

        node.map(|n| n.contains(value)).unwrap_or_default()
    }

    pub(crate) fn value(&self) -> usize {
        self.value
    }

    pub(crate) fn height(&self) -> u8 {
        self.height
    }

    pub(crate) fn left(&self) -> Option<&Node> {
        self.left.as_deref()
    }

    pub(crate) fn right(&self) -> Option<&Node> {
        self.right.as_deref()
    }
}

fn height(n: Option<&Node>) -> u8 {
    n.map(|v| v.height()).unwrap_or_default()
}

fn update_height(n: &mut Node) {
    n.height = n
        .left
        .as_ref()
        .map(|v| v.height() + 1)
        .max(n.right.as_ref().map(|v| v.height() + 1))
        .unwrap_or_default()
}

fn balance(n: &Node) -> i8 {
    // Correctness: the height is a u8, the maximal value of which fits in a i16
    // without truncation or sign inversion.
    (height(n.left()) as i16 - height(n.right()) as i16) as i8
}

/// Left rotate the given subtree rooted at `x` around the pivot point `P`.
///
/// ```text
///
///      x
///     / \                               P
///    1   P         Rotate Left        /   \
///       / \      --------------->    x     y
///      2   y                        / \   / \
///         / \                      1   2 3   4
///        3   4
/// ```
///
/// # Panics
///
/// Panics if `x` has no right pointer (cannot be rotated).
fn rotate_left(mut x: Box<Node>) -> Box<Node> {
    let mut p = x.right.take().unwrap();

    x.right = p.left;
    update_height(&mut x);

    p.left = Some(x);
    update_height(&mut p);

    p
}

/// Right rotate the given subtree rooted at `y` around the pivot point `P`.
///
/// ```text
///          y
///         / \                           P
///        P   4     Rotate Right       /   \
///       / \      --------------->    x     y
///      x   3                        / \   / \
///     / \                          1   2 3   4
///    1   2
/// ```
///
/// # Panics
///
/// Panics if `y` has no left pointer (cannot be rotated).
fn rotate_right(mut y: Box<Node>) -> Box<Node> {
    let mut p = y.left.take().unwrap();

    y.left = p.right;
    update_height(&mut y);

    p.right = Some(y);
    update_height(&mut p);

    p
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dot::print_dot;

    fn add_left(n: &mut Node, v: usize) -> &mut Node {
        assert!(n.left.is_none());
        n.left = Some(Box::new(Node::new(v)));
        n.left.as_mut().unwrap()
    }

    fn add_right(n: &mut Node, v: usize) -> &mut Node {
        assert!(n.right.is_none());
        n.right = Some(Box::new(Node::new(v)));
        n.right.as_mut().unwrap()
    }

    #[test]
    fn test_rotate_left() {
        //
        //      2
        //     / \                               4
        //    1   4         Rotate Left        /   \
        //       / \      --------------->    2     6
        //      3   6                        / \   / \
        //         / \                      1   3 5   7
        //        5   7
        //

        let mut t = Node::new(2);
        add_left(&mut t, 1);
        let v = add_right(&mut t, 4);
        add_left(v, 3);
        let v = add_right(v, 6);
        add_left(v, 5);
        add_right(v, 7);

        let t = rotate_left(Box::new(t));

        assert_eq!(t.value, 4);

        {
            let left_root = t.left().unwrap();
            assert_eq!(left_root.value, 2);

            let left = left_root.left().unwrap();
            assert_eq!(left.value, 1);

            let right = left_root.right().unwrap();
            assert_eq!(right.value, 3);
        }

        {
            let right_root = t.right().unwrap();
            assert_eq!(right_root.value, 6);

            let left = right_root.left().unwrap();
            assert_eq!(left.value, 5);

            let right = right_root.right().unwrap();
            assert_eq!(right.value, 7);
        }
    }

    #[test]
    fn test_rotate_right() {
        //
        //          6
        //         / \                           4
        //        4   7     Rotate Right       /   \
        //       / \      --------------->    2     6
        //      2   5                        / \   / \
        //     / \                          1   3 5   7
        //    1   3
        //
        let mut t = Node::new(6);
        add_right(&mut t, 7);
        let v = add_left(&mut t, 4);
        add_right(v, 5);
        let v = add_left(v, 2);
        add_right(v, 3);
        add_left(v, 1);

        let t = rotate_right(Box::new(t));

        assert_eq!(t.value, 4);

        {
            let left_root = t.left().unwrap();
            assert_eq!(left_root.value, 2);

            let left = left_root.left().unwrap();
            assert_eq!(left.value, 1);

            let right = left_root.right().unwrap();
            assert_eq!(right.value, 3);
        }

        {
            let right_root = t.right().unwrap();
            assert_eq!(right_root.value, 6);

            let left = right_root.left().unwrap();
            assert_eq!(left.value, 5);

            let right = right_root.right().unwrap();
            assert_eq!(right.value, 7);
        }
    }
}
