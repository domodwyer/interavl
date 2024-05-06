use std::cmp::Ordering;

#[derive(Debug)]
pub(super) enum RemoveResult<T> {
    /// The value was removed from the tree.
    Removed(T),

    /// The direct descendent node contains the value, but contains no children
    /// and must be unlinked by the parent.
    ParentUnlink,
}

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
        let child = match value.cmp(&self.value) {
            Ordering::Less => &mut self.left,
            Ordering::Equal => return,
            Ordering::Greater => &mut self.right,
        };

        match child {
            Some(v) => {
                v.insert(value);
            }
            None => {
                // Insert the value as a new immediate descendent of self.
                *child = Some(Box::new(Self::new(value)));

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
        // was applied to can be used to infer which child subtree is now
        // unbalanced as a result.
        match (balance(self), self.left.as_ref(), self.right.as_ref()) {
            // Left-heavy
            (2, Some(l), _) if value < l.value => {
                *self = rotate_right(self.clone()); // TODO(dom): clone is recursive!
            }
            (2, Some(l), _) if value > l.value => {
                self.left = Some(rotate_left(self.left.take().unwrap()));
                *self = rotate_right(self.clone());
            }
            // Right-heavy
            (-2, _, Some(r)) if value > r.value => {
                *self = rotate_left(self.clone());
            }
            (-2, _, Some(r)) if value < r.value => {
                self.right = Some(rotate_right(self.right.take().unwrap()));
                *self = rotate_left(self.clone());
            }
            (-1..=1, _, _) => { /* The tree is well balanced */ }
            _ => unreachable!(),
        };

        // Invariant: the absolute difference between tree heights ("balance
        // factor") cannot exceed 1.
        debug_assert!(balance(self).abs() <= 1);
    }

    pub(super) fn remove(self: &mut Box<Self>, value: usize) -> Option<RemoveResult<usize>> {
        // Recurse down the subtree rooted at `self`.
        //
        // If the value is not found, or successfully removed, the result is
        // returned. If the direct descendent node contains the value and no
        // children, it returns [`RemoveResult::ParentUnlink`] and the node is
        // unlinked here in the parent before returning the result to the
        // caller.
        match value.cmp(&self.value()) {
            Ordering::Less => return remove_recurse(&mut self.left, value),
            Ordering::Greater => return remove_recurse(&mut self.right, value),
            Ordering::Equal => {
                // This node holds the value to be removed from the tree.
                debug_assert_eq!(self.value, value);
            }
        };

        // This node may have 0, 1 or 2 child node(s):
        //
        //                          +----------+
        //                          |  parent  |
        //                          +----------+
        //                                |
        //                                v
        //                          +----------+
        //                     +----|   self   |----+
        //                     |    +----------+    |
        //                     |                    |
        //                     v                    v
        //               +-----------+       +------------+
        //               | self.left |       | self.right |
        //               +-----------+       +------------+
        //
        // The minimum successor child (if any) should move to replace this
        // node.
        //
        // If the "self.right" has a left child, descend the left-most edge to
        // locate the successor to "self" returned in an in-order traversal and
        // use it in place of "self". The right child of "self" after removing
        // this successor (if any) is then linked to this replacement.
        //
        // If there is no left node of "self.right", the "self.right" itself
        // replaces the target node (the minimum subtree successor value).
        //
        // If there is no right child, then "self.left" replaces "self".
        let old = if let Some(mut right) = self.right.take() {
            debug_assert_ne!(self.height, 0);

            // Extract the minimum node in the node_right subtree, if any.
            match extract_subtree_min(&mut right) {
                Some(mut min) => {
                    // This minimum node "min" should be mutated to link
                    // self.right on the right, and self.left (if any) linked on
                    // the left in order to preserve the binary search property.
                    //
                    // The "min" node is guaranteed to have no left pointer as
                    // it is the left-most / minimum node in the subtree.
                    debug_assert!(min.left.is_none());
                    debug_assert!(min.right.is_none());

                    min.left = self.left.take();
                    min.right = Some(right);

                    std::mem::replace(self, min)
                }

                None => {
                    // Otherwise the extracted "right" is the successor, and can
                    // replace "self".
                    //
                    // It is guaranteed that "right" has no left pointer,
                    // otherwise the above branch would be taken.
                    debug_assert!(right.left.is_none());

                    right.left = self.left.take();
                    std::mem::replace(self, right)
                }
            }
        } else if let Some(left) = self.left.take() {
            // Otherwise, if "self" has a left child only, simply replace "self"
            // with the left child (the minimum subtree value).
            debug_assert!(self.right.is_none());
            debug_assert_ne!(self.height, 0);

            std::mem::replace(self, left)
        } else {
            // Otherwise "self" has no children.
            debug_assert!(self.left.is_none());
            debug_assert!(self.right.is_none());
            debug_assert_eq!(self.height, 0);

            // Parent will unlink this "self" node.
            return Some(RemoveResult::ParentUnlink);
        };

        // Invariant: the node being unlinked contains no subtree.
        debug_assert!(old.right.is_none());
        debug_assert!(old.left.is_none());

        // Invariant: the old node being unlinked does contain the target value.
        debug_assert_eq!(old.value, value);
        debug_assert_ne!(self.value, value); // The replacement node does not.

        Some(RemoveResult::Removed(old.value))
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

    pub(crate) fn left(&self) -> Option<&Self> {
        self.left.as_deref()
    }

    pub(crate) fn left_mut(&mut self) -> Option<&mut Box<Self>> {
        self.left.as_mut()
    }

    pub(crate) fn right(&self) -> Option<&Self> {
        self.right.as_deref()
    }

    pub(crate) fn right_mut(&mut self) -> Option<&mut Box<Self>> {
        self.right.as_mut()
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

/// Compute the "balance factor" of the subtree rooted at `n`.
///
/// Returns the subtree height skew / magnitude, which is a positive number when
/// left heavy, and a negative number when right heavy.
fn balance(n: &Node) -> i8 {
    // Correctness: the height is a u8, the maximal value of which fits in an
    // i16 without truncation or sign inversion.
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

/// Extracts the node holding the minimum subtree value in a descendent of
/// `root`, if any, linking the right subtree of the extracted node to in its
/// place.
fn extract_subtree_min(root: &mut Box<Node>) -> Option<Box<Node>> {
    // Descend left to the leaf.
    let v = match extract_subtree_min(root.left.as_mut()?) {
        Some(mut v) => Some(v),
        None => {
            // The left child is the end of the left edge.
            //
            // ```text
            //                 6
            //                / \
            //    here ->   <4>   7
            //              / \
            //             2   5
            //              \
            //               3
            // ```
            //
            // Unlink the right node of the left root, which will become the new
            // left node of "root" (if any).
            let mut left_right = root.left.as_mut().and_then(|v| v.right.take());

            std::mem::replace(&mut root.left, left_right)
        }
    };

    rebalance_after_remove(root);
    debug_assert!(balance(root).abs() <= 1);
    v
}

/// Recurse into `node`, calling [`Node::remove()`] to remove the provided
/// `value` from the subtree rooted at `node`, if it exists.
///
/// Returns [`None`] if the value is not found.
///
/// Clears the `node` pointer if the [`Node::remove()`] call returns
/// [`RemoveResult::ParentUnlink`], returning the extracted value within a
/// [`RemoveResult::Removed`] variant.
pub(super) fn remove_recurse(
    node: &mut Option<Box<Node>>,
    value: usize,
) -> Option<RemoveResult<usize>> {
    // Remove the value (if any) and rebalance the tree.
    let remove_ret = node.as_mut().and_then(|v| {
        let ret = v.remove(value)?;
        rebalance_after_remove(v);
        Some(ret)
    })?;

    let v = match remove_ret {
        RemoveResult::Removed(v) => v,
        RemoveResult::ParentUnlink => node.take().unwrap().value,
    };

    debug_assert_eq!(v, value);

    Some(RemoveResult::Removed(v))
}

fn rebalance_after_remove(v: &mut Box<Node>) {
    // Recompute the height of the relocated node.
    update_height(v);

    // And rebalance the subtree.
    match (balance(v)) {
        (2..) if v.left.as_deref().map(balance).unwrap_or_default() >= 0 => {
            *v = rotate_right(v.clone()); // TODO(dom): subtree clone
        }
        (2..) if v.left.as_deref().map(balance).unwrap_or_default() < 0 => {
            v.left = v.left.take().map(rotate_left);
            *v = rotate_right(v.clone()); // TODO(dom): subtree clone
        }
        (..=-2) if v.right.as_deref().map(balance).unwrap_or_default() <= 0 => {
            *v = rotate_left(v.clone()); // TODO(dom): subtree clone
        }
        (..=-2) if v.right.as_deref().map(balance).unwrap_or_default() > 0 => {
            v.right = v.right.take().map(rotate_right);
            *v = rotate_left(v.clone()); // TODO(dom): subtree clone
        }

        #[allow(clippy::manual_range_patterns)]
        -1 | 0 | 1 => { /* balanced */ }

        _ => unreachable!(),
    }

    // Invariant: the absolute difference between tree heights ("balance
    // factor") cannot exceed 1 after removing a value.
    debug_assert!(balance(v).abs() <= 1);
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

    #[test]
    fn test_extract_subtree_min() {
        //
        //          6
        //         / \
        //        4   7
        //       / \
        //      2   5
        //     / \
        //    1   3
        //
        let mut t = Box::new(Node::new(6));
        add_right(&mut t, 7);
        let v = add_left(&mut t, 4);
        add_right(v, 5);
        let v = add_left(v, 2);
        add_right(v, 3);
        add_left(v, 1);

        for want in [1, 2, 3] {
            let n: Box<Node> = extract_subtree_min(&mut t).unwrap();
            assert_eq!(n.value, want);
            assert!(n.right.is_none());
        }

        assert!(extract_subtree_min(&mut t).is_none());
        assert!(extract_subtree_min(&mut t).is_none());

        assert!(t.left.is_none());
        assert_eq!(t.value, 4);

        let right = t.right.as_ref().unwrap();
        assert_eq!(right.value, 6);
        assert_eq!(right.left.as_ref().unwrap().value, 5);
        assert_eq!(right.right.as_ref().unwrap().value, 7);
    }
}
