use std::{cmp::Ordering, fmt::Debug, ops::Range};

use crate::interval::Interval;

#[derive(Debug)]
pub(super) enum RemoveResult<T> {
    /// The value was removed from the tree.
    Removed(T),

    /// The direct descendent node contains the value, but contains no children
    /// and must be unlinked by the parent.
    ParentUnlink,
}

#[derive(Debug, Clone)]
pub(crate) struct Node<R, V> {
    /// Child nodes pointers.
    left: Option<Box<Node<R, V>>>,
    right: Option<Box<Node<R, V>>>,

    /// The node's AVL height.
    ///
    /// A leaf has a height of 0.
    ///
    /// A u8 holds a maximum value of 255, meaning it can represent the height
    /// of a balanced tree of up to 5.78*10⁷⁶ entries.
    height: u8,

    /// The maximum upper bound of all intervals for the subtree rooted at this
    /// [`Node`].
    subtree_max: R,

    interval: Interval<R>,
    value: V,
}

impl<R, V> Node<R, V> {
    pub(crate) fn new(interval: Interval<R>, value: V) -> Self
    where
        R: Clone,
    {
        Self {
            subtree_max: interval.end().clone(),
            interval,
            value,
            left: None,
            right: None,
            height: 0,
        }
    }

    pub(crate) fn insert(self: &mut Box<Self>, interval: Interval<R>, value: V) -> Option<V>
    where
        R: Ord + Clone,
    {
        let child = match interval.cmp(&self.interval) {
            Ordering::Less => &mut self.left,
            Ordering::Equal => {
                return Some(std::mem::replace(&mut self.value, value));
            }
            Ordering::Greater => &mut self.right,
        };

        let inserted = match child {
            Some(v) => v.insert(interval, value),
            None => {
                // Insert the value as a new immediate descendent of self.
                *child = Some(Box::new(Self::new(interval, value)));

                // Inserting this new child node cannot skew the tree in the
                // direction of the new addition such that it requires the tree
                // be rebalanced as, at most, it creates an absolute difference
                // of 1 in this direction (from balanced, or slightly skewed in
                // the opposite direction).
                //
                // Update this node and skip the rebalancing checks.
                update_height(self);
                update_subtree_max(self);
                return None;
            }
        };

        if inserted.is_some() {
            // The tree structure has not been modified, so it does not require
            // rebalancing.
            return inserted;
        }

        // Update this node's height.
        update_height(self);

        // Determine the balance factor of the subtree rooted at self and
        // correct it if the absolute difference in height between branches is
        // > 1.
        match (balance(self), self.left(), self.right()) {
            // Left-heavy
            (2, Some(l), _) if balance(l) >= 0 => {
                rotate_right(self);
            }
            (2, Some(_l), _) => {
                rotate_left(self.left_mut().unwrap());
                rotate_right(self);
            }
            // Right-heavy
            (-2, _, Some(r)) if balance(r) < 0 => {
                rotate_left(self);
            }
            (-2, _, Some(_r)) => {
                rotate_right(self.right_mut().unwrap());
                rotate_left(self);
            }
            (-1..=1, _, _) => { /* The tree is well balanced */ }
            _ => unreachable!(),
        };

        update_subtree_max(self);

        // Invariant: the absolute difference between tree heights ("balance
        // factor") cannot exceed 1.
        debug_assert!(balance(self).abs() <= 1);

        debug_assert!(inserted.is_none());
        None
    }

    pub(super) fn remove(self: &mut Box<Self>, range: &Range<R>) -> Option<RemoveResult<V>>
    where
        R: Ord + Clone + Debug,
    {
        // Recurse down the subtree rooted at `self`.
        //
        // If the value is not found, or successfully removed, the result is
        // returned. If the direct descendent node contains the value and no
        // children, it returns [`RemoveResult::ParentUnlink`] and the node is
        // unlinked here in the parent before returning the result to the
        // caller.
        match self.interval.partial_cmp(range).unwrap() {
            Ordering::Greater => return remove_recurse(&mut self.left, range),
            Ordering::Less => return remove_recurse(&mut self.right, range),
            Ordering::Equal => {
                // This node holds the value to be removed from the tree.
                debug_assert_eq!(self.interval, *range);
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
        debug_assert_eq!(old.interval, *range);
        debug_assert_ne!(self.interval, *range); // The replacement node does not.

        Some(RemoveResult::Removed(old.value))
    }

    pub(crate) fn get(&self, range: &Range<R>) -> Option<&V>
    where
        R: Ord + Eq,
    {
        let node = match self.interval.partial_cmp(range).unwrap() {
            Ordering::Greater => self.left(),
            Ordering::Equal => return Some(&self.value),
            Ordering::Less => self.right(),
        }?;

        // Prune this subtree from the search if the maximum upper bound in the
        // subtree is less than the search upper bound. If true, this subtree
        // cannot contain the search range.
        if *node.subtree_max() < range.end {
            return None;
        }

        node.get(range)
    }

    pub(crate) fn get_mut(&mut self, range: &Range<R>) -> Option<&mut V>
    where
        R: Ord + Eq,
    {
        let node = match self.interval.partial_cmp(range).unwrap() {
            Ordering::Greater => self.left_mut(),
            Ordering::Equal => return Some(&mut self.value),
            Ordering::Less => self.right_mut(),
        }?;

        // Prune this subtree from the search if the maximum upper bound in the
        // subtree is less than the search upper bound. If true, this subtree
        // cannot contain the search range.
        if *node.subtree_max() < range.end {
            return None;
        }

        node.get_mut(range)
    }

    pub(crate) fn value(&self) -> &V {
        &self.value
    }

    pub(crate) fn interval(&self) -> &Interval<R> {
        &self.interval
    }

    pub(crate) fn subtree_max(&self) -> &R {
        &self.subtree_max
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

    /// Remove the left child, if any.
    pub(crate) fn take_left(&mut self) -> Option<Box<Self>> {
        self.left.take()
    }

    pub(crate) fn right(&self) -> Option<&Self> {
        self.right.as_deref()
    }

    pub(crate) fn right_mut(&mut self) -> Option<&mut Box<Self>> {
        self.right.as_mut()
    }

    /// Remove the right child, if any.
    pub(crate) fn take_right(&mut self) -> Option<Box<Self>> {
        self.right.take()
    }

    /// Explode this [`Node`] into the [`Range`] and value `V` it contains.
    pub(crate) fn into_tuple(self) -> (Range<R>, V) {
        (self.interval.into_range(), self.value)
    }
}

fn height<R, V>(n: Option<&Node<R, V>>) -> u8 {
    n.map(|v| v.height()).unwrap_or_default()
}

fn update_height<R, V>(n: &mut Node<R, V>) {
    n.height = n
        .left()
        .map(|v| v.height() + 1)
        .max(n.right().map(|v| v.height() + 1))
        .unwrap_or_default()
}

fn update_subtree_max<R, V>(n: &mut Node<R, V>)
where
    R: Ord + Clone,
{
    let new_max = n
        .left()
        .map(|v| v.subtree_max())
        .max(n.right().map(|v| v.subtree_max()))
        .max(Some(n.interval().end()));

    if let Some(new_max) = new_max {
        n.subtree_max = new_max.clone();
    }
}

/// Compute the "balance factor" of the subtree rooted at `n`.
///
/// Returns the subtree height skew / magnitude, which is a positive number when
/// left heavy, and a negative number when right heavy.
fn balance<R, V>(n: &Node<R, V>) -> i8 {
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
fn rotate_left<R, V>(x: &mut Box<Node<R, V>>)
where
    R: Ord + Clone,
{
    let mut p = x.right.take().unwrap();
    std::mem::swap(x, &mut p);

    p.right = x.left.take();
    update_height(&mut p);
    update_subtree_max(&mut p);

    x.left = Some(p);
    update_height(x);
    update_subtree_max(x);
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
fn rotate_right<R, V>(y: &mut Box<Node<R, V>>)
where
    R: Ord + Clone,
{
    let mut p = y.left.take().unwrap();
    std::mem::swap(y, &mut p);

    p.left = y.right.take();
    update_height(&mut p);
    update_subtree_max(&mut p);

    y.right = Some(p);
    update_height(y);
    update_subtree_max(y);
}

/// Extracts the node holding the minimum subtree value in a descendent of
/// `root`, if any, linking the right subtree of the extracted node to in its
/// place.
fn extract_subtree_min<R, V>(root: &mut Box<Node<R, V>>) -> Option<Box<Node<R, V>>>
where
    R: Ord + Clone,
{
    // Descend left to the leaf.
    let v = match extract_subtree_min(root.left_mut()?) {
        Some(v) => Some(v),
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
            let left_right = root.left_mut().and_then(|v| v.right.take());

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
pub(super) fn remove_recurse<R, V>(
    node: &mut Option<Box<Node<R, V>>>,
    interval: &Range<R>,
) -> Option<RemoveResult<V>>
where
    R: Ord + Clone + Debug,
{
    // Remove the value (if any) and rebalance the tree.
    let remove_ret = node.as_mut().and_then(|v| {
        // Prune this subtree from the search if the maximum upper bound in the
        // subtree is less than the search upper bound. If true, this subtree
        // cannot contain the search range.
        if *v.subtree_max() < interval.end {
            return None;
        }

        let ret = v.remove(interval)?;
        rebalance_after_remove(v);
        Some(ret)
    })?;

    let v = match remove_ret {
        RemoveResult::Removed(v) => v,
        RemoveResult::ParentUnlink => {
            let node = node.take().unwrap();
            debug_assert_eq!(node.interval, *interval);

            node.value
        }
    };

    Some(RemoveResult::Removed(v))
}

fn rebalance_after_remove<R, V>(v: &mut Box<Node<R, V>>)
where
    R: Ord + Clone,
{
    // Recompute the height of the relocated node.
    update_height(v);

    // And rebalance the subtree.
    match balance(v) {
        (2..) if v.left().map(balance).unwrap_or_default() >= 0 => {
            rotate_right(v);
        }
        (2..) => {
            v.left_mut().map(rotate_left);
            rotate_right(v);
        }
        (..=-2) if v.right().map(balance).unwrap_or_default() <= 0 => {
            rotate_left(v);
        }
        (..=-2) => {
            v.right_mut().map(rotate_right);
            rotate_left(v);
        }

        #[allow(clippy::manual_range_patterns)]
        -1 | 0 | 1 => { /* balanced */ }
    }

    update_subtree_max(v);

    // Invariant: the absolute difference between tree heights ("balance
    // factor") cannot exceed 1 after removing a value.
    debug_assert!(balance(v).abs() <= 1);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn add_left<R, V>(n: &mut Node<R, V>, interval: impl Into<Interval<R>>, v: V) -> &mut Node<R, V>
    where
        R: Clone,
    {
        assert!(n.left.is_none());
        n.left = Some(Box::new(Node::new(interval.into(), v)));
        n.left_mut().unwrap()
    }

    fn add_right<R, V>(
        n: &mut Node<R, V>,
        interval: impl Into<Interval<R>>,
        v: V,
    ) -> &mut Node<R, V>
    where
        R: Clone,
    {
        assert!(n.right.is_none());
        n.right = Some(Box::new(Node::new(interval.into(), v)));
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

        let mut t = Node::new(Interval::from(2..2), 2);
        add_left(&mut t, 1..1, 1);
        let v = add_right(&mut t, 4..4, 4);
        add_left(v, 3..3, 3);
        let v = add_right(v, 6..6, 6);
        add_left(v, 5..5, 5);
        add_right(v, 7..7, 7);

        let mut t = Box::new(t);
        rotate_left(&mut t);

        assert_eq!(t.interval, 4..4);

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
        let mut t = Node::new(Interval::from(6..6), 6);
        add_right(&mut t, 7..7, 7);
        let v = add_left(&mut t, 4..4, 4);
        add_right(v, 5..5, 5);
        let v = add_left(v, 2..2, 2);
        add_right(v, 3..3, 3);
        add_left(v, 1..1, 1);

        let mut t = Box::new(t);
        rotate_right(&mut t);

        assert_eq!(t.interval, 4..4);

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
        let mut t = Box::new(Node::new(Interval::from(6..6), 6));
        add_right(&mut t, 7..7, 7);
        let v = add_left(&mut t, 4..4, 7);
        add_right(v, 5..5, 5);
        let v = add_left(v, 2..2, 2);
        add_right(v, 3..3, 3);
        add_left(v, 1..1, 1);

        for want in [1, 2, 3] {
            let n: Box<Node<_, _>> = extract_subtree_min(&mut t).unwrap();
            assert_eq!(n.value, want);
            assert!(n.right.is_none());
        }

        assert!(extract_subtree_min(&mut t).is_none());
        assert!(extract_subtree_min(&mut t).is_none());

        assert!(t.left.is_none());
        assert_eq!(t.interval, 4..4);

        let right = t.right().unwrap();
        assert_eq!(right.interval, 6..6);
        assert_eq!(right.left().unwrap().interval, 5..5);
        assert_eq!(right.right().unwrap().interval, 7..7);
    }
}
