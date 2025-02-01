use std::ops::Range;

use crate::node::Node;

use super::pruning_iter::PruningOracle;

pub(crate) struct OverlapsPruner;
impl<R, V> PruningOracle<R, V> for OverlapsPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.end > *subtree_root.interval().start()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().overlaps(query)
    }
}
