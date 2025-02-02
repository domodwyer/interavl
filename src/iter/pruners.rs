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

pub(crate) struct MeetsPruner;
impl<R, V> PruningOracle<R, V> for MeetsPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.start >= *subtree_root.interval().start()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().meets(query)
    }
}

pub(crate) struct PrecedesPruner;
impl<R, V> PruningOracle<R, V> for PrecedesPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.start > *subtree_root.interval().start()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().precedes(query)
    }
}

pub(crate) struct PrecededByPruner;
impl<R, V> PruningOracle<R, V> for PrecededByPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.end < *subtree_root.subtree_max()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().preceded_by(query)
    }
}

pub(crate) struct MetByPruner;
impl<R, V> PruningOracle<R, V> for MetByPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.end <= *subtree_root.subtree_max()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().met_by(query)
    }
}

pub(crate) struct StartsPruner;
impl<R, V> PruningOracle<R, V> for StartsPruner
where
    R: Ord,
{
    fn visit_right(subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        query.start >= *subtree_root.interval().start()
    }

    fn filter_yield(n: &Node<R, V>, query: &Range<R>) -> bool {
        n.interval().starts(query)
    }
}
