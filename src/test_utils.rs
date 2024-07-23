use std::ops::Range;

use proptest::prelude::*;

const RANGE_MAX: usize = 20;

/// Generate arbitrary (potentially invalid!) ranges with bounds from
/// [0..[`RANGE_MAX`]).
pub(crate) fn arbitrary_range() -> impl Strategy<Value = Range<usize>> {
    (0..RANGE_MAX, 0..RANGE_MAX).prop_map(|(start, end)| Range { start, end })
}
