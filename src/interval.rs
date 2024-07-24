use std::{
    cmp::Ordering,
    ops::{Range, RangeBounds},
};

/// A totally-ordered interval, convertible from and infallibly comparable to a
/// [`Range`].
///
/// An [`Interval`] is ordered by the [`Range`] lower bound, and tie-braked with
/// the upper bound.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Interval<T>(Range<T>);

impl<T> Interval<T> {
    pub(crate) fn end(&self) -> &T {
        &self.0.end
    }
}

impl<T> PartialOrd for Interval<T>
where
    T: Ord + Eq,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Interval<T>
where
    T: Ord + Eq,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other.0).unwrap()
    }
}

impl<T> PartialOrd<Range<T>> for Interval<T>
where
    T: Ord + Eq,
{
    fn partial_cmp(&self, other: &Range<T>) -> Option<Ordering> {
        // To provide ordering of an interval, the lower bound is used as the
        // primary ordering value, falling back to the upper bound when the
        // lower bounds are equal.
        Some(match self.0.start.cmp(&other.start) {
            Ordering::Equal => self.0.end.cmp(&other.end),
            v => v,
        })
    }
}

impl<T> PartialEq<Range<T>> for Interval<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Range<T>) -> bool {
        self.0.start == other.start && self.0.end == other.end
    }
}

impl<T> From<Range<T>> for Interval<T> {
    fn from(value: Range<T>) -> Self {
        Self(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::arbitrary_range;

    use super::*;

    use proptest::prelude::*;

    proptest! {
        #[test]
        fn prop_range_eq(r in any::<Range<usize>>()) {
            let interval = Interval::from(r.clone());

            // Intervals are equal with ranges.
            assert_eq!(interval, r);
            assert_eq!(interval.partial_cmp(&r).unwrap(), Ordering::Equal);

            // And other intervals.
            let other = Interval::from(r.clone());
            assert_eq!(interval, other);
            assert_eq!(interval.partial_cmp(&other).unwrap(), Ordering::Equal);
            assert_eq!(interval.cmp(&other), Ordering::Equal);
        }

        #[test]
        fn prop_range_ord(a in arbitrary_range(), b in arbitrary_range()) {
            let interval = Interval::from(a.clone());

            let got = interval.partial_cmp(&b).unwrap();

            if a.start == b.start {
                // If the start ranges are equal, then the ordering is defined
                // by the end bounds.
                assert_eq!(got, a.end.cmp(&b.end));
            } else {
                // Otherwise an Interval is ordered by the start bounds.
                assert_eq!(got, a.start.cmp(&b.start));
            }
        }
    }
}
