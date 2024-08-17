use std::{cmp::Ordering, fmt::Display, ops::Range};

/// A totally-ordered interval, convertible from and infallibly comparable to a
/// [`Range`].
///
/// An [`Interval`] is ordered by the [`Range`] lower bound, and tie-braked with
/// the upper bound.
#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Interval<T>(Range<T>);

impl<T> Interval<T> {
    pub(crate) fn start(&self) -> &T {
        &self.0.start
    }
    pub(crate) fn end(&self) -> &T {
        &self.0.end
    }
    pub(crate) fn as_range(&self) -> &Range<T> {
        &self.0
    }
    pub(crate) fn into_range(self) -> Range<T> {
        self.0
    }
}

impl<T> Display for Interval<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start(), self.end())
    }
}

impl<T> Interval<T>
where
    T: Ord,
{
    pub(crate) fn overlaps(&self, other: &Range<T>) -> bool {
        other.end > self.0.start && other.start < self.0.end
    }

    pub(crate) fn precedes(&self, other: &Range<T>) -> bool {
        self.0.end < other.start && self.0.start < other.start
    }

    pub(crate) fn meets(&self, other: &Range<T>) -> bool {
        self.0.end == other.start
    }

    pub(crate) fn met_by(&self, other: &Range<T>) -> bool {
        other.end == self.0.start
    }

    pub(crate) fn preceded_by(&self, other: &Range<T>) -> bool {
        other.start < self.0.start && other.end < self.0.start
    }

    pub(crate) fn starts(&self, other: &Range<T>) -> bool {
        other.start == self.0.start
    }

    pub(crate) fn finishes(&self, other: &Range<T>) -> bool {
        other.end == self.0.end
    }

    pub(crate) fn during(&self, other: &Range<T>) -> bool {
        self.0.start >= other.start && self.0.end <= other.end
    }

    pub(crate) fn contains(&self, other: &Range<T>) -> bool {
        self.0.start <= other.start && self.0.end >= other.end
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

    #[test]
    fn test_overlaps() {
        let a = 42..100;

        assert!(Interval::from(42..100).overlaps(&a));
        assert!(Interval::from(42..101).overlaps(&a));
        assert!(Interval::from(41..100).overlaps(&a));
        assert!(Interval::from(41..101).overlaps(&a));
        assert!(Interval::from(42..43).overlaps(&a));
        assert!(Interval::from(99..100).overlaps(&a));
        assert!(Interval::from(50..51).overlaps(&a));

        // Non-overlapping
        assert!(!Interval::from(41..42).overlaps(&a)); // Meets
        assert!(!Interval::from(100..101).overlaps(&a)); // Meets

        // Point overlap
        assert!(Interval::from(50..50).overlaps(&a));
        assert!(!Interval::from(40..40).overlaps(&a));
        assert!(!Interval::from(101..101).overlaps(&a));
    }

    #[test]
    fn test_precedes() {
        let a = 42..100;

        assert!(Interval::from(1..2).precedes(&a));
        assert!(Interval::from(40..41).precedes(&a));

        assert!(!Interval::from(40..42).precedes(&a)); // Meets
        assert!(!Interval::from(40..43).precedes(&a)); // Overlaps
        assert!(!Interval::from(100..101).precedes(&a)); // Preceded by
    }

    #[test]
    fn test_preceded_by() {
        let a = 42..100;

        assert!(Interval::from(101..102).preceded_by(&a));

        assert!(!Interval::from(100..420).preceded_by(&a)); // Meets
        assert!(!Interval::from(99..420).preceded_by(&a)); // Overlaps
        assert!(!Interval::from(40..41).preceded_by(&a)); // Precedes
    }

    #[test]
    fn test_meets() {
        let a = 42..100;

        assert!(Interval::from(10..42).meets(&a));

        assert!(!Interval::from(100..420).meets(&a));
        assert!(!Interval::from(101..420).meets(&a));
        assert!(!Interval::from(99..420).meets(&a));
        assert!(!Interval::from(10..43).meets(&a));
        assert!(!Interval::from(10..41).meets(&a));
    }

    #[test]
    fn test_met_by() {
        let a = 42..100;

        assert!(Interval::from(100..420).met_by(&a));

        assert!(!Interval::from(10..42).met_by(&a));
        assert!(!Interval::from(101..420).met_by(&a));
        assert!(!Interval::from(99..420).met_by(&a));
        assert!(!Interval::from(10..43).met_by(&a));
        assert!(!Interval::from(10..41).met_by(&a));
    }

    #[test]
    fn test_starts() {
        let a = 42..100;

        assert!(Interval::from(42..100).starts(&a));
        assert!(Interval::from(42..99).starts(&a));
        assert!(Interval::from(42..101).starts(&a));

        assert!(!Interval::from(41..100).starts(&a));
        assert!(!Interval::from(41..99).starts(&a));
        assert!(!Interval::from(41..101).starts(&a));
        assert!(!Interval::from(43..100).starts(&a));
        assert!(!Interval::from(43..99).starts(&a));
        assert!(!Interval::from(43..101).starts(&a));
    }

    #[test]
    fn test_finishes() {
        let a = 42..100;

        assert!(Interval::from(41..100).finishes(&a));
        assert!(Interval::from(42..100).finishes(&a));
        assert!(Interval::from(43..100).finishes(&a));

        assert!(!Interval::from(41..99).finishes(&a));
        assert!(!Interval::from(41..101).finishes(&a));
        assert!(!Interval::from(43..99).finishes(&a));
        assert!(!Interval::from(43..101).finishes(&a));
    }

    #[test]
    fn test_during() {
        let a = 42..100;

        assert!(Interval::from(42..100).during(&a));
        assert!(Interval::from(42..99).during(&a));
        assert!(Interval::from(43..100).during(&a));
        assert!(Interval::from(43..99).during(&a));

        assert!(!Interval::from(42..101).during(&a));
        assert!(!Interval::from(41..99).during(&a));
        assert!(!Interval::from(41..101).during(&a));
        assert!(!Interval::from(42..101).during(&a));
    }

    #[test]
    fn test_contains() {
        let a = 42..100;

        assert!(Interval::from(42..100).contains(&a));
        assert!(Interval::from(42..101).contains(&a));
        assert!(Interval::from(41..100).contains(&a));
        assert!(Interval::from(41..101).contains(&a));

        assert!(!Interval::from(41..99).contains(&a));
        assert!(!Interval::from(42..99).contains(&a));
        assert!(!Interval::from(43..99).contains(&a));
        assert!(!Interval::from(43..100).contains(&a));
        assert!(!Interval::from(43..101).contains(&a));
    }

    proptest! {
        #[test]
        fn prop_range_eq(r in any::<Range<usize>>()) {
            let interval = Interval::from(r.clone());

            // Reversing the conversion yields the input.
            assert_eq!(r, *interval.as_range());
            assert_eq!(r.start, interval.0.start);
            assert_eq!(r.end, *interval.end());

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


        /// Validate exclusive relations are never returned.
        #[test]
        fn prop_exclusive_interval_relations(
            interval in arbitrary_range(),
            values in prop::collection::vec(arbitrary_range(), 1..20),
        ) {
            let interval = Interval::from(interval);

            for v in &values {
                let mut truthy = 0;

                if interval.precedes(v) {
                    println!("{interval} precedes {v:?}");
                    truthy += 1;
                }

                if interval.preceded_by(v) {
                    println!("{interval} preceded_by {v:?}");
                    truthy += 1;
                }

                if interval.overlaps(v) {
                    println!("{interval} overlaps {v:?}");
                    truthy += 1;
                }

                if interval.meets(v) {
                    println!("{interval} meets {v:?}");
                    truthy += 1;
                }

                if interval.met_by(v) {
                    println!("{interval} met_by {v:?}");
                    truthy += 1;
                }

                if interval.during(v) {
                    println!("{interval} during {v:?}");
                    truthy += 1;
                }

                if interval.contains(v) {
                    println!("{interval} contains {v:?}");
                    truthy += 1;
                }

                if interval.starts(v) {
                    println!("{interval} starts {v:?}");
                    truthy += 1;
                }

                if interval.finishes(v) {
                    println!("{interval} finishes {v:?}");
                    truthy += 1;
                }

                if v.is_empty() || interval.as_range().is_empty() {
                    continue;
                }

                match truthy {
                    1 => {}
                    2 if interval.overlaps(v) && interval.during(v) => {}
                    3 if interval.overlaps(v) && interval.during(v) && interval.starts(v) => {
                        assert_eq!(*interval.start(), v.start);
                    }
                    3 if interval.overlaps(v) && interval.during(v) && interval.finishes(v) => {
                        assert_eq!(*interval.end(), v.end);
                    }
                    2 if interval.overlaps(v) && interval.contains(v) => {}
                    3 if interval.overlaps(v) && interval.contains(v) && interval.starts(v) => {
                        assert_eq!(*interval.start(), v.start);
                    }
                    3 if interval.overlaps(v) && interval.contains(v) && interval.finishes(v) => {
                        assert_eq!(*interval.end(), v.end);
                    }
                    5 if interval.overlaps(v)
                        && interval.starts(v)
                        && interval.finishes(v)
                        && interval.contains(v)
                        && interval.during(v) =>
                    {
                        assert_eq!(interval.as_range(), v)
                    }
                    _ if v.start > v.end => { /* invalid query range */ }
                    _ if interval.start() > interval.end() => { /* invalid interval */ }
                    _ => panic!("non-exclusive relation found"),
                }
            }
        }
    }
}
