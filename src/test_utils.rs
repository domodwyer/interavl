use std::{
    fmt::{Display, Write},
    ops::Range,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use proptest::prelude::*;

use crate::{iter::PruningOracle, node::Node};

const RANGE_MAX: usize = 20;

/// Generate arbitrary (potentially invalid!) ranges with bounds from
/// [0..[`RANGE_MAX`]).
pub(crate) fn arbitrary_range() -> impl Strategy<Value = Range<usize>> {
    (0..RANGE_MAX, 0..RANGE_MAX).prop_map(|(start, end)| Range { start, end })
}

#[allow(unused)]
pub(crate) fn print_dot<R, V>(n: &Node<R, V>) -> String
where
    V: Display,
    R: Display + Ord,
{
    let mut buf = String::new();

    writeln!(buf, "digraph {{");
    writeln!(buf, r#"bgcolor = "transparent";"#);
    writeln!(
        buf,
        r#"node [shape = record; style = filled; fontcolor = orange4; fillcolor = white;];"#
    );
    recurse(n, &mut buf);
    writeln!(buf, "}}");

    buf
}

#[allow(unused)]
fn recurse<V, R, W>(n: &Node<R, V>, buf: &mut W)
where
    W: std::fmt::Write,
    V: Display,
    R: Display + Ord,
{
    writeln!(
        buf,
        r#""{}" [label="{} | {} | {{ max={} | h={} }}"];"#,
        n.interval(),
        n.interval(),
        n.value(),
        n.subtree_max(),
        n.height(),
    )
    .unwrap();

    for v in [n.left(), n.right()] {
        match v {
            Some(v) => {
                writeln!(
                    buf,
                    "\"{}\" -> \"{}\" [color = \"orange1\";];",
                    n.interval(),
                    v.interval()
                )
                .unwrap();
                recurse(v, buf);
            }
            None => {
                writeln!(buf, "\"null_{}\" [shape=point,style=invis];", n.interval()).unwrap();
                writeln!(
                    buf,
                    "\"{}\" -> \"null_{}\" [style=invis];",
                    n.interval(),
                    n.interval()
                )
                .unwrap();
            }
        };
    }
}

#[derive(Debug)]
pub(crate) struct NodeFilterCount<T>(T, Arc<AtomicUsize>);

impl<T> NodeFilterCount<T> {
    pub(crate) fn new(inner: T, counter: Arc<AtomicUsize>) -> Self {
        Self(inner, counter)
    }
}

impl<R, V, T> PruningOracle<R, V> for NodeFilterCount<T>
where
    T: PruningOracle<R, V>,
{
    fn visit_right(&self, subtree_root: &Node<R, V>, query: &Range<R>) -> bool {
        self.0.visit_right(subtree_root, query)
    }

    fn filter_yield(&self, n: &Node<R, V>, query: &Range<R>) -> bool {
        self.1.fetch_add(1, Ordering::Relaxed);
        self.0.filter_yield(n, query)
    }
}

/// Linear-feedback shift register based PRNG.
///
/// Generates 65,535 unique values before cycling.
#[derive(Debug, Clone)]
pub(crate) struct Lfsr(u16, u16);

impl Lfsr {
    pub(crate) fn new(seed: u16) -> Self {
        Self(seed, seed)
    }
}

impl Lfsr {
    #[allow(clippy::should_implement_trait)]
    pub(crate) fn next(&mut self) -> u16 {
        let lsb = self.0 & 1;
        self.0 >>= 1;
        if lsb == 1 {
            self.0 ^= 0xD008;
        }
        assert_ne!(self.0, self.1);
        self.0
    }
}
