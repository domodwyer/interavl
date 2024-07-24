use std::{
    fmt::{Display, Write},
    ops::Range,
};

use proptest::prelude::*;

use crate::node::Node;

const RANGE_MAX: usize = 20;

/// Generate arbitrary (potentially invalid!) ranges with bounds from
/// [0..[`RANGE_MAX`]).
pub(crate) fn arbitrary_range() -> impl Strategy<Value = Range<usize>> {
    (0..RANGE_MAX, 0..RANGE_MAX).prop_map(|(start, end)| Range { start, end })
}

#[allow(unused)]
pub(crate) fn print_dot<T, R>(n: &Node<T, R>) -> String
where
    T: Display,
    R: Ord,
{
    let mut buf = String::new();

    writeln!(buf, "digraph {{");
    writeln!(buf, "node [shape=record];");
    recurse(n, &mut buf);
    writeln!(buf, "}}");

    buf
}

#[allow(unused)]
fn recurse<T, R, W>(n: &Node<T, R>, buf: &mut W)
where
    W: std::fmt::Write,
    T: Display,
    R: Ord,
{
    writeln!(
        buf,
        r#"{} [label="{} | {}"];"#,
        n.value(),
        n.value(),
        n.height()
    )
    .unwrap();

    for v in [n.left(), n.right()] {
        match v {
            Some(v) => {
                writeln!(buf, "{} -> {};", n.value(), v.value()).unwrap();
                recurse(v, buf);
            }
            None => {
                writeln!(buf, "null_{} [shape=point,style=invis];", n.value()).unwrap();
                writeln!(buf, "{} -> null_{} [style=invis];", n.value(), n.value()).unwrap();
            }
        };
    }
}
