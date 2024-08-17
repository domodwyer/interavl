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
