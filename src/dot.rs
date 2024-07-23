use std::fmt::{Display, Write};

use crate::node::Node;

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
