use std::fmt::Write;

use crate::node::Node;

pub(crate) fn print_dot(n: &Node) -> String {
    let mut buf = String::new();

    writeln!(buf, "digraph {{");
    recurse(n, &mut buf);
    writeln!(buf, "}}");

    buf
}

fn recurse<W>(n: &Node, buf: &mut W)
where
    W: std::fmt::Write,
{
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
