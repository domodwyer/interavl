use crate::node::Node;

#[derive(Debug, Default)]
pub(crate) struct IntervalTree(Option<Node>);

impl IntervalTree {
    pub fn insert(&mut self, value: usize) {
        match self.0 {
            Some(ref mut v) => v.insert(value),
            None => self.0 = Some(Node::new(value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::dot::print_dot;

    use super::*;

    #[test]
    fn test_simple() {
        let mut t = IntervalTree::default();

        t.insert(42);
        t.insert(1);
        t.insert(13);
        t.insert(12);
        t.insert(142);
        t.insert(25);
        t.insert(15);

        let dot = print_dot(&t.0.unwrap());

        assert_eq!(dot, "digraph {\n42 -> 1;\nnull_1 [shape=point,style=invis];\n1 -> null_1 [style=invis];\n1 -> 13;\n13 -> 12;\nnull_12 [shape=point,style=invis];\n12 -> null_12 [style=invis];\nnull_12 [shape=point,style=invis];\n12 -> null_12 [style=invis];\n13 -> 25;\n25 -> 15;\nnull_15 [shape=point,style=invis];\n15 -> null_15 [style=invis];\nnull_15 [shape=point,style=invis];\n15 -> null_15 [style=invis];\nnull_25 [shape=point,style=invis];\n25 -> null_25 [style=invis];\n42 -> 142;\nnull_142 [shape=point,style=invis];\n142 -> null_142 [style=invis];\nnull_142 [shape=point,style=invis];\n142 -> null_142 [style=invis];\n}\n");
    }
}
