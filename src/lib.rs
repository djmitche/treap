#![allow(dead_code)]

#[derive(Debug, Default)]
struct Node {
    a: u64,
    u: u64,
    /// Index of the left child, if any.
    l: Option<usize>,
    /// Index of the right child, if any.
    r: Option<usize>,
}

impl Node {
    fn new(a: u64, u: u64) -> Self {
        Self {
            a,
            u,
            ..Self::default()
        }
    }
}

/// A Treap contains pairs `(a, u)` with distinct `a`, supporting O(log(n)) lookup of pairs by
/// first coordinate (`a`) and removal of items with the highest second coordinate (`u`).
///
/// # Invariants
///
/// * The `u` value at any node is greater than both of its children.
/// * the `a` value at any node is greater than the `a` value of its left child, if any.
/// * the `a` value at any node is less than the `a` value of its right child, if any.
#[derive(Debug, Default)]
pub struct Treap {
    /// Index of the root node, if any.
    root: Option<usize>,
    /// All nodes in the tree.
    nodes: Vec<Node>,
}

impl Treap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the number of pairs in the Treap.
    pub fn len(&self) -> usize {
        fn len(nodes: &[Node], idx: Option<usize>) -> usize {
            let Some(idx) = idx else {
                return 0;
            };
            let node = &nodes[idx];
            1 + len(nodes, node.l) + len(nodes, node.r)
        }
        len(&self.nodes, self.root)
    }

    /// Insert `(a, u)` into the Treap. No change occurs if any other pair `(a, _)` is in the
    /// Treap (O(log(n))).
    pub fn insert(&mut self, a: u64, u: u64) {
        fn insert(nodes: &mut Vec<Node>, idx: Option<usize>, a: u64, u: u64) -> usize {
            let Some(idx) = idx else {
                let idx = nodes.len();
                nodes.push(Node::new(a, u));
                return idx;
            };
            match a.cmp(&nodes[idx].a) {
                std::cmp::Ordering::Less => {
                    let l_idx = insert(nodes, nodes[idx].l, a, u);
                    // Rebalance for u on the left.
                    let n = &nodes[idx];
                    let l = &nodes[l_idx];
                    if n.u < l.u {
                        // Rotate:
                        //
                        //     n            l
                        //    / \          / \
                        //   l   c  --->  a   n
                        //  / \              / \
                        // a   b            b   c
                        nodes[idx].l = l.r;
                        nodes[l_idx].r = Some(idx);
                        l_idx
                    } else {
                        nodes[idx].l = Some(l_idx);
                        idx
                    }
                }
                std::cmp::Ordering::Equal => idx,
                std::cmp::Ordering::Greater => {
                    let r_idx = insert(nodes, nodes[idx].r, a, u);
                    // Rebalance for u on the right.
                    let n = &nodes[idx];
                    let r = &nodes[r_idx];
                    if n.u < r.u {
                        // Rotate:
                        //
                        //     n            r
                        //    / \          / \
                        //   a   r  --->  n   c
                        //      / \      / \
                        //     b   c    a   b
                        nodes[idx].r = r.l;
                        nodes[r_idx].l = Some(idx);
                        r_idx
                    } else {
                        nodes[idx].r = Some(r_idx);
                        idx
                    }
                }
            }
        }
        self.root = Some(insert(&mut self.nodes, self.root, a, u));
    }

    /// Delete the node with first coordinate `a` from the Treap (O(log(n))).
    pub fn delete(&mut self, a: u64) {
        /// Return the index of the root of a subtree containing all children of the given node,
        /// but not the node itself.
        fn delete(nodes: &mut [Node], idx: usize) -> Option<usize> {
            let n = &nodes[idx];
            match (n.l, n.r) {
                (None, None) => None,
                (Some(l), None) => Some(l),
                (None, Some(r)) => Some(r),
                (Some(l), Some(r)) => {
                    // Choose one of l or r to be the new root; then the opposite
                    // beomes one of its children. The other child is the tree resulting
                    // from deleting the new root.
                    if nodes[l].u > nodes[r].u {
                        // l is the new root, and r will be its right child.
                        let new_child = delete(nodes, l);
                        nodes[l].l = new_child;
                        nodes[l].r = Some(r);
                        Some(l)
                    } else {
                        // r is the new root, and l will be its left child
                        let new_child = delete(nodes, r);
                        nodes[r].l = Some(l);
                        nodes[r].r = new_child;
                        Some(r)
                    }
                }
            }
        }

        /// Find the node with the given `a` in the given subtree and delete it, returning the new
        /// subtree.
        fn find_and_delete(nodes: &mut [Node], idx: Option<usize>, a: u64) -> Option<usize> {
            let Some(idx) = idx else {
                return None;
            };
            // TODO: keep a free list and add the deleted node to it
            match a.cmp(&nodes[idx].a) {
                std::cmp::Ordering::Less => {
                    nodes[idx].l = find_and_delete(nodes, nodes[idx].l, a);
                    Some(idx)
                }
                std::cmp::Ordering::Equal => delete(nodes, idx),
                std::cmp::Ordering::Greater => {
                    nodes[idx].r = find_and_delete(nodes, nodes[idx].r, a);
                    Some(idx)
                }
            }
        }

        self.root = find_and_delete(&mut self.nodes, self.root, a);
    }

    /// Find a pair with the given `a`, and return its `u`, if any (O(log n)).
    pub fn lookup(&self, a: u64) -> Option<u64> {
        fn lookup(nodes: &[Node], idx: Option<usize>, a: u64) -> Option<u64> {
            let Some(idx) = idx else {
                return None;
            };
            match a.cmp(&nodes[idx].a) {
                std::cmp::Ordering::Less => lookup(nodes, nodes[idx].l, a),
                std::cmp::Ordering::Equal => Some(nodes[idx].u),
                std::cmp::Ordering::Greater => lookup(nodes, nodes[idx].r, a),
            }
        }
        lookup(&self.nodes, self.root, a)
    }

    /// Get the maximum value of `u` in any pair (O(1)).
    pub fn peek_max_u(&self) -> Option<(u64, u64)> {
        self.root.map(|idx| (self.nodes[idx].a, self.nodes[idx].u))
    }

    /// Check invariants.
    fn check(&self) {
        fn check(nodes: &[Node], idx: Option<usize>) {
            let Some(idx) = idx else {
                return;
            };
            let n = &nodes[idx];
            if let Some(l_idx) = n.l {
                let ln = &nodes[l_idx];
                assert!(ln.a < n.a);
                assert!(ln.u <= n.u);
            }
            if let Some(r_idx) = n.r {
                let rn = &nodes[r_idx];
                assert!(rn.a > n.a);
                assert!(rn.u <= n.u);
            }
            check(nodes, nodes[idx].l);
            check(nodes, nodes[idx].r);
        }
        assert_eq!(self.len(), self.nodes.len());
        check(&self.nodes, self.root)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_treap() {
        let mut t = Treap::new();
        assert_eq!(t.len(), 0);
        assert_eq!(t.lookup(10), None);
        assert_eq!(t.peek_max_u(), None);
        t.delete(99);
        assert_eq!(t.len(), 0);
    }

    fn build_and_check_no_dup(vals: &[(u64, u64)]) -> Treap {
        let mut t = Treap::new();
        for (a, u) in vals {
            t.insert(*a, *u);
            dbg!(&t).check();
        }
        // Re-insert to verify nothing bad happens
        for (a, u) in vals {
            t.insert(*a, *u);
        }
        dbg!(&t).check();
        assert_eq!(t.len(), vals.len());
        for (a, u) in vals {
            assert_eq!(t.lookup(*a), Some(*u));
        }
        t
    }

    #[test]
    fn small_treap() {
        build_and_check_no_dup(&[(1, 10), (2, 20), (3, 15)]);
    }

    #[test]
    fn sequential_treap() {
        build_and_check_no_dup(&[(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)]);
    }

    #[test]
    fn reverse_treap() {
        build_and_check_no_dup(&[(6, 10), (5, 20), (4, 30), (3, 40), (2, 50), (1, 60)]);
    }

    #[test]
    fn mixed_treap() {
        let mut t = build_and_check_no_dup(&[(3, 10), (9, 80), (2, 30), (1, 40), (8, 50), (4, 60)]);
        assert_eq!(t.peek_max_u(), Some((9, 80)));

        t.delete(9);
        assert_eq!(t.lookup(9), None);
        assert_eq!(t.peek_max_u(), Some((4, 60)));

        t.delete(3);
        assert_eq!(t.lookup(3), None);
        assert_eq!(t.peek_max_u(), Some((4, 60)));

        t.delete(8);
        assert_eq!(t.lookup(8), None);
        assert_eq!(t.peek_max_u(), Some((4, 60)));
    }
}
