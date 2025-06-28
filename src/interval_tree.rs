use std::cmp;
use std::ops::Range;

/// A node in an AVL-based interval tree, storing one interval [start,end),
/// the maximum high endpoint among itself and descendants, and balancing information.
pub struct Node<N: Ord + Clone, D> {
    pub interval: Range<N>, // Pub for python support
    pub max: N,
    pub height: i64,
    pub value: D,
    pub left: Option<Box<Node<N, D>>>,
    pub right: Option<Box<Node<N, D>>>,
}

impl<N: Ord + Clone, D> Node<N, D> {
    /// Creates a new leaf node containing the given interval and value.
    pub fn new(interval: Range<N>, value: D) -> Self {
        let max = interval.end.clone();
        Node {
            interval,
            max,
            height: 1,
            value,
            left: None,
            right: None,
        }
    }

    /// Updates the height of the current node based on its children.
    fn update_height(&mut self) {
        let lh = self.left.as_ref().map_or(0, |c| c.height);
        let rh = self.right.as_ref().map_or(0, |c| c.height);
        self.height = 1 + cmp::max(lh, rh);
    }

    /// Updates the maximum end value (`max`) for this node based on itself and its children.
    fn update_max(&mut self) {
        let mut m = self.interval.end.clone();
        if let Some(ref l) = self.left {
            if l.max > m {
                m = l.max.clone();
            }
        }
        if let Some(ref r) = self.right {
            if r.max > m {
                m = r.max.clone();
            }
        }
        self.max = m;
    }

    /// Computes the balance factor (left subtree height − right subtree height) for AVL balancing.
    fn balance_factor(&self) -> i64 {
        let lh = self.left.as_ref().map_or(0, |c| c.height);
        let rh = self.right.as_ref().map_or(0, |c| c.height);
        lh - rh
    }

    /// Performs a right rotation and returns the new root node.
    fn rotate_right(mut self: Box<Self>) -> Box<Self> {
        // y = self.left.take().unwrap()
        let mut y = self.left.take().expect("rotate_right requires left child");
        // T2 = y.right
        let t2 = y.right.take();
        // perform rotation
        y.right = Some(self);
        let mut new_root = y;
        // re‐hook the old root’s left child
        new_root.right.as_mut().unwrap().left = t2;
        // fix heights / max
        {
            let right = new_root.right.as_mut().unwrap();
            right.update_height();
            right.update_max();
        }
        new_root.update_height();
        new_root.update_max();
        new_root
    }

    /// Performs a left rotation and returns the new root node.
    fn rotate_left(mut self: Box<Self>) -> Box<Self> {
        let mut y = self.right.take().expect("rotate_left requires right child");
        let t2 = y.left.take();
        y.left = Some(self);
        let mut new_root = y;
        new_root.left.as_mut().unwrap().right = t2;
        {
            let left = new_root.left.as_mut().unwrap();
            left.update_height();
            left.update_max();
        }
        new_root.update_height();
        new_root.update_max();
        new_root
    }

    /// Rebalances the subtree rooted at this node and returns the new root.
    fn rebalance(mut self: Box<Self>) -> Box<Self> {
        self.update_height();
        self.update_max();
        let bf = self.balance_factor();
        if bf > 1 {
            if self.left.as_ref().unwrap().balance_factor() < 0 {
                let left = self.left.take().unwrap();
                self.left = Some(left.rotate_left());
            }
            return self.rotate_right();
        } else if bf < -1 {
            if self.right.as_ref().unwrap().balance_factor() > 0 {
                let right = self.right.take().unwrap();
                self.right = Some(right.rotate_right());
            }
            return self.rotate_left();
        }
        self
    }

    /// Inserts a new interval and value into the subtree rooted at this node,
    /// rebalancing as needed, and returns the new root.
    pub fn insert(mut self: Box<Self>, interval: Range<N>, value: D) -> Box<Self> {
        if interval.start <= self.interval.start {
            if let Some(left) = self.left.take() {
                self.left = Some(left.insert(interval, value));
            } else {
                self.left = Some(Box::new(Node::new(interval, value)));
            }
        } else {
            if let Some(right) = self.right.take() {
                self.right = Some(right.insert(interval, value));
            } else {
                self.right = Some(Box::new(Node::new(interval, value)));
            }
        }
        self.rebalance()
    }
}

/// A self-balancing interval tree supporting fast insertion and point queries.
pub struct IntervalTree<N: Ord + Clone, D> {
    /// Optional root node of the tree.
    pub root: Option<Box<Node<N, D>>>,
}

impl<N: Ord + Clone, D> IntervalTree<N, D> {
    /// Creates an empty interval tree.
    pub fn new() -> Self {
        IntervalTree { root: None }
    }

    /// Returns the height of the tree. Useful for testing balance properties.
    #[cfg(test)]
    pub fn height(&self) -> i64 {
        self.root.as_ref().map_or(0, |r| r.height)
    }

    /// Inserts a new interval [start, end) associated with a value into the tree.
    ///
    /// Average time complexity: **O(log N)**.
    pub fn insert(&mut self, interval: Range<N>, value: D) {
        let new_root = if let Some(r) = self.root.take() {
            r.insert(interval, value)
        } else {
            Box::new(Node::new(interval, value))
        };
        self.root = Some(new_root);
    }

    /// Finds all values whose intervals contain the given `point`.
    ///
    /// Time complexity: **O(log N + K)**, where K is the number of matches.
    ///
    /// Returns a vector of references to matching values.
    pub fn find_point(&self, point: &N) -> Vec<&D> {
        let mut out = Vec::new();
        fn go<'a, N: Ord + Clone, D>(
            node: &'a Option<Box<Node<N, D>>>,
            point: &N,
            out: &mut Vec<&'a D>,
        ) {
            if let Some(n) = node {
                // if left child might contain some intervals
                if let Some(ref l) = n.left {
                    if l.max > *point {
                        go(&n.left, point, out);
                    }
                }
                // Check current node
                if &n.interval.start <= point && point < &n.interval.end {
                    out.push(&n.value);
                }
                // if point ≥ this interval's start, right subtree may also contain matches
                if &n.interval.start <= point {
                    go(&n.right, point, out);
                }
            }
        }
        go(&self.root, point, &mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::NotNan;

    use super::IntervalTree;

    #[test]
    fn empty_tree_has_no_matches() {
        let tree: IntervalTree<i32, &str> = IntervalTree::new();
        assert!(tree.find_point(&42).is_empty());
    }

    #[test]
    fn single_interval_contains_only_its_range() {
        let mut tree = IntervalTree::new();
        tree.insert(5..10, "foo");

        // inside
        let res = tree.find_point(&7);
        assert_eq!(res, vec![&"foo"]);

        // boundary: start is inclusive
        let res = tree.find_point(&5);
        assert_eq!(res, vec![&"foo"]);

        // boundary: end is exclusive
        assert!(tree.find_point(&10).is_empty());
        assert!(tree.find_point(&4).is_empty());
    }

    #[test]
    fn overlapping_intervals_return_all_containing() {
        let mut tree = IntervalTree::new();
        tree.insert(0..5, "a");
        tree.insert(2..8, "b");
        tree.insert(5..10, "c");

        // point 3 should see a & b
        let out = tree.find_point(&3);
        assert_eq!(out.len(), 2);
        assert!(out.contains(&&"a"));
        assert!(out.contains(&&"b"));

        // point 5 should see b & c (0..5 does _not_ include 5)
        let out = tree.find_point(&5);
        assert_eq!(out.len(), 2);
        assert!(out.contains(&&"b"));
        assert!(out.contains(&&"c"));
    }

    #[test]
    fn non_overlapping_intervals_are_separate() {
        let mut tree = IntervalTree::new();
        tree.insert(0..2, "x");
        tree.insert(2..4, "y");

        assert_eq!(tree.find_point(&1), vec![&"x"]);
        assert_eq!(tree.find_point(&2), vec![&"y"]); // 2 is start of second
        assert!(tree.find_point(&4).is_empty());
    }

    #[test]
    fn random_order_inserts_still_work() {
        let mut tree = IntervalTree::new();
        let intervals = vec![
            (10..20, "ten-twenty"),
            (0..5, "zero-five"),
            (7..13, "seven-thirteen"),
            (3..8, "three-eight"),
        ];
        for (r, v) in &intervals {
            tree.insert(r.clone(), *v);
        }

        // pick a few test points
        let p_tests = vec![
            (1, vec!["zero-five"]),
            (4, vec!["zero-five", "three-eight"]),
            (7, vec!["three-eight", "seven-thirteen"]),
            (12, vec!["ten-twenty", "seven-thirteen"]),
        ];
        for (pt, expected) in p_tests {
            let got = tree.find_point(&pt);
            assert_eq!(got.len(), expected.len(), "pt = {}", pt);
            for &e in &expected {
                assert!(got.contains(&&e));
            }
        }
    }

    #[test]
    fn tree_balances_to_log_height() {
        let mut tree = IntervalTree::new();
        // insert sorted intervals to force skew
        for i in 0..128 {
            tree.insert(i..(i + 1), i);
        }
        // Height should be O(log n) instead of 128
        #[cfg(test)]
        {
            let h = tree.height();
            assert!(h < 20, "tree did not balance, height = {}", h);
        }
    }

    /// Test two fractional intervals that overlap on 2.0
    #[test]
    fn fractional_overlaps() {
        let mut tree = IntervalTree::<NotNan<f64>, &str>::new();
        tree.insert(NotNan::new(1.1).unwrap()..NotNan::new(2.2).unwrap(), "A");
        tree.insert(NotNan::new(2.0).unwrap()..NotNan::new(3.0).unwrap(), "B");

        // at 2.0 both A (1.1..2.2) and B (2.0..3.0) should match
        let got = tree.find_point(&NotNan::new(2.0).unwrap());
        assert_eq!(got.len(), 2);
        assert!(got.contains(&&"A"));
        assert!(got.contains(&&"B"));

        // at 2.2, A’s end is exclusive, so only B remains
        let got_at_2_2 = tree.find_point(&NotNan::new(2.2).unwrap());
        assert_eq!(got_at_2_2, vec![&"B"]);
    }

    /// Multiple random float intervals
    #[test]
    fn random_float_intervals() {
        let mut tree = IntervalTree::<NotNan<f64>, usize>::new();

        // Insert a few intervals
        let intervals = vec![(0.0..1.0, 0), (0.5..1.5, 1), (1.4..2.0, 2)];
        for (r, id) in intervals {
            tree.insert(
                NotNan::new(r.start).unwrap()..NotNan::new(r.end).unwrap(),
                id,
            );
        }

        // point 0.75 → in [0.0..1.0) and [0.5..1.5)
        let mut out = tree.find_point(&NotNan::new(0.75).unwrap());
        out.sort();
        assert_eq!(out, vec![&0, &1]);

        // point 1.45 → in [0.5..1.5) and [1.4..2.0)
        let mut out = tree.find_point(&NotNan::new(1.45).unwrap());
        out.sort();
        assert_eq!(out, vec![&1, &2]);

        // point 2.0 → no interval includes its exclusive end
        assert!(tree.find_point(&NotNan::new(2.0).unwrap()).is_empty());
    }
}

#[cfg(test)]
mod fuzz_tests {
    use super::*;
    use ordered_float::NotNan;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn fuzz_random_inserts_and_queries_i32() {
        let mut rng = StdRng::seed_from_u64(0xDEADBEEF);

        for _trial in 0..100 {
            let mut tree = IntervalTree::<i32, usize>::new();
            let mut intervals = Vec::new();

            // Insert random intervals
            for id in 0..100 {
                let a = rng.random_range(-1000..1000);
                let b = rng.random_range(-1000..1000);
                if a == b {
                    continue;
                } // skip degenerate
                let (start, end) = if a < b { (a, b) } else { (b, a) };
                tree.insert(start..end, id);
                intervals.push((start..end, id));
            }

            // Random point queries
            for _ in 0..100 {
                let point = rng.random_range(-1200..1200);

                // Ground truth: what values should match?
                let expected: Vec<_> = intervals
                    .iter()
                    .filter(|(r, _)| r.start <= point && point < r.end)
                    .map(|(_, v)| v)
                    .collect();

                let got = tree.find_point(&point);
                assert_eq!(
                    got.len(),
                    expected.len(),
                    "Mismatch at point {}: expected {:?}, got {:?}",
                    point,
                    expected,
                    got
                );
                for v in &expected {
                    assert!(got.contains(&v), "Missing value {} at point {}", v, point);
                }
            }
        }
    }

    #[test]
    fn fuzz_random_inserts_and_queries_f64() {
        let mut rng = StdRng::seed_from_u64(0xCAFEBABE);

        for _trial in 0..100 {
            let mut tree = IntervalTree::<NotNan<f64>, usize>::new();
            let mut intervals = Vec::new();

            // Insert random intervals
            for id in 0..100 {
                let a: f64 = rng.random_range(-1000.0..1000.0);
                let b: f64 = rng.random_range(-1000.0..1000.0);
                if (a - b).abs() < 1.0e-9 {
                    continue;
                } // skip nearly-equal
                let (start, end) = if a < b { (a, b) } else { (b, a) };
                let r = NotNan::new(start).unwrap()..NotNan::new(end).unwrap();
                tree.insert(r.clone(), id);
                intervals.push((r, id));
            }

            // Random point queries
            for _ in 0..100 {
                let point = rng.random_range(-1200.0..1200.0);
                let point = NotNan::new(point).unwrap();

                let expected: Vec<_> = intervals
                    .iter()
                    .filter(|(r, _)| r.start <= point && point < r.end)
                    .map(|(_, v)| v)
                    .collect();

                let got = tree.find_point(&point);
                assert_eq!(
                    got.len(),
                    expected.len(),
                    "Mismatch at point {:?}: expected {:?}, got {:?}",
                    point,
                    expected,
                    got
                );
                for v in &expected {
                    assert!(got.contains(&v), "Missing value {} at point {:?}", v, point);
                }
            }
        }
    }

    #[test]
    fn fuzz_degenerate_intervals_should_not_panic() {
        let mut tree = IntervalTree::<i32, &str>::new();

        // Insert some intervals where start == end (should not panic)
        tree.insert(5..5, "empty"); // meaningless but should not crash
        tree.insert(-10..-10, "also empty");

        // Queries should not panic either
        for pt in -20..20 {
            let _ = tree.find_point(&pt);
        }
    }
}
