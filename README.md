# Interval Stabbing
A data structure for finding the intervals that overlap a particular point


`IntervalTree<N, D>` is a self-balancing, generic interval tree (AVL-based) supporting fast insertion and point queries:

- **Generic parameters**
  - `N: Ord + Clone` — the interval endpoint type (e.g. `NotNan<f64>`)
  - `D` — the associated payload type

- **Core structure**
  - Each `Node<N, D>` stores one half-open interval (`Range<N>`), a payload `D`, its subtree’s maximum endpoint `max`, and AVL height for balancing.
  - Child pointers: `left: Option<Box<Node<N, D>>>` and `right: Option<Box<Node<N, D>>>`.

- **Balancing (AVL)**
  - Maintains subtree heights and `max` endpoints on every insert or rotation.
  - Single/double rotations (`rotate_left`, `rotate_right`) rebalance when the balance factor (left-height − right-height) goes outside `[-1, +1]`.

- **API**
  - `IntervalTree::new()` — create an empty tree.
  - `insert(interval: Range<N>, value: D)` — insert a new `[start, end)` → `value` in _O(log N)_ amortized time.
  - `find_point(point: &N) -> Vec<&D>` — return all values whose intervals contain `point`, in _O(log N + K)_ where _K_ is the number of matches.
  - `height()` (test-only) — retrieve the current tree height to verify balance properties.

- **Usage notes**
  - Internally counts nodes and updates `max` endpoints in each subtree to prune searches quickly.
  - Designed for mutable, dynamic interval maps where both insertion speed and query performance are critical.
