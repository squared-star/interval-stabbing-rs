use ordered_float::NotNan;
use pyo3::exceptions::{PyFloatingPointError, PyIndexError};
use pyo3::prelude::*;
use pyo3::types::{PyList, PyTuple};

mod interval_tree;
use interval_tree::IntervalTree;

/// Python‐exposed QRangeStore mapping [low,high)→any Python object.
#[pyclass(mapping)]
struct RangeDict {
    tree: IntervalTree<NotNan<f64>, PyObject>,
}

#[pymethods]
impl RangeDict {
    #[new]
    fn new() -> Self {
        RangeDict {
            tree: IntervalTree::new(),
        }
    }

    /// `len(qs)` → number of stored intervals.
    fn __len__(&self) -> PyResult<usize> {
        // We don't track count separately, so count on the fly:
        // This is O(N), but Python rarely uses len() on big stores.
        fn count_nodes<N: Ord + Clone, D>(node: &Option<Box<interval_tree::Node<N, D>>>) -> usize {
            if let Some(n) = node {
                1 + count_nodes(&n.left) + count_nodes(&n.right)
            } else {
                0
            }
        }
        let cnt = count_nodes(&self.tree.root);
        Ok(cnt)
    }

    /// `qs[low, high] = value` — insert a new range.
    fn __setitem__(&mut self, key: Bound<PyTuple>, value: PyObject) -> PyResult<()> {
        // Expect a tuple (low, high)
        let (low, high) = key
            .extract::<(f64, f64)>()
            .map_err(|_| PyIndexError::new_err("Invalid Range: must be a (low, high) tuple"))?;
        if !(low < high) {
            return Err(PyIndexError::new_err("Invalid Range."));
        }
        let lo =
            NotNan::new(low).map_err(|_| PyFloatingPointError::new_err("Invalid low value."))?;
        let hi =
            NotNan::new(high).map_err(|_| PyFloatingPointError::new_err("Invalid high value."))?;
        self.tree.insert(lo..hi, value);
        Ok(())
    }

    /// `qs[key]` → list of all values whose [low,high) contains key.
    fn __getitem__(&self, key: f64, py: Python) -> PyResult<PyObject> {
        let ord = NotNan::new(key).unwrap();
        let refs = self.tree.find_point(&ord);
        if refs.is_empty() {
            return Err(PyIndexError::new_err("Not found."));
        }
        // clone references into a new Python list
        let list = PyList::new(py, refs.iter().map(|v| v.clone_ref(py)))?;
        Ok(list.into())
    }
}

/// Module initialization
#[pymodule]
fn simutil(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<RangeDict>()?;
    Ok(())
}
