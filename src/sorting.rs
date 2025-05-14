use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use itertools::Itertools;
use log::error;

/// Takes the given `greater_than` relation and
/// returns a vector that is topologically sorted from smallest to largest element.
///
/// Uses Kahn's algorithm
/// <https://en.wikipedia.org/w/index.php?title=Topological_sorting&oldid=1275275815>,
/// which has `O(n)` time complexity.
pub fn topological_sort<T: Eq + Hash + Clone>(mut greater_than: HashMap<T, HashSet<T>>) -> Vec<T> {
    let mut sorted = Vec::new();

    // TODO: Further optimize
    // FIXME: Take HashMap parameter by reference?
    let keys: HashSet<_> = greater_than.keys().collect();
    let mut smallest: VecDeque<_> = greater_than
        .iter()
        .flat_map(|(key, value)| {
            value
                .is_empty()
                .then_some(key)
                .into_iter()
                .chain(value.iter().filter(|x| !keys.contains(x)))
        })
        .unique()
        .cloned()
        .collect();
    greater_than.retain(|_, values| !values.is_empty());

    while let Some(x) = smallest.pop_front() {
        for (key, value) in greater_than.iter_mut() {
            value.remove(&x);
            if value.is_empty() {
                smallest.push_back(key.clone());
            }
        }
        greater_than.retain(|_, values| !values.is_empty());
        sorted.push(x);
    }

    sorted
}

struct State {
    /// Path of nodes from smallest to greatest.
    ///
    /// ## Invariant
    ///
    /// Nodes from the path are disjoint from the nodes of the `greater_than` relation.
    path: Vec<usize>,
    /// `greater_than[i] = vec![j, k, l]`
    /// means that node `i` is greater than nodes `j`, `k` and `l`.
    ///
    /// ## Invariant
    ///
    /// All nodes must appear as key in the map.
    ///
    /// In other words, a node that appears in the value of another node
    /// must itself appear as a key in the map.
    greater_than: HashMap<usize, Vec<usize>>,
}

impl State {
    /// Check the invariants for [`State`].
    fn sanity_check(&self) -> bool {
        let is_disjoint = self
            .path
            .iter()
            .all(|node| !self.greater_than.contains_key(node));
        if !is_disjoint {
            error!("given relation is not disjoint");
            return false;
        };
        let has_all_keys = self.greater_than.values().all(|smaller_nodes| {
            smaller_nodes
                .iter()
                .all(|smaller_node| self.greater_than.contains_key(smaller_node))
        });
        if !has_all_keys {
            error!("given relation doesn't have all keys");
            return false;
        };
        true
    }

    /// Creates a state from the given `greater_than` relation.
    ///
    /// The state works in terms of node indices.
    /// The second value returned by this function maps nodes to their index
    /// (position in the vector).
    ///
    /// Due to the nature of hash maps, the index of each node is arbitrary.
    fn new<T: Eq + Hash>(greater_than: &HashMap<T, Vec<T>>) -> (Self, Vec<&T>) {
        let arbitrary_node_order = greater_than
            .values()
            .flat_map(|smaller_nodes| smaller_nodes.iter())
            .chain(greater_than.keys())
            .unique()
            .collect::<Vec<&T>>();
        let node_to_index = arbitrary_node_order
            .iter()
            .enumerate()
            .map(|(node_index, &node)| (node, node_index))
            .collect::<HashMap<&T, usize>>();
        let greater_than = greater_than
            .iter()
            .map(|(node, smaller_nodes)| {
                (
                    node_to_index[node],
                    smaller_nodes
                        .iter()
                        .map(|node| node_to_index[node])
                        .collect(),
                )
            })
            .collect::<HashMap<usize, Vec<usize>>>();
        let state = Self {
            path: Vec::new(),
            greater_than,
        };
        debug_assert!(state.sanity_check());

        (state, arbitrary_node_order)
    }

    fn step(self) -> Vec<Self> {
        debug_assert!(self.sanity_check());
        let mut output = vec![];

        for (&node, source) in &self.greater_than {
            if source.is_empty() {
                let next_incoming = self
                    .greater_than
                    .iter()
                    .filter(|(key, _value)| **key != node)
                    .map(|(key, value)| {
                        let new_value = value
                            .iter()
                            .copied()
                            .filter(|&x| x != node)
                            .collect::<Vec<usize>>();
                        (*key, new_value)
                    })
                    .collect::<HashMap<usize, Vec<usize>>>();
                let next_path = self
                    .path
                    .iter()
                    .copied()
                    .chain(std::iter::once(node))
                    .collect::<Vec<usize>>();
                let next_state = Self {
                    path: next_path,
                    greater_than: next_incoming,
                };
                debug_assert!(next_state.sanity_check());
                output.push(next_state);
            }
        }

        output
    }

    fn get_result(&self) -> Option<&[usize]> {
        match self.greater_than.is_empty() {
            true => Some(&self.path),
            false => None,
        }
    }
}

struct AllTopologicalOrders<'a, T> {
    stack: Vec<State>,
    arbitrary_node_order: Vec<&'a T>,
}

fn is_cyclic<T: Eq + Hash>(greater_than: &HashMap<T, Vec<T>>) -> bool {
    #[derive(Copy, Clone, Debug)]
    enum Task<'a, T> {
        Visit(&'a T),
        MarkFinished(&'a T),
    }

    let mut visited = HashSet::new();
    let mut finished = HashSet::new();
    let mut tasks = greater_than.keys().map(Task::Visit).collect::<Vec<_>>();

    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(node) => {
                if finished.contains(node) {
                    continue;
                }
                if visited.contains(node) {
                    return true;
                }
                visited.insert(node);
                tasks.push(Task::MarkFinished(node));
                if let Some(neighbors) = greater_than.get(node) {
                    tasks.extend(neighbors.iter().map(Task::Visit));
                }
            }
            Task::MarkFinished(node) => {
                finished.insert(node);
            }
        }
    }

    false
}

impl<'a, T: Eq + Hash> AllTopologicalOrders<'a, T> {
    fn new(greater_than: &'a HashMap<T, Vec<T>>) -> Self {
        let (initial_state, arbitrary_node_order) = State::new(greater_than);
        Self {
            stack: vec![initial_state],
            arbitrary_node_order,
        }
    }
}

impl<'a, T> Iterator for AllTopologicalOrders<'a, T> {
    type Item = Vec<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.stack.pop() {
            if let Some(ordered_indices) = state.get_result() {
                let ordered_nodes = ordered_indices
                    .iter()
                    .copied()
                    .map(|index| self.arbitrary_node_order[index])
                    .collect::<Vec<&T>>();
                return Some(ordered_nodes);
            }
            self.stack.extend(state.step());
        }

        None
    }
}

/// Creates an iterator over all topological orders of the given `greater_than` relation.
///
/// ## Acyclicity
///
/// This function requires that the given `greater_than` relation is acyclic.
///
/// ## Complexity
///
/// In the worst case, the iterator yields V! (V factorial) many orders.
/// This happens when all items in the relation are incomparable or equal.
///
/// In the best case, the iterator yields exactly 1 order.
/// This happens when each item in the relation strictly depends on the previous item.
///
/// ## Panics
///
/// This function panics if the given `greater_than` relation is cyclic.
pub fn all_topological_orders<T: Eq + Hash>(
    greater_than: &HashMap<T, Vec<T>>,
) -> impl Iterator<Item = Vec<&T>> {
    if is_cyclic(greater_than) {
        panic!("The given relation is cyclic");
    }
    AllTopologicalOrders::new(greater_than)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verify_topological_order<T: Eq + Hash + std::fmt::Debug>(
        greater_than: &HashMap<T, HashSet<T>>,
        sorted: &[T],
    ) {
        for x in greater_than.keys().chain(greater_than.values().flatten()) {
            assert!(
                sorted.contains(x),
                "sorted slice should contain `{x:?}`, but it doesn't: `{sorted:?}`"
            )
        }
        for (x, less_than_x) in greater_than {
            for y in less_than_x {
                assert!(
                    sorted.iter().position(|y1| y1 == y).unwrap()
                        < sorted.iter().position(|x1| x1 == x).unwrap(),
                    "`{y:?}` should come before `{x:?}`, but it doesn't: `{sorted:?}`"
                );
            }
        }
    }

    #[test]
    fn test_topological_sort() {
        // ε
        let empty: HashMap<i32, HashSet<i32>> = HashMap::new();
        assert_eq!(topological_sort(empty), vec![]);

        // 1
        let single = HashMap::from([(1, HashSet::<i32>::new())]);
        assert_eq!(topological_sort(single), vec![1]);

        // 1 > 2 > 3 > 4
        let chain = HashMap::from([
            (1, HashSet::from([2])),
            (2, HashSet::from([3])),
            (3, HashSet::from([4])),
        ]);
        assert_eq!(topological_sort(chain), vec![4, 3, 2, 1]);

        // 1 > 2 > 4
        // |       ^
        // V       |
        // 3 > ----/
        let diamond = HashMap::from([
            (1, HashSet::from([2, 3])),
            (2, HashSet::from([4])),
            (3, HashSet::from([4])),
        ]);
        verify_topological_order(&diamond, &topological_sort(diamond.clone()));

        // 1 > 2 > 3
        // |   |   ^
        // v   v   |
        // 4 > 5 > 6 > 7
        let complex = HashMap::from([
            (1, HashSet::from([2, 4])),
            (2, HashSet::from([3, 5])),
            (4, HashSet::from([5])),
            (5, HashSet::from([6])),
            (6, HashSet::from([3, 7])),
        ]);
        verify_topological_order(&complex, &topological_sort(complex.clone()));
    }

    #[test]
    fn test_topological_sort_cyclic() {
        let greater_than = HashMap::from([
            (1, HashSet::from([2])),
            (2, HashSet::from([3])),
            (3, HashSet::from([1])),
        ]);
        assert!(topological_sort(greater_than).is_empty());
    }

    #[test]
    fn test_topological_order() {
        // let input = [3, 8, 9, 5, 7, 2, 4, 6, 1]
        //     .into_iter()
        //     .map(|x| (x, vec![x + 1]))
        //     .chain(std::iter::once((10, vec![])))
        //     .collect::<HashMap<u8, Vec<u8>>>();
        // let expected_outputs = [input.keys().copied().sorted().collect::<Vec<u8>>()];
        // assert!(
        //     expected_outputs
        //         .into_iter()
        //         .eq(all_topological_orders(input))
        // );

        // s1 = add(x, y)
        // s2 = add(s1, z)
        // c = lookup(s2, div_table)
        // r = lookup(s2, mod_table)
        let input = HashMap::from([
            ("s1", vec![]),
            ("s2", vec!["s1"]),
            ("c", vec!["s2"]),
            ("r", vec!["s2"]),
        ]);
        let expected_orders = vec![["s1", "s2", "c", "r"], ["s1", "s2", "r", "c"]];
        let computed_orders = AllTopologicalOrders::new(&input)
            .map(|sorted| sorted.into_iter().copied().collect())
            .sorted()
            .collect::<Vec<Vec<&str>>>();
        assert_eq!(computed_orders, expected_orders,);
    }

    #[should_panic(expected = "The given relation is cyclic")]
    #[test]
    fn test_cyclic_order_direct() {
        let greater_than = HashMap::from([("x", vec!["y"]), ("y", vec!["x"])]);
        let _ = all_topological_orders(&greater_than);
    }

    #[should_panic(expected = "The given relation is cyclic")]
    #[test]
    fn test_cyclic_order_indirect() {
        let greater_than = HashMap::from([("x", vec!["y"]), ("y", vec!["z"]), ("z", vec!["x"])]);
        let _ = all_topological_orders(&greater_than);
    }
}
