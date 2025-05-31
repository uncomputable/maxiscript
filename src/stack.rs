use std::collections::{HashMap, HashSet};
use std::fmt;
use std::num::NonZero;
use std::rc::Rc;

use itertools::Itertools;

use crate::util;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum StackOp<T> {
    // Copy
    Dup,
    _2Dup,
    _3Dup,
    Over,
    _2Over,
    Tuck,
    Pick(T),
    // Move
    Swap,
    _2Swap,
    Rot,
    _2Rot,
    Roll(T),
    // // Drop
    // Drop,
    // Nip,
    // _2Drop,
    // // Alt stack
    // ToAltStack,
    // FromAltStack,
}

impl<T: fmt::Display> fmt::Display for StackOp<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StackOp::Dup => write!(f, "OP_DUP"),
            StackOp::_2Dup => write!(f, "OP_2DUP"),
            StackOp::_3Dup => write!(f, "OP_3DUP"),
            StackOp::Over => write!(f, "OP_OVER"),
            StackOp::_2Over => write!(f, "OP_2OVER"),
            StackOp::Tuck => write!(f, "OP_TUCK"),
            StackOp::Pick(x) => write!(f, "OP_PICK {x}"),
            StackOp::Swap => write!(f, "OP_SWAP"),
            StackOp::_2Swap => write!(f, "OP_2SWAP"),
            StackOp::Rot => write!(f, "OP_ROT"),
            StackOp::_2Rot => write!(f, "OP_2ROT"),
            StackOp::Roll(x) => write!(f, "OP_ROLL {x}"),
        }
    }
}

impl<T> StackOp<T> {
    pub const fn cost(&self) -> usize {
        match self {
            // FIXME: OP_PICK / OP_ROLL cost 1 + 1 + n WU, where N is the number of index bytes!
            Self::Pick(_) | Self::Roll(_) => 2,
            _ => 1,
        }
    }

    pub fn map<S, F: Fn(T) -> S>(self, f: F) -> StackOp<S> {
        match self {
            StackOp::Pick(x) => StackOp::Pick(f(x)),
            StackOp::Roll(x) => StackOp::Roll(f(x)),
            StackOp::Dup => StackOp::Dup,
            StackOp::_2Dup => StackOp::_2Dup,
            StackOp::_3Dup => StackOp::_3Dup,
            StackOp::Over => StackOp::Over,
            StackOp::_2Over => StackOp::_2Over,
            StackOp::Tuck => StackOp::Tuck,
            StackOp::Swap => StackOp::Swap,
            StackOp::_2Swap => StackOp::_2Swap,
            StackOp::Rot => StackOp::Rot,
            StackOp::_2Rot => StackOp::_2Rot,
        }
    }
}

fn script_cost<T>(script: &[StackOp<T>]) -> usize {
    script.iter().map(StackOp::cost).sum()
}

type Id = NonZero<u8>;

fn get_maps<T: Eq + std::hash::Hash>(slice: &[T]) -> (Vec<Id>, HashMap<&T, Id>, HashMap<Id, &T>) {
    assert!(slice.len() < 255, "slice must be shorter than 255 items");
    let mut forward_map: HashMap<&T, Id> = HashMap::new();
    let mut backward_map: HashMap<Id, &T> = HashMap::new();

    // First pass: build the maps
    for item in slice.iter().rev() {
        if !forward_map.contains_key(item) {
            debug_assert!(forward_map.len() < 255);
            // safety: 0 < length + 1 ≤ 255
            let index = unsafe { Id::new_unchecked(forward_map.len() as u8 + 1) };
            forward_map.insert(item, index);
            backward_map.insert(index, item);
        }
    }

    // Second pass: create the transformed vector
    let mapped_vec: Vec<Id> = slice
        .iter()
        .map(|item| *forward_map.get(item).unwrap())
        .collect();

    (mapped_vec, forward_map, backward_map)
}

fn apply_map<S: Eq + std::hash::Hash, T: Clone>(
    slice: &[S],
    map: &HashMap<&S, T>,
) -> Vec<Option<T>> {
    slice.iter().map(|id| map.get(id).cloned()).collect()
}

pub fn find_shortest_transformation<T: Clone + Ord + fmt::Debug + std::hash::Hash>(
    source: &[T],
    target: &[T],
) -> Option<Vec<StackOp<T>>> {
    find_shortest_transformation2(source, target, target)
}

// ## Assumptions
// source stack contains each item at most once
// target stack top contains each item at most once
// set of copied variables is disjoint from set of moved variables
/// Computes a minimal Bitcoin script that puts the `target` on top of the `source` stack.
///
/// After applying the script, the result stack consists of the `source` stack
/// (same list of items in arbitrary order) with the `target` (exact order) on top.
///
/// This function returns `None` if there is no transformation script.
/// This is the case if the `source` stack is missing elements that exist in the `target`.
///
/// ## Stack representation
///
/// The stack bottom is the first element and the stack top is the last element.
///
/// ## Complexity
///
/// In the worst case, the algorithm will check 7^(2n) scripts for a target of size n.
/// In other words, the algorithm takes exponential time in the target size.
pub fn find_shortest_transformation2<T: Clone + Ord + fmt::Debug + std::hash::Hash>(
    source: &[T],
    target: &[T],
    to_copy: &[T],
) -> Option<Vec<StackOp<T>>> {
    // Bail out if the source is missing elements from the target
    if target.iter().any(|x| !source.contains(x)) {
        return None;
    }
    // Bail out if target is too long
    if usize::from(u8::MAX) <= target.len() {
        return None;
    }

    let (mapped_target, map, map_back) = get_maps(target);
    let mapped_source = apply_map(source, &map);
    // Ignore items in `to_copy` that are not in `target`
    let mapped_to_copy: Vec<Id> = to_copy.iter().filter_map(|x| map.get(x)).copied().collect();
    let mapped_script =
        find_shortest_transformation_(&mapped_source, &mapped_target, &mapped_to_copy);

    let script = mapped_script
        .into_iter()
        .map(|op| op.map(|x| (*map_back.get(&x).unwrap()).clone()))
        .collect();
    Some(script)
}

fn find_shortest_transformation_(
    source: &[Option<Id>],
    target: &[Id],
    to_copy: &[Id],
) -> Vec<StackOp<Id>> {
    let initial_state = State::initial(target, to_copy);
    let mut queue_n_plus_0 = vec![initial_state];
    let mut queue_n_plus_1 = Vec::new();
    let mut script_bytes = 0;

    loop {
        // Termination is guaranteed
        debug_assert!(
            script_bytes <= target.len() * 2,
            "maximum transformation cost should be 2 times target size (using OP_PICK or OP_ROLL)"
        );
        // TODO: Allocate queue with known upper bound
        // Question: Does queue monotonically grow?
        let mut queue_n_plus_2 = Vec::new();

        for state in queue_n_plus_0 {
            debug_assert_eq!(script_bytes, script_cost(&state.script));
            debug_assert!(state.sanity_check(target));

            // println!("{:?}", state.script);
            //
            // if let &[StackOp::Over, StackOp::Swap] = state.script.as_slice() {
            //     dbg!(&state);
            // }
            // if let &[StackOp::_2Dup, StackOp::Over, StackOp::Swap] = state.script.as_slice() {
            //     dbg!(&state);
            // }

            if state.matches(source) {
                return state.script;
            }

            state.reverse_apply1(&mut queue_n_plus_1, target);
            state.reverse_apply2(&mut queue_n_plus_2, target);
        }

        queue_n_plus_0 = queue_n_plus_1;
        queue_n_plus_1 = queue_n_plus_2;
        script_bytes += 1;
    }
}

const fn unify(a: Option<Id>, b: Option<Id>) -> Option<Id> {
    match (a, b) {
        (Some(a), Some(b)) if a.get() == b.get() => Some(a),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        _ => None,
    }
}

// TODO: Consider using precomputed tree of states
#[derive(Clone, Debug, Eq, PartialEq)]
struct State {
    /// Sequence of stack operations that transforms this state
    /// to the original target state.
    ///
    /// If this state matches the source stack,
    /// then the sequence of stack operations transforms the source stack
    /// into the result stack with the target on top.
    ///
    /// As in Bitcoin Script, the first operation appears first in the sequence.
    // TODO: Consider using arrayvec
    script: Vec<StackOp<Id>>,
    /// Items on top of the stack.
    ///
    /// A state doesn't match the entire source stack.
    /// Instead, it matches the stack top in a fuzzy way.
    /// Items that are `Some(x)` must exist as `x` in the stack.
    /// Items that are `None` are free variables that match anything in the stack.
    ///
    /// The stack top is the last item.
    // TODO: Consider using arrayvec
    target: Vec<Option<Id>>,
    /// Maps indices from `self.target` to indices from the global `target`.
    ///
    /// The map is used to check if items that are produced by opcodes
    /// (such as `OP_DUP`) are on the list of copied items.
    /// Moved items are not relevant and stored as `None` in the map.
    /// Remember that copied items are disjoint from the moved items.
    ///
    /// The last item in `self.above` corresponds to the last item in `self.target`;
    /// the second-last item corresponds to the second-last item; and so on.
    ///
    /// ```text
    /// [ ~~~~~ self.target ~~~~~ ]
    ///              [ self.above ]
    ///              ↓↓↓↓↓↓↓↓↓↓↓↓↓↓
    ///              [ ~~~~~ target ~~~~~ ]
    /// ```
    ///
    /// Leading `None` items can be omitted from the vector.
    // TODO: Consider using arrayvec
    above: Vec<Option<usize>>,
    /// Set of items that were ROLLed onto the stack from within the source stack.
    ///
    /// The ROLL operation removes the item from the target.
    /// We assume that each item occurs at most once in the source stack and in the target,
    /// so by induction we will never encounter this item again for any child state.
    // TODO: Consider using FnvHashSet
    rolled: Rc<HashSet<Id>>,
}

impl State {
    pub fn initial(target: &[Id], to_copy: &[Id]) -> Self {
        Self {
            script: vec![],
            target: target.iter().copied().map(Some).collect(),
            above: target
                .iter()
                .enumerate()
                .map(|(index, item)| match to_copy.iter().contains(item) {
                    true => Some(index), // copied item
                    false => None,       // moved item
                })
                .collect(),
            rolled: Rc::new(HashSet::new()),
        }
    }

    fn sanity_check(&self, target: &[Id]) -> bool {
        // [ ~~~~~ self.target ~~~~~ ]
        //              [ self.above ]
        //              ↓↓↓↓↓↓↓↓↓↓↓↓↓↓
        //              [ ~~~~~ target ~~~~~ ]
        let local_idx_delta = match self.target.len().checked_sub(self.above.len()) {
            Some(x) => x,
            None => return false,
        };

        for (local_idx, global_idx) in self.above.iter().copied().enumerate() {
            if let (Some(global_idx), Some(x)) =
                (global_idx, self.target[local_idx_delta + local_idx])
            {
                if x != target[global_idx] {
                    return false;
                }
            }
        }

        true
    }

    /// Checks if the state matches the given `source` stack and the given `target` stack top.
    pub fn matches(&self, source: &[Option<Id>]) -> bool {
        // Any copied item has not yet been produced
        if self.above.iter().any(Option::is_some) {
            return false;
        }

        if source.len() < self.target.len() {
            return false;
        }

        let mut rolled_items = 0;
        for (rev_index, target_item) in self.target.iter().rev().copied().enumerate() {
            if target_item.is_none() {
                continue;
            }

            // Skip over rolled items.
            // Return first non-rolled item.
            let source_item = loop {
                match &source[source.len() - 1 - rev_index - rolled_items] {
                    Some(x) if self.rolled.contains(x) => rolled_items += 1,
                    x => break *x,
                }
            };

            if target_item != source_item {
                return false;
            }
        }

        true
    }

    fn make_child(
        &self,
        op: StackOp<Id>,
        target: Vec<Option<Id>>,
        above: Vec<Option<usize>>,
    ) -> Self {
        State {
            script: std::iter::once(op)
                .chain(self.script.iter().copied())
                .collect(),
            target,
            above,
            rolled: Rc::clone(&self.rolled),
        }
    }

    fn make_child_rolled(
        &self,
        op: StackOp<Id>,
        target: Vec<Option<Id>>,
        above: Vec<Option<usize>>,
        top0: Id,
    ) -> Self {
        State {
            script: std::iter::once(op)
                .chain(self.script.iter().copied())
                .collect(),
            target,
            above,
            rolled: Rc::new(
                self.rolled
                    .iter()
                    .copied()
                    .chain(std::iter::once(top0))
                    .collect(),
            ),
        }
    }

    /// Computes all states that lead to the present state via an opcode.
    ///
    /// Opcodes are applied reversely.
    ///
    /// For the present state `S`,
    /// if there is a state `T` with transition `T → S`,
    /// then include `T` in the output.
    pub fn reverse_apply1(&self, children: &mut Vec<Self>, target: &[Id]) {
        // OP_SWAP
        //
        // [α 1 0] → [α 0 1]
        // [  1 _] → [  _ 1]
        if !self.target.is_empty() {
            if let Some(new_above) = above_swap(&self.above) {
                let (bottom, [top0, top1]) = util::split_last_chunk2(&self.target);
                children.push(self.make_child(
                    StackOp::Swap,
                    bottom.iter().copied().chain([top1, top0]).collect(),
                    new_above,
                ));
            }
        }

        // OP_2SWAP
        //
        // [α 3 2 1 0] → [α 1 0 3 2]
        // [  3 2 _ 0] → [  _ 0 3 2]
        // [  3 2 _ _] → [  _ _ 3 2]
        // [  _ 2 _ _] → [  _ _ _ 2]
        if !self.target.is_empty() {
            if let Some(new_above) = above_2swap(&self.above) {
                let (bottom, [top1, top0, top3, top2]) = util::split_last_chunk2(&self.target);
                children.push(
                    self.make_child(
                        StackOp::_2Swap,
                        bottom
                            .iter()
                            .copied()
                            .chain([top3, top2, top1, top0])
                            .collect(),
                        new_above,
                    ),
                );
            }
        }

        // OP_ROT
        //
        // [α 2 1 0] → [α 1 0 2]
        // [  2 _ 0] → [  _ 0 2]
        // [  2 _ _] → [  _ _ 2]
        if !self.target.is_empty() {
            if let Some(new_above) = above_rot(&self.above) {
                let (bottom, [top1, top0, top2]) = util::split_last_chunk2(&self.target);
                children.push(self.make_child(
                    StackOp::Rot,
                    bottom.iter().copied().chain([top2, top1, top0]).collect(),
                    new_above,
                ));
            }
        }

        // OP_2ROT
        //
        // [α 5 4 3 2 1 0] → [α 3 2 1 0 5 4]
        // [  5 4 _ 2 1 0] → [  _ 2 1 0 5 4]
        // [  5 4 _ _ 1 0] → [  _ _ 1 0 5 4]
        // [  5 4 _ _ _ 0] → [  _ _ _ 0 5 4]
        // [  5 4 _ _ _ _] → [  _ _ _ _ 5 4]
        // [  _ 4 _ _ _ _] → [  _ _ _ _ _ 4]
        if !self.target.is_empty() {
            if let Some(new_above) = above_2rot(&self.above) {
                let (bottom, [top3, top2, top1, top0, top5, top4]) =
                    util::split_last_chunk2(&self.target);
                children.push(
                    self.make_child(
                        StackOp::_2Rot,
                        bottom
                            .iter()
                            .copied()
                            .chain([top5, top4, top3, top2, top1, top0])
                            .collect(),
                        new_above,
                    ),
                );
            }
        }

        // Require at least one copied item to be produced.
        // Copied items live in `Some(index)`
        let (above_bottom, idx0) = match self.above.split_last_chunk() {
            Some((above_bottom, &[Some(idx0)])) => (above_bottom, idx0),
            _ => return,
        };

        // OP_DUP
        //
        // [α 0] → [α 0 0]
        // [  0] → [  _ 0]
        let (bottom, [top0_prime, top0]) = util::split_last_chunk2(&self.target);

        if let Some(top0) = unify(top0, top0_prime) {
            if target[idx0] == top0 {
                children.push(self.make_child(
                    StackOp::Dup,
                    bottom.iter().copied().chain([Some(top0)]).collect(),
                    Vec::from(above_bottom),
                ));
            }
        }

        // OP_OVER
        //
        // [α 1 0] → [α 1 0 1]
        // [  1 0] → [  _ 0 1]
        // [  1 _] → [  _ _ 1]
        let (bottom, [top1_prime, top0, top1]) = util::split_last_chunk2(&self.target);

        if let Some(top1) = unify(top1, top1_prime) {
            if target[idx0] == top1 {
                children.push(self.make_child(
                    StackOp::Over,
                    bottom.iter().copied().chain([Some(top1), top0]).collect(),
                    Vec::from(above_bottom),
                ));
            }
        }

        // OP_TUCK
        //
        // [α 1 0] → [α 0 1 0]
        // [  1 0] → [  _ 1 0]
        // [  _ 0] → [  _ _ 0]
        let (bottom, [top0_prime, top1, top0]) = util::split_last_chunk2(&self.target);

        if let Some(top0) = unify(top0, top0_prime) {
            if target[idx0] == top0 {
                if let Some(new_above) = above_tuck(above_bottom) {
                    children.push(self.make_child(
                        StackOp::Tuck,
                        bottom.iter().copied().chain([top1, Some(top0)]).collect(),
                        new_above,
                    ));
                }
            }
        }

        // Require at least two copied items to be produced.
        let (above_bottom, idx1, idx0) = match self.above.split_last_chunk() {
            Some((above_bottom, &[Some(idx1), Some(idx0)])) => (above_bottom, idx1, idx0),
            _ => return,
        };

        // OP_2DUP
        //
        // [α 1 0] → [α 1 0 1 0]
        // [  1 0] → [  _ 0 1 0]
        // [  1 0] → [  _ _ 1 0]
        let (bottom, [top1_prime, top0_prime, top1, top0]) = util::split_last_chunk2(&self.target);

        if let (Some(top1), Some(top0)) = (unify(top1, top1_prime), unify(top0, top0_prime)) {
            if target[idx1] == top1 && target[idx0] == top0 {
                children.push(
                    self.make_child(
                        StackOp::_2Dup,
                        bottom
                            .iter()
                            .copied()
                            .chain([Some(top1), Some(top0)])
                            .collect(),
                        Vec::from(above_bottom),
                    ),
                );
            }
        }

        // OP_2OVER
        //
        // [α 3 2 1 0] → [α 3 2 1 0 3 2]
        // [  3 2 1 0] → [  _ 2 1 0 3 2]
        // [  3 2 1 0] → [  _ _ 1 0 3 2]
        // [  3 2 _ 0] → [  _ _ _ 0 3 2]
        // [  3 2 _ _] → [  _ _ _ _ 3 2]
        let (bottom, [top3_prime, top2_prime, top1, top0, top3, top2]) =
            util::split_last_chunk2(&self.target);

        if let (Some(top3), Some(top2)) = (unify(top3, top3_prime), unify(top2, top2_prime)) {
            if target[idx1] == top3 && target[idx0] == top2 {
                children.push(
                    self.make_child(
                        StackOp::_2Over,
                        bottom
                            .iter()
                            .copied()
                            .chain([Some(top3), Some(top2), top1, top0])
                            .collect(),
                        Vec::from(above_bottom),
                    ),
                );
            }
        }

        // Require at least three copied items to be produced.
        let (above_bottom, idx2, idx1, idx0) = match self.above.split_last_chunk() {
            Some((above_bottom, &[Some(idx2), Some(idx1), Some(idx0)])) => {
                (above_bottom, idx2, idx1, idx0)
            }
            _ => return,
        };

        // OP_3DUP
        //
        // [α 2 1 0] → [α 2 1 0 2 1 0]
        // [  2 1 0] → [  _ 1 0 2 1 0]
        // [  2 1 0] → [  _ _ 0 2 1 0]
        // [  2 1 0] → [  _ _ _ 2 1 0]
        let (bottom, [top2_prime, top1_prime, top0_prime, top2, top1, top0]) =
            util::split_last_chunk2(&self.target);

        if let (Some(top2), Some(top1), Some(top0)) = (
            unify(top2, top2_prime),
            unify(top1, top1_prime),
            unify(top0, top0_prime),
        ) {
            if target[idx2] == top2 && target[idx1] == top1 && target[idx0] == top0 {
                children.push(
                    self.make_child(
                        StackOp::_3Dup,
                        bottom
                            .iter()
                            .copied()
                            .chain([Some(top2), Some(top1), Some(top0)])
                            .collect(),
                        Vec::from(above_bottom),
                    ),
                );
            }
        }
    }

    pub fn reverse_apply2(&self, children: &mut Vec<Self>, target: &[Id]) {
        let (bottom, top0) = match self.target.split_last_chunk() {
            Some((bottom, &[Some(top0)])) => (bottom, top0),
            _ => return,
        };
        let (above_bottom, maybe_idx0) = match self.above.split_last_chunk() {
            Some((above_bottom, &[maybe_idx0])) => (above_bottom, maybe_idx0),
            _ => return,
        };

        // OP_PICK X
        //
        // [α X β] → [α X β X]
        if let Some(idx0) = maybe_idx0 {
            if target[idx0] == top0 {
                children.push(self.make_child(
                    StackOp::Pick(top0),
                    Vec::from(bottom),
                    Vec::from(above_bottom),
                ));
            }
        }

        // OP_ROLL X
        //
        // [α       X β] → [α       β X]
        // [α   3 2 1 0] → [α   2 1 0 3]
        // [α 4 3 2 1 0] → [α 3 2 1 0 4]
        // ...
        //
        // OP_ROLL is never used for copied items, because it is cheaper to use OP_PICK instead.
        if maybe_idx0.is_some() {
            return;
        }

        // Possibility 1
        // `top0` was ROLLed onto the stack from below the target.
        children.push(self.make_child_rolled(
            StackOp::Roll(top0),
            Vec::from(bottom),
            Vec::from(above_bottom),
            top0,
        ));

        // Possibility 2
        // `top0` was ROLLed onto the stack from within the target.
        // `top0` must come from below one of the target items.
        // `OP_ROLL n` makes sense only for `n ≥ 3`, because other opcodes are cheaper.
        //
        // [α         0] → [α         0] (OP_ROLL 0 = NOP)
        // [α       1 0] → [α       0 1] (OP_ROLL 1 = OP_SWAP)
        // [α     2 1 0] → [α     1 0 2] (OP_ROLL 2 = OP_ROT)
        let index_delta = self.target.len() - self.above.len();

        for i in 0..bottom.len().saturating_sub(3) {
            // [ ~~~~~ self.target ~~~~~ ]
            //              [ self.above ]
            let new_above = match i.checked_sub(index_delta) {
                None => Vec::new(),
                Some(j) => above_bottom[0..j]
                    .iter()
                    .copied()
                    .chain(std::iter::once(None))
                    .chain(above_bottom[j..].iter().copied())
                    .collect(),
            };
            children.push(
                self.make_child(
                    StackOp::Roll(top0),
                    bottom[0..i]
                        .iter()
                        .copied()
                        .chain(std::iter::once(Some(top0)))
                        .chain(bottom[i..].iter().copied())
                        .collect(),
                    new_above,
                ),
            );
        }
    }
}

fn above_tuck(above_bottom: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    // OP_TUCK = OP_SWAP OP_OVER
    above_swap(above_bottom)
}

fn above_swap(above: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    match &above {
        // [1 0 | ] --SWAP-> [0 1 | ]
        // 1, 0: moved item
        [] => Some(Vec::new()),
        // [1 | 0] --SWAP-> [0 | 1]
        // 1, 0: moved item
        // 1 cannot be copied item!
        [None] => Some(Vec::new()),
        [_] => None,
        _ => {
            let (before_above, &[idx0, idx1]) = above.split_last_chunk().unwrap();
            Some(before_above.iter().copied().chain([idx1, idx0]).collect())
        }
    }
}

fn above_2swap(above: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    match &above {
        // [3 2 1 0 | ] --2SWAP-> [1 0 3 2 | ]
        [] => Some(Vec::new()),
        // [3 2 1 | 0] --2SWAP-> [1 0 3 | 2]
        // 3, 2, 1, 0: moved item
        [None] => Some(Vec::new()),
        [_] => None,
        // [3 2 | 1 0] --2SWAP-> [1 0 | 3 2]
        // 3, 2, 1, 0: moved item
        [None, None] => Some(Vec::new()),
        [_, _] => None,
        // [3 | 2 1 0] --2SWAP-> [1 | 0 3 2]
        // 3, 1: moved item
        // 2, 0: unrestrained
        [x0, None, x2] => Some(vec![*x2, None, *x0]),
        [_, _, _] => None,
        _ => {
            let (before_above, &[idx1, idx0, idx3, idx2]) = above.split_last_chunk().unwrap();
            Some(
                before_above
                    .iter()
                    .copied()
                    .chain([idx3, idx2, idx1, idx0])
                    .collect(),
            )
        }
    }
}

fn above_rot(above: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    match &above {
        // [2 1 0 | ] --ROT-> [1 0 2 | ]
        [] => Some(Vec::new()),
        // [2 1 | 0] --ROT-> [1 0 | 2]
        // 2, 1, 0: moved item
        [None] => Some(Vec::new()),
        [_] => None,
        // [2 | 1 0] --ROT-> [1 | 0 2]
        // 2, 1: moved item
        // 0: unrestrained
        [idx0, None] => Some(vec![*idx0]),
        [_, _] => None,
        _ => {
            let (before_above, &[idx1, idx0, idx2]) = above.split_last_chunk().unwrap();
            Some(
                before_above
                    .iter()
                    .copied()
                    .chain([idx2, idx1, idx0])
                    .collect(),
            )
        }
    }
}

fn above_2rot(above: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    match &above {
        // [5 4 3 2 1 0 | ] --2ROT-> [3 2 1 0 5 4 | ]
        // all: moved items
        [] => Some(Vec::new()),
        // [5 4 3 2 1 | 0] --2ROT-> [3 2 1 0 5 | 4]
        // all: moved items
        [None] => Some(Vec::new()),
        [_] => None,
        // [5 4 3 2 | 1 0] --2ROT-> [3 2 1 0 | 5 4]
        // all: moved items
        [None, None] => Some(Vec::new()),
        [_, _] => None,
        // [5 4 3 | 2 1 0] --2ROT-> [3 2 1 | 0 5 4]
        // 5, 4, 3, 2, 1: moved items
        // 0: unrestrained
        [idx0, None, None] => Some(vec![*idx0]),
        [_, _, _] => None,
        // [5 4 | 3 2 1 0] --2ROT-> [3 2 | 1 0 5 4]
        // 5, 4, 3, 2: moved items
        // 1, 0: unrestrained
        [idx1, idx0, None, None] => Some(vec![*idx1, *idx0]),
        [_, _, _, _] => None,
        // [5 | 4 3 2 1 0] --2ROT-> [3 | 2 1 0 5 4]
        // 5, 3: moved items
        // 4, 2, 1, 0: unrestrained
        [idx2, idx1, idx0, None, idx4] => Some(vec![*idx4, None, *idx2, *idx1, *idx0]),
        [_, _, _, _, _] => None,
        _ => {
            let (before_above, &[idx3, idx2, idx1, idx0, idx5, idx4]) =
                above.split_last_chunk().unwrap();
            Some(
                before_above
                    .iter()
                    .copied()
                    .chain([idx5, idx4, idx3, idx2, idx1, idx0])
                    .collect(),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::{Itertools, repeat_n};
    use std::sync::{LazyLock, Mutex};

    type Script = Vec<StackOp<u8>>;

    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    pub struct ScriptFailed;

    pub fn run_script(stack: &mut Vec<u8>, script: &Script) -> Result<(), ScriptFailed> {
        for op in script {
            match op {
                // Copy
                StackOp::Dup => {
                    let [top0] = stack.last_chunk().cloned().ok_or(ScriptFailed)?;
                    stack.push(top0);
                }
                StackOp::_2Dup => {
                    let [top1, top0] = stack.last_chunk().cloned().ok_or(ScriptFailed)?;
                    stack.push(top1);
                    stack.push(top0);
                }
                StackOp::_3Dup => {
                    let [top2, top1, top0] = stack.last_chunk().cloned().ok_or(ScriptFailed)?;
                    stack.push(top2);
                    stack.push(top1);
                    stack.push(top0);
                }
                StackOp::Over => {
                    let [top1, _top0] = stack.last_chunk().ok_or(ScriptFailed)?;
                    let top1 = *top1;
                    stack.push(top1);
                }
                StackOp::_2Over => {
                    let [top3, top2, _top1, _top0] = stack.last_chunk().ok_or(ScriptFailed)?;
                    let top3 = *top3;
                    let top2 = *top2;
                    stack.push(top3);
                    stack.push(top2);
                }
                StackOp::Tuck => {
                    let top0 = stack.pop().ok_or(ScriptFailed)?;
                    let top1 = stack.pop().ok_or(ScriptFailed)?;
                    stack.push(top0);
                    stack.push(top1);
                    stack.push(top0);
                }
                StackOp::Pick(x) => {
                    if !stack.contains(x) {
                        return Err(ScriptFailed);
                    }
                    stack.push(*x)
                }
                // Move
                StackOp::Swap => {
                    if stack.len() < 2 {
                        return Err(ScriptFailed);
                    }
                    let top_n0 = stack.len() - 1;
                    let top_n1 = stack.len() - 2;
                    stack.swap(top_n0, top_n1);
                }
                StackOp::_2Swap => {
                    if stack.len() < 4 {
                        return Err(ScriptFailed);
                    }
                    let top_n0 = stack.len() - 1;
                    let top_n1 = stack.len() - 2;
                    let top_n2 = stack.len() - 3;
                    let top_n3 = stack.len() - 4;
                    stack.swap(top_n0, top_n2);
                    stack.swap(top_n1, top_n3);
                }
                StackOp::Rot => {
                    if stack.len() < 3 {
                        return Err(ScriptFailed);
                    }
                    let top_n0 = stack.len() - 1;
                    let top_n1 = stack.len() - 2;
                    let top_n2 = stack.len() - 3;
                    stack.swap(top_n2, top_n1);
                    stack.swap(top_n1, top_n0);
                }
                StackOp::_2Rot => {
                    if stack.len() < 6 {
                        return Err(ScriptFailed);
                    }
                    let top5 = stack.remove(stack.len() - 6);
                    let top4 = stack.remove(stack.len() - 5);
                    stack.push(top5);
                    stack.push(top4);
                }
                StackOp::Roll(x) => {
                    if let Some(occurrence) = stack.iter().rposition(|item| item == x) {
                        let removed_x = stack.remove(occurrence);
                        stack.push(removed_x);
                    } else {
                        return Err(ScriptFailed);
                    }
                } // Drop
                  // StackOp::Drop => {
                  //     if stack.len() < 1 {
                  //         return None;
                  //     }
                  //     let mut output = Vec::from(stack);
                  //     output.pop();
                  //     Some(output)
                  // }
                  // StackOp::Nip => {
                  //     if stack.len() < 2 {
                  //         return None;
                  //     }
                  //     // TODO: Create output stack using iterators without shifting all its elements
                  //     let mut output = Vec::from(stack);
                  //     output.remove(top_index(1));
                  //     Some(output)
                  // }
                  // StackOp::_2Drop => {
                  //     if stack.len() < 2 {
                  //         return None;
                  //     }
                  //     let mut output = Vec::from(stack);
                  //     output.pop();
                  //     output.pop();
                  //     Some(output)
                  // }
                  // // Alt Stack
                  // StackOp::ToAltStack => {}
                  // StackOp::FromAltStack => {}
            }
        }

        Ok(())
    }

    // Seems to take 10 GB of memory currently
    #[test]
    #[ignore]
    fn find_transformation_regression1() {
        let source = &[235, 154, 0, 46, 255];
        let target = &[255, 235, 154, 0, 0, 0, 0, 0, 0, 0];
        let _doesnt_run_out_of_memory =
            find_shortest_transformation(source, target).expect("there should be a transformation");
    }

    #[test]
    fn find_transformation_regression2() {
        // [0 0 1] --OVER-> [0 0 1 0] --2OVER-> [0 0 1 0 0 0]
        // [0 0 0] <-2OVER-- [0 0 _ 0] <-OVER-- [0 0 _] = [0 0 1]
        let source = &[0, 0, 1];
        let target = &[0, 0, 0];
        let script = find_shortest_transformation(source, target).unwrap();
        assert_eq!(&[StackOp::Over, StackOp::_2Over], script.as_slice());
    }

    #[test]
    fn find_transformation_regression3() {
        // [0 1 2] --ROT-> [1 2 0] --TUCK-> [1 0 2 0] --2OVER-> [1 0 2 0 1 0]
        let source = &[0, 1, 2];
        let target = &[0, 1, 0];
        let script = find_shortest_transformation(source, target).unwrap();
        assert_eq!(
            &[StackOp::Rot, StackOp::Tuck, StackOp::_2Over],
            script.as_slice()
        );
    }

    #[test]
    fn find_transformation_regression4() {
        // [0 1 0] --OVER-> [0 1 0 1] --2DUP-> [0 1 0 1 0 1] --SWAP-> [0 1 0 1 1 0]
        // [  1 0] <-OVER-- [0 1] <-2DUP-- [1 0 1] <-SWAP-- [1 1 0]
        let source = &[0, 1, 0];
        let target = &[1, 1, 0];
        let script = find_shortest_transformation(source, target).unwrap();
        assert_eq!(
            &[StackOp::_2Dup, StackOp::Over, StackOp::Swap],
            script.as_slice()
        );
    }

    #[test]
    fn find_transformation_regression5() {
        let source = &[1, 0];
        let target = &[1, 0];
        let to_copy = &[0];
        let script = find_shortest_transformation2(source, target, to_copy).unwrap();
        assert_eq!(&[StackOp::Tuck], script.as_slice());
    }

    fn all_stack_ops(source_len: u8) -> impl Iterator<Item = StackOp<u8>> + Clone {
        let target_items = 0..source_len;
        [
            StackOp::Dup,
            StackOp::_2Dup,
            StackOp::_3Dup,
            StackOp::Over,
            StackOp::_2Over,
            StackOp::Tuck,
            StackOp::Swap,
            StackOp::_2Swap,
            StackOp::Rot,
            StackOp::_2Rot,
        ]
        .into_iter()
        .chain(target_items.clone().map(StackOp::Pick))
        .chain(target_items.map(StackOp::Roll))
    }

    fn all_scripts(source_len: u8, target_len: u8) -> impl Iterator<Item = Script> {
        (1..=target_len * 2).flat_map(move |n| {
            repeat_n(all_stack_ops(source_len), usize::from(n)).multi_cartesian_product()
        })
    }

    #[test]
    fn iterator_sanity_check() {
        assert_eq!(16, all_stack_ops(3).count());
        assert_eq!(17_895_696, all_scripts(3, 3).count());
    }

    fn multiset<T: Eq + std::hash::Hash>(s: &[T]) -> HashMap<&T, usize> {
        let mut counts = HashMap::new();

        for item in s {
            *counts.entry(item).or_insert(0) += 1;
        }

        counts
    }

    fn script_is_functional_copy(source: &[u8], target: &[u8], script: &Script) -> bool {
        let mut final_stack = Vec::with_capacity(source.len() + target.len());
        final_stack.extend(source);
        let result = run_script(&mut final_stack, script);
        result.is_ok()
            && source.len() + target.len() == final_stack.len()
            && target == &final_stack[source.len()..] // match target precisely
            // && source == &final_stack[..source.len()] // match source precisely
            && multiset(&final_stack[..source.len()]) == multiset(source) // match source without respect to order
    }

    fn script_is_functional_copy2(source: &[u8], target: &[u8], script: &Script) -> bool {
        let mut final_stack = Vec::with_capacity(source.len());
        final_stack.extend(source);
        let result = run_script(&mut final_stack, script);
        result.is_ok()
            && source.len() == final_stack.len()
            && target == &final_stack[final_stack.len() - target.len()..] // match target precisely
            && multiset(&final_stack) == multiset(source) // match source without respect to order
    }

    fn script_is_shortest_copy(
        source: &[u8],
        target: &[u8],
        script: &Script,
    ) -> Result<(), Script> {
        assert!(2 <= source.len() && source.len() <= 3);
        assert!(target.len() <= source.len());

        let cost = script_cost(script);
        let script_key = (source.to_vec(), target.to_vec());

        // TODO: Consider arrayvec
        static OPTIMAL_SCRIPTS: LazyLock<Mutex<HashMap<(Vec<u8>, Vec<u8>), (Script, usize)>>> =
            LazyLock::new(|| Mutex::new(HashMap::new()));

        let mut cache = OPTIMAL_SCRIPTS.lock().unwrap();

        if !cache.contains_key(&script_key) {
            let mut best_cost = usize::MAX;
            let mut best_script = Vec::new();

            for other_script in all_scripts(source.len() as u8, target.len() as u8)
                .filter(|s| script_is_functional_copy(source, target, s))
            {
                let other_cost = script_cost(&other_script);
                if other_cost < best_cost {
                    best_cost = other_cost;
                    best_script = other_script;
                }
            }

            debug_assert!(best_cost < usize::MAX, "there should be a best script");
            cache.insert(script_key.clone(), (best_script, best_cost));
        }

        let (best_script, best_cost) = cache.get(&script_key).unwrap();
        if *best_cost < cost {
            return Err(best_script.clone());
        }

        Ok(())
    }

    fn script_is_shortest_copy2(
        source: &[u8],
        target: &[u8],
        script: &Script,
    ) -> Result<(), Script> {
        assert!(2 <= source.len() && source.len() <= 3);
        assert!(target.len() <= source.len());

        let cost = script_cost(script);
        let script_key = (source.to_vec(), target.to_vec());

        static OPTIMAL_SCRIPTS: LazyLock<Mutex<HashMap<(Vec<u8>, Vec<u8>), (Script, usize)>>> =
            LazyLock::new(|| Mutex::new(HashMap::new()));

        let mut cache = OPTIMAL_SCRIPTS.lock().unwrap();

        if !cache.contains_key(&script_key) {
            let mut best_cost = usize::MAX;
            let mut best_script = Vec::new();

            for other_script in all_scripts(source.len() as u8, target.len() as u8)
                .filter(|s| script_is_functional_copy2(source, target, s))
            {
                let other_cost = script_cost(&other_script);
                if other_cost < best_cost {
                    best_cost = other_cost;
                    best_script = other_script;
                }
            }

            debug_assert!(best_cost < usize::MAX, "there should be a best script");
            cache.insert(script_key.clone(), (best_script, best_cost));
        }

        let (best_script, best_cost) = cache.get(&script_key).unwrap();
        if *best_cost < cost {
            return Err(best_script.clone());
        }

        Ok(())
    }

    fn transformation_is_optimal(source: &[u8], target: &[u8]) {
        if let Some(script) = find_shortest_transformation(source, target) {
            if !script_is_functional_copy(source, target, &script) {
                eprintln!("Source stack: {source:?}");
                eprintln!("Target stack top: {target:?}");
                panic!("Script is not functional copy: {script:?}");
            }
            if let Err(other_script) = script_is_shortest_copy(source, target, &script) {
                eprintln!("Source stack: {source:?}");
                eprintln!("Target stack top: {target:?}");
                eprintln!("Computed script: {script:?}");
                panic!("Other script is better: {other_script:?}");
            }
        }
    }

    fn transformation_is_optimal2(source: &[u8], target: &[u8]) {
        if let Some(script) = find_shortest_transformation2(source, target, &[]) {
            if !script_is_functional_copy2(source, target, &script) {
                eprintln!("Source stack: {source:?}");
                eprintln!("Target stack top: {target:?}");
                panic!("Script is not functional copy: {script:?}");
            }
            if let Err(other_script) = script_is_shortest_copy2(source, target, &script) {
                eprintln!("Source stack: {source:?}");
                eprintln!("Target stack top: {target:?}");
                eprintln!("Computed script: {script:?}");
                panic!("Other script is better: {other_script:?}");
            }
        }
    }

    #[test]
    fn transformation_is_optimal_2_1() {
        let source = &[1, 0];
        for target in (0..2).permutations(1) {
            transformation_is_optimal(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_2_2() {
        let source = &[1, 0];
        for target in (0..2).permutations(2) {
            transformation_is_optimal(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_3_1() {
        let source = &[2, 1, 0];
        for target in (0..3).permutations(1) {
            transformation_is_optimal(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_3_2() {
        let source = &[2, 1, 0];
        for target in (0..3).permutations(2) {
            transformation_is_optimal(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_3_3() {
        let source = &[2, 1, 0];
        for target in (0..3).permutations(3) {
            transformation_is_optimal(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_3_2_mov() {
        let source = &[2, 1, 0];
        for target in (0..3).permutations(2) {
            transformation_is_optimal2(source, &target);
        }
    }

    #[test]
    fn transformation_is_optimal_3_3_mov() {
        let source = &[2, 1, 0];
        for target in (0..3).permutations(3) {
            transformation_is_optimal2(source, &target);
        }
    }
}
