use crate::util;
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt;
// the top of the stack is the last element of the slice

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
    // // Move
    // Rot,
    // Swap,
    // Roll(T),
    // _2Rot,
    // _2Swap,
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
        }
    }
}

impl<T> StackOp<T> {
    pub const fn cost(&self) -> usize {
        match self {
            Self::Pick(_) => 2,
            _ => 1,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ScriptFailed;

// #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
// enum Var<T> {
//     Some(T),
//     Free,
// }
//
// impl<T> Var<T> {
//     pub const fn is_free(&self) -> bool {
//         matches!(self, Var::Free)
//     }
// }
//
// impl<T: Eq> Var<T> {
//     pub fn unify(&self, other: &Self) -> bool {
//         match (self, other) {
//             (Self::Some(x), Self::Some(y)) => x == y,
//             _ => true,
//         }
//     }
// }

fn unify<'a, T: Eq>(a: Option<&'a T>, b: Option<&'a T>) -> Option<&'a T> {
    match (a, b) {
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        _ => None,
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum Above<T> {
    Push(T),
    Tuck,
}

impl<T: Clone + Eq + fmt::Debug> StackOp<T> {
    pub fn apply<I: Iterator<Item = StackOp<T>>>(
        stack: &mut Vec<T>,
        script: I,
    ) -> Result<(), ScriptFailed> {
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
                    let top1 = top1.clone();
                    stack.push(top1);
                }
                StackOp::_2Over => {
                    let [top3, top2, _top1, _top0] = stack.last_chunk().ok_or(ScriptFailed)?;
                    let top3 = top3.clone();
                    let top2 = top2.clone();
                    stack.push(top3);
                    stack.push(top2);
                }
                StackOp::Tuck => {
                    let top0 = stack.pop().ok_or(ScriptFailed)?;
                    let top1 = stack.pop().ok_or(ScriptFailed)?;
                    stack.push(top0.clone());
                    stack.push(top1);
                    stack.push(top0);
                }
                StackOp::Pick(top_n) => {
                    if !stack.contains(&top_n) {
                        return Err(ScriptFailed);
                    }
                    stack.push(top_n)
                } // // Move
                  // StackOp::Rot => {
                  //     if stack.len() < 3 {
                  //         return None;
                  //     }
                  //     let mut output = Vec::from(stack);
                  //     output.swap(top_index(2), top_index(1));
                  //     output.swap(top_index(1), top_index(0));
                  //     Some(output)
                  // }
                  // StackOp::Swap => {
                  //     if stack.len() < 2 {
                  //         return None;
                  //     }
                  //     let mut output = Vec::from(stack);
                  //     output.swap(top_index(1), top_index(0));
                  //     Some(output)
                  // }
                  // StackOp::Roll(n) => {
                  //     // We treat value `n` as off the stack!
                  //     // This is different from Bitcoin Core or the Bitcoin Wiki!
                  //     if stack.len() < n {
                  //         return None;
                  //     }
                  //     // TODO: Create output stack using iterators without shifting all its elements
                  //     let mut output = Vec::from(stack);
                  //     let top_n = output.remove(top_index(n));
                  //     output.push(top_n);
                  //     Some(output)
                  // }
                  // StackOp::_2Rot => {
                  //     if stack.len() < 6 {
                  //         return None;
                  //     }
                  //     // TODO: Create output stack using iterators without shifting all its elements
                  //     let mut output = Vec::from(stack);
                  //     let top5 = output.remove(top_index(5));
                  //     let top4 = output.remove(top_index(5));
                  //     output.push(top5);
                  //     output.push(top4);
                  //     Some(output)
                  // }
                  // StackOp::_2Swap => {
                  //     if stack.len() < 4 {
                  //         return None;
                  //     }
                  //     let mut output = Vec::from(stack);
                  //     output.swap(top_index(3), top_index(1));
                  //     output.swap(top_index(2), top_index(0));
                  //     Some(output)
                  // }
                  // // Drop
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

    /// If the target stack top is reached via the given opcode,
    /// this function returns the necessary source stack top.
    ///
    /// This function returns `None` is the target stack top is unreachable.
    pub fn reverse_apply(
        target: &[Option<T>],
        above: &[Above<T>],
    ) -> Vec<(Self, Vec<Option<T>>, Vec<Above<T>>)> {
        let mut sources = Vec::new();

        // OP_DUP
        //
        // [.. 0] → [.. 0 0]
        // [   0] → [   _ 0]
        let (bottom, [top0_prime, top0]) = util::split_last_chunk2(target);

        if let Some(top0) = unify(top0, top0_prime) {
            sources.push((
                Self::Dup,
                bottom.iter().cloned().chain([Some(top0.clone())]).collect(),
                [Above::Push(top0.clone())]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        // OP_2DUP
        //
        // [.. 1 0] → [.. 1 0 1 0]
        // [   1 0] → [   _ 0 1 0]
        // [   1 0] → [   _ _ 1 0]
        let (bottom, [top1_prime, top0_prime, top1, top0]) = util::split_last_chunk2(target);

        if let (Some(top1), Some(top0)) = (unify(top1, top1_prime), unify(top0, top0_prime)) {
            sources.push((
                Self::_2Dup,
                bottom
                    .iter()
                    .cloned()
                    .chain([Some(top1.clone()), Some(top0.clone())])
                    .collect(),
                [Above::Push(top1.clone()), Above::Push(top0.clone())]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        // OP_3DUP
        //
        // [.. 2 1 0] → [.. 2 1 0 2 1 0]
        // [   2 1 0] → [   _ 1 0 2 1 0]
        // [   2 1 0] → [   _ _ 0 2 1 0]
        // [   2 1 0] → [   _ _ _ 2 1 0]
        let (bottom, [top2_prime, top1_prime, top0_prime, top2, top1, top0]) =
            util::split_last_chunk2(target);

        if let (Some(top2), Some(top1), Some(top0)) = (
            unify(top2, top2_prime),
            unify(top1, top1_prime),
            unify(top0, top0_prime),
        ) {
            sources.push((
                Self::_3Dup,
                bottom
                    .iter()
                    .cloned()
                    .chain([Some(top2.clone()), Some(top1.clone()), Some(top0.clone())])
                    .collect(),
                [
                    Above::Push(top2.clone()),
                    Above::Push(top1.clone()),
                    Above::Push(top0.clone()),
                ]
                .into_iter()
                .chain(above.iter().cloned())
                .collect(),
            ));
        }

        // OP_OVER
        //
        // [.. 1 0] → [.. 1 0 1]
        // [   1 0] → [   _ 0 1]
        // [   1 _] → [   _ _ 1]
        let (bottom, [top1_prime, top0, top1]) = util::split_last_chunk2(target);

        if let Some(top1) = unify(top1, top1_prime) {
            sources.push((
                Self::Over,
                bottom
                    .iter()
                    .cloned()
                    .chain([Some(top1.clone()), top0.cloned()])
                    .collect(),
                [Above::Push(top1.clone())]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        // OP_2OVER
        //
        // [.. 3 2 1 0] → [.. 3 2 1 0 3 2]
        // [   3 2 1 0] → [   _ 2 1 0 3 2]
        // [   3 2 1 0] → [   _ _ 1 0 3 2]
        // [   3 2 _ 0] → [   _ _ _ 0 3 2]
        // [   3 2 _ _] → [   _ _ _ _ 3 2]
        let (bottom, [top3_prime, top2_prime, top1, top0, top3, top2]) =
            util::split_last_chunk2(target);

        if let (Some(top3), Some(top2)) = (unify(top3, top3_prime), unify(top2, top2_prime)) {
            sources.push((
                Self::_2Over,
                bottom
                    .iter()
                    .cloned()
                    .chain([
                        Some(top3.clone()),
                        Some(top2.clone()),
                        top1.cloned(),
                        top0.cloned(),
                    ])
                    .collect(),
                [Above::Push(top3.clone()), Above::Push(top2.clone())]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        // OP_TUCK
        //
        // [.. 1 0] → [.. 0 1 0]
        // [   1 0] → [   _ 1 0]
        // [   _ 0] → [   _ _ 0]
        let (bottom, [top0_prime, top1, top0]) = util::split_last_chunk2(target);

        if let Some(top0) = unify(top0, top0_prime) {
            sources.push((
                Self::Tuck,
                bottom
                    .iter()
                    .cloned()
                    .chain([top1.cloned(), Some(top0.clone())])
                    .collect(),
                [Above::Tuck]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        // OP_PICK X
        //
        // [.. X ..] → [.. X .. X]
        if let Some((bottom, [Some(top0)])) = target.split_last_chunk() {
            sources.push((
                Self::Pick(top0.clone()),
                Vec::from(bottom),
                [Above::Push(top0.clone())]
                    .into_iter()
                    .chain(above.iter().cloned())
                    .collect(),
            ));
        }

        sources
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State<T> {
    pub script_bytes: usize,
    pub reversed_script: Vec<StackOp<T>>,
    target: Vec<Option<T>>,
    above: Vec<Above<T>>,
}

impl<T> State<T> {
    pub fn new(target: Vec<T>) -> Self {
        Self {
            script_bytes: 0,
            reversed_script: vec![],
            target: target.into_iter().map(Some).collect(),
            above: Vec::new(),
        }
    }
}

impl<T: Clone + Eq> State<T> {
    pub fn matches(&self, source: &[T], target: &[T]) -> bool {
        let mut above = Vec::with_capacity(target.len());
        for op in &self.above {
            match op {
                Above::Push(x) => above.push(x),
                Above::Tuck => {
                    if above.len() < 2 {
                        return false;
                    }
                    let last = *above.last().unwrap();
                    let i = above.len() - 1;
                    let j = above.len() - 2;
                    above.swap(i, j);
                    above.push(last);
                }
            }
        }
        if target.len() != above.len() || (0..target.len()).any(|i| &target[i] != above[i]) {
            return false;
        }

        self.target.len() <= source.len()
            && self.target.iter().enumerate().all(|(index, x)| match x {
                Some(x) => &source[source.len() - self.target.len() + index] == x,
                None => true,
            })
    }
}

impl<T: Ord> PartialOrd for State<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.cmp(self)) // reversed to turn max heap into min heap
    }
}

impl<T: Ord> Ord for State<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.script_bytes.cmp(&other.script_bytes)
    }
}

/// Computes a minimal Bitcoin script that manipulates the `source_stack`
/// such that the items from the `target` are on the top of the stack.
///
/// If a value exists in the `target` but not in the `source_stack`,
/// then no Bitcoin script can push this value onto the stack top.
/// In this case, this function returns `None`.
///
/// ## Complexity
///
/// In the worst case, the algorithm will check 7^(2n) scripts for a target of size n.
/// In other words, the algorithm takes exponential time in the target size.
pub fn find_shortest_transformation<T: Clone + Ord + std::fmt::Debug + std::hash::Hash>(
    source_stack: &[T],
    target: &[T],
) -> Option<State<T>> {
    if target.iter().any(|name| !source_stack.contains(name)) {
        return None;
    }

    let initial_state = State::new(target.to_vec());
    let mut priority_queue = BinaryHeap::from([initial_state]);

    // Each reverse application of opcode reduces target by 1
    // Termination is guaranteed
    while let Some(state) = priority_queue.pop() {
        debug_assert!(
            state.script_bytes <= target.len() * 2,
            "maximum transformation cost should be 2 times target size (using OP_PICK)"
        );

        if target.len() < state.above.len() {
            continue;
        }

        if 2 * target.len() < state.script_bytes {
            panic!("Cost is too high");
        }

        if state.matches(source_stack, target) {
            return Some(state);
        }

        for (next_op, next_target, next_above) in
            StackOp::reverse_apply(&state.target, &state.above)
        {
            let delta_bytes = match next_op {
                StackOp::Pick(_) => 2,
                _ => 1,
            };
            priority_queue.push(State {
                script_bytes: state.script_bytes + delta_bytes,
                reversed_script: state
                    .reversed_script
                    .iter()
                    .cloned()
                    .chain(std::iter::once(next_op))
                    .collect(),
                target: next_target,
                above: next_above,
            })
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::{repeat_n, Itertools};
    use std::collections::HashMap;

    type Script = Vec<StackOp<usize>>;

    #[test]
    fn find_manipulation_out_of_memory_regression() {
        let source = &[235, 154, 0, 46, 255];
        let target = &[255, 235, 154, 0, 0, 0, 0, 0, 0, 0];
        find_shortest_transformation(source, target).expect("there should be a transformation");
    }

    #[test]
    fn find_transformation_regression1() {
        // [0 0 1] --OVER-> [0 0 1 0] --2OVER-> [0 0 1 0 0 0]
        // [0 0 0] <-2OVER-- [0 0 _ 0] <-OVER-- [0 0 _] = [0 0 1]
        let source = &[0, 0, 1];
        let target = &[0, 0, 0];
        let script = find_shortest_transformation(source, target)
            .expect("there should be a transformation")
            .reversed_script;
        assert_eq!(&[StackOp::_2Over, StackOp::Over], script.as_slice())
    }

    #[test]
    fn find_transformation_regression2() {
        // [0 1 2] --OVER-> [0 1 2 1] --Pick(0)-> [0 1 2 1 0] --TUCK-> [0 1 2 0 1 0]
        // [0 1 0] <-TUCK-- [1 0] <-Pick(0)-- [1] <-OVER-- [1 _]
        let source = &[0, 1, 2];
        let target = &[0, 1, 0];
        let script = find_shortest_transformation(source, target)
            .expect("there should be a transformation")
            .reversed_script;
        assert_eq!(
            &[StackOp::Tuck, StackOp::Pick(0), StackOp::Over],
            script.as_slice()
        )
    }

    fn stack_ops(target: &[usize]) -> impl Iterator<Item = StackOp<usize>> + Clone + '_ {
        [
            StackOp::Dup,
            StackOp::_2Dup,
            StackOp::_3Dup,
            StackOp::Over,
            StackOp::_2Over,
            StackOp::Tuck,
        ]
        .into_iter()
        .chain(target.iter().copied().map(|x| StackOp::Pick(x)))
    }

    fn all_copy_scripts(target: &[usize]) -> impl Iterator<Item = Script> + '_ {
        repeat_n(stack_ops(target), target.len())
            .flatten()
            .powerset()
    }

    // type Stack = Vec<usize>;
    //
    // static BEST_SCRIPT: LazyLock<HashMap<Stack, HashMap<Stack, Script>>> = LazyLock::new(|| {
    //     let mut outer = HashMap::new();
    //
    //     for source in repeat_n(0..3, 3).multi_cartesian_product() {
    //         let mut inner = HashMap::new();
    //
    //         for target in repeat_n(0..3, 3).multi_cartesian_product() {
    //             let mut best_script = Vec::default();
    //             let mut best_cost = usize::MAX;
    //
    //             for script in all_copy_scripts(&[0, 1, 2]) {
    //                 if script_is_functional_copy(&source, &target, &script) && script_cost(&script) < best_cost {
    //                     best_cost = script_cost(&script);
    //                     best_script = script;
    //                 }
    //             }
    //
    //             inner.insert(target.clone(), best_script);
    //         }
    //
    //         outer.insert(source.clone(), inner);
    //     }
    //
    //     outer
    // });

    fn script_cost(script: &Script) -> usize {
        script.iter().map(StackOp::cost).sum()
    }

    fn multiset<T: std::hash::Hash + Eq>(slice: &[T]) -> HashMap<&T, usize> {
        let mut map = HashMap::new();
        for element in slice {
            *map.entry(element).or_default() += 1;
        }
        map
    }

    fn script_is_functional_copy(source: &[usize], target: &[usize], script: &Script) -> bool {
        let mut final_stack = Vec::from(source);
        let result = StackOp::apply(&mut final_stack, script.iter().copied());
        result.is_ok()
            && source.len() + target.len() == final_stack.len()
            && source == &final_stack[..source.len()]
            && target == &final_stack[source.len()..]
    }

    // TODO: Cache optimal scripts
    fn script_is_optimal_copy(
        source: &[usize],
        target: &[usize],
        script: &Script,
    ) -> Result<(), Script> {
        // let best_script = BEST_SCRIPT.get(source).unwrap().get(target).unwrap();
        // if script_cost(&best_script) < script_cost(script) {
        //     return Err(best_script.clone());
        // }

        for other_script in all_copy_scripts(target) {
            if script_cost(&other_script) < script_cost(script) {
                if script_is_functional_copy(source, target, &other_script) {
                    return Err(other_script);
                }
            }
        }

        Ok(())
    }

    fn transformation_is_optimal<const N: usize>() {
        for source in repeat_n(0..N, N).multi_cartesian_product() {
            for target in repeat_n(0..N, N).multi_cartesian_product() {
                if let Some(state) = find_shortest_transformation(&source, &target) {
                    let script: Vec<_> = state.reversed_script.into_iter().rev().collect();
                    if !script_is_functional_copy(&source, &target, &script) {
                        eprintln!("Source stack: {source:?}");
                        eprintln!("Target stack top: {target:?}");
                        panic!("Script is not functional copy: {script:?}");
                    }
                    if let Err(other_script) = script_is_optimal_copy(&source, &target, &script) {
                        eprintln!("Source stack: {source:?}");
                        eprintln!("Target stack top: {target:?}");
                        eprintln!("Computed script: {script:?}");
                        panic!("Other script is better: {other_script:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn transformation_is_optimal3() {
        // transformation_is_optimal::<3>();

        for top0 in 0..3 {
            for top1 in 0..3 {
                for top2 in 0..3 {
                    let source = &[top2, top1, top0];

                    for target0 in 0..3 {
                        for target1 in 0..3 {
                            for target2 in 0..3 {
                                let target = &[target2, target1, target0];

                                if let Some(state) = find_shortest_transformation(source, target) {
                                    let script: Vec<_> =
                                        state.reversed_script.into_iter().rev().collect();
                                    if !script_is_functional_copy(source, target, &script) {
                                        eprintln!("Source stack: {source:?}");
                                        eprintln!("Target stack top: {target:?}");
                                        panic!("Script is not functional copy: {script:?}");
                                    }
                                    if let Err(other_script) =
                                        script_is_optimal_copy(source, target, &script)
                                    {
                                        eprintln!("Source stack: {source:?}");
                                        eprintln!("Target stack top: {target:?}");
                                        eprintln!("Computed script: {script:?}");
                                        panic!("Other script is better: {other_script:?}");
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
