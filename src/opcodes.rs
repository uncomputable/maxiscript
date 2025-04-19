use crate::util;
use std::fmt;

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
            Self::Pick(_) | Self::Roll(_) => 2,
            _ => 1,
        }
    }
}

fn script_cost<T>(script: &[StackOp<T>]) -> usize {
    script.iter().map(StackOp::cost).sum()
}

// TODO: Copy some elements, move other elements
// TODO: result stack: allow change of order below target (enables smaller scripts?)
/// Computes a minimal Bitcoin script that puts the `target` on top of the `source` stack.
///
/// After applying the script, the result stack consists of the `source` stack
/// (exactly the same order and number of elements) with the `target` on top.
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
pub fn find_shortest_transformation<T: Clone + Ord + fmt::Debug + std::hash::Hash>(
    source: &[T],
    target: &[T],
) -> Option<Vec<StackOp<T>>> {
    // Bail out if the source is missing elements from the target
    if target.iter().any(|name| !source.contains(name)) {
        return None;
    }

    let initial_state = State::new(target.to_vec());
    let mut queue_n_plus_0 = vec![initial_state];
    let mut queue_n_plus_1 = Vec::new();
    let mut script_bytes = 0;

    loop {
        // Termination is guaranteed
        debug_assert!(
            script_bytes <= target.len() * 2,
            "maximum transformation cost should be 2 times target size (using OP_PICK or OP_ROLL)"
        );
        let mut queue_n_plus_2 = Vec::new();

        for state in queue_n_plus_0 {
            debug_assert_eq!(script_bytes, script_cost(&state.script));
            // println!("{:?}", state.script);

            // Bail out if we produced more than the target
            if target.len() < state.above.len() {
                continue;
            }
            if state.matches(source, target) {
                return Some(state.script);
            }

            queue_n_plus_1.extend(state.reverse_apply1());
            queue_n_plus_2.extend(state.reverse_apply2());
        }

        queue_n_plus_0 = queue_n_plus_1;
        queue_n_plus_1 = queue_n_plus_2;
        script_bytes += 1;
    }
}

fn unify<'a, T: Eq>(a: Option<&'a T>, b: Option<&'a T>) -> Option<&'a T> {
    match (a, b) {
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        _ => None,
    }
}

/// Pseudo script for computing stack top.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum Above<T> {
    Push(T),
    Tuck,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct State<T> {
    script: Vec<StackOp<T>>,
    /// Stack elements that are required to reach this state.
    ///
    /// `None` elements are free variables that match anything.
    target: Vec<Option<T>>,
    /// Produced stack elements above target.
    ///
    /// The stack elements are encoded in a pseudo script.
    above: Vec<Above<T>>,
}

impl<T> State<T> {
    pub fn new(target: Vec<T>) -> Self {
        Self {
            script: vec![],
            target: target.into_iter().map(Some).collect(),
            above: Vec::new(),
        }
    }
}

impl<T: Clone + Eq> State<T> {
    /// Checks if the state matches the given `source` stack and the given `target` stack top.
    pub fn matches(&self, source: &[T], target: &[T]) -> bool {
        let mut above = Vec::with_capacity(target.len());
        for op in &self.above {
            match op {
                Above::Push(x) => above.push(x),
                // TODO: Allow target to merge with source stack, in case of moved variables
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

        // TODO: Allow target to merge with source stack, in case of moved variables
        if target.len() != above.len() || (0..target.len()).any(|i| &target[i] != above[i]) {
            return false;
        }

        self.target.len() <= source.len()
            && self.target.iter().enumerate().all(|(index, x)| match x {
                Some(x) => &source[source.len() - self.target.len() + index] == x,
                None => true,
            })
    }

    fn make_child(&self, op: StackOp<T>, target: Vec<Option<T>>, above: Vec<Above<T>>) -> Self {
        State {
            script: std::iter::once(op)
                .chain(self.script.iter().cloned())
                .collect(),
            target,
            above,
        }
    }

    /// Computes all states that lead to the present state via an opcode.
    ///
    /// Opcodes are applied reversely.
    ///
    /// For the present state `S`,
    /// if there is a state `T` with transition `T → S`,
    /// then include `T` in the output.
    pub fn reverse_apply1(&self) -> Vec<Self> {
        let mut children = Vec::new();

        // OP_DUP
        //
        // [α 0] → [α 0 0]
        // [  0] → [  _ 0]
        let (bottom, [top0_prime, top0]) = util::split_last_chunk2(&self.target);

        if let Some(top0) = unify(top0, top0_prime) {
            children.push(
                self.make_child(
                    StackOp::Dup,
                    bottom.iter().cloned().chain([Some(top0.clone())]).collect(),
                    [Above::Push(top0.clone())]
                        .into_iter()
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
        }

        // OP_2DUP
        //
        // [α 1 0] → [α 1 0 1 0]
        // [  1 0] → [  _ 0 1 0]
        // [  1 0] → [  _ _ 1 0]
        let (bottom, [top1_prime, top0_prime, top1, top0]) = util::split_last_chunk2(&self.target);

        if let (Some(top1), Some(top0)) = (unify(top1, top1_prime), unify(top0, top0_prime)) {
            children.push(
                self.make_child(
                    StackOp::_2Dup,
                    bottom
                        .iter()
                        .cloned()
                        .chain([Some(top1.clone()), Some(top0.clone())])
                        .collect(),
                    [Above::Push(top1.clone()), Above::Push(top0.clone())]
                        .into_iter()
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
        }

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
            children.push(
                self.make_child(
                    StackOp::_3Dup,
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
                    .chain(self.above.iter().cloned())
                    .collect(),
                ),
            );
        }

        // OP_OVER
        //
        // [α 1 0] → [α 1 0 1]
        // [  1 0] → [  _ 0 1]
        // [  1 _] → [  _ _ 1]
        let (bottom, [top1_prime, top0, top1]) = util::split_last_chunk2(&self.target);

        if let Some(top1) = unify(top1, top1_prime) {
            children.push(
                self.make_child(
                    StackOp::Over,
                    bottom
                        .iter()
                        .cloned()
                        .chain([Some(top1.clone()), top0.cloned()])
                        .collect(),
                    [Above::Push(top1.clone())]
                        .into_iter()
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
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
            children.push(
                self.make_child(
                    StackOp::_2Over,
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
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
        }

        // OP_TUCK
        //
        // [α 1 0] → [α 0 1 0]
        // [  1 0] → [  _ 1 0]
        // [  _ 0] → [  _ _ 0]
        let (bottom, [top0_prime, top1, top0]) = util::split_last_chunk2(&self.target);

        if let Some(top0) = unify(top0, top0_prime) {
            children.push(
                self.make_child(
                    StackOp::Tuck,
                    bottom
                        .iter()
                        .cloned()
                        .chain([top1.cloned(), Some(top0.clone())])
                        .collect(),
                    [Above::Tuck]
                        .into_iter()
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
        }

        // // OP_SWAP
        // //
        // // [α 1 0] → [α 0 1]
        // if let Some((bottom, [top0, top1])) = self.target.split_last_chunk() {
        //     children.push(
        //         self.make_child(
        //             StackOp::Swap,
        //             bottom.iter().chain([top1, top0]).cloned().collect(),
        //             self.above.clone(),
        //         ),
        //     );
        // }
        //
        // // OP_2SWAP
        // //
        // // [α 3 2 1 0] → [α 1 0 3 2]
        // if let Some((bottom, [top1, top0, top3, top2])) = self.target.split_last_chunk() {
        //     children.push(
        //         self.make_child(
        //             StackOp::_2Swap,
        //             bottom.iter().chain([top3, top2, top1, top0]).cloned().collect(),
        //             self.above.clone(),
        //         ),
        //     );
        // }
        //
        // // OP_ROT
        // //
        // // [α 2 1 0] → [α 1 0 2]
        // if let Some((bottom, [top1, top0, top2])) = self.target.split_last_chunk() {
        //     children.push(
        //         self.make_child(
        //             StackOp::Rot,
        //             bottom.iter().chain([top2, top1, top0]).cloned().collect(),
        //             self.above.clone(),
        //         ),
        //     );
        // }
        //
        // // OP_2ROT
        // //
        // // [α 5 4 3 2 1 0] → [α 3 2 1 0 5 4]
        // if let Some((bottom, [top3, top2, top1, top0, top5, top4])) = self.target.split_last_chunk() {
        //     children.push(
        //         self.make_child(
        //             StackOp::_2Rot,
        //             bottom.iter().chain([top5, top4, top3, top2, top1, top0]).cloned().collect(),
        //             self.above.clone(),
        //         ),
        //     );
        // }

        children
    }

    pub fn reverse_apply2(&self) -> Vec<Self> {
        let mut children = Vec::new();

        // OP_PICK X
        //
        // [α X β] → [α X β X]
        if let Some((bottom, [Some(top0)])) = self.target.split_last_chunk() {
            children.push(
                self.make_child(
                    StackOp::Pick(top0.clone()),
                    Vec::from(bottom),
                    [Above::Push(top0.clone())]
                        .into_iter()
                        .chain(self.above.iter().cloned())
                        .collect(),
                ),
            );
        }

        // OP_ROLL X
        //
        // [α       X β] → [α       β X]
        // [α     2 1 0] → [α     1 0 2]
        // [α   3 2 1 0] → [α   2 1 0 3]
        // [α 4 3 2 1 0] → [α 3 2 1 0 4]
        // ...
        // The following doesn't make sense:
        // [α         0] → [α         0] (NOP)
        // [α       1 0] → [α       0 1] (OP_SWAP is equivalent and cheaper)
        //
        // Two possibilities:
        // 1) X is taken from inside target (spawn one child for each position)
        // 2) X is taken from outside target (spawn one extra child; consider this when extending target _ in future steps)
        //
        // if let Some((bottom, [Some(top0)])) = self.target.split_last_chunk() {
        //     children.push(
        //         self.make_child(
        //             StackOp::Pick(top0.clone()),
        //             Vec::from(bottom),
        //             [Above::Push(top0.clone())]
        //                 .into_iter()
        //                 .chain(self.above.iter().cloned())
        //                 .collect(),
        //         ),
        //     );
        // }

        children
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::{repeat_n, Itertools};

    type Script = Vec<StackOp<usize>>;

    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    pub struct ScriptFailed;

    pub fn run_script(stack: &mut Vec<usize>, script: &Script) -> Result<(), ScriptFailed> {
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
        assert_eq!(&[StackOp::Over, StackOp::_2Over], script.as_slice())
    }

    #[test]
    fn find_transformation_regression3() {
        // [0 1 2] --OVER-> [0 1 2 1] --Pick(0)-> [0 1 2 1 0] --TUCK-> [0 1 2 0 1 0]
        // [0 1 0] <-TUCK-- [1 0] <-Pick(0)-- [1] <-OVER-- [1 _]
        let source = &[0, 1, 2];
        let target = &[0, 1, 0];
        let script = find_shortest_transformation(source, target).unwrap();
        assert_eq!(
            &[StackOp::Over, StackOp::Pick(0), StackOp::Tuck],
            script.as_slice()
        )
    }

    fn all_stack_ops(target: &[usize]) -> impl Iterator<Item = StackOp<usize>> + Clone + '_ {
        [
            StackOp::Dup,
            StackOp::_2Dup,
            StackOp::_3Dup,
            StackOp::Over,
            StackOp::_2Over,
            StackOp::Tuck,
            // StackOp::Swap,
            // StackOp::_2Swap,
            // StackOp::Rot,
            // StackOp::_2Rot,
        ]
        .into_iter()
        .chain(target.iter().copied().map(StackOp::Pick))
    }

    fn all_copy_scripts(target: &[usize]) -> impl Iterator<Item = Script> + '_ {
        repeat_n(all_stack_ops(target), target.len())
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

    // fn multiset<T: Eq + std::hash::Hash>(s: &[T]) -> HashMap<&T, usize> {
    //     let mut counts = HashMap::new();
    //
    //     for item in s {
    //         *counts.entry(item).or_insert(0) += 1;
    //     }
    //
    //     counts
    // }

    fn script_is_functional_copy(source: &[usize], target: &[usize], script: &Script) -> bool {
        let mut final_stack = Vec::from(source);
        let result = run_script(&mut final_stack, script);
        result.is_ok()
            && source.len() + target.len() == final_stack.len()
            && target == &final_stack[source.len()..] // match target precisely
            && source == &final_stack[..source.len()] // match source precisely

        // && multiset(&final_stack[..source.len()]) == multiset(source) // match source without respect to order
    }

    // TODO: Cache optimal scripts
    fn script_is_shortest_copy(
        source: &[usize],
        target: &[usize],
        script: &Script,
    ) -> Result<(), Script> {
        // let best_script = BEST_SCRIPT.get(source).unwrap().get(target).unwrap();
        // if script_cost(&best_script) < script_cost(script) {
        //     return Err(best_script.clone());
        // }

        for other_script in all_copy_scripts(target) {
            if script_cost(&other_script) < script_cost(script)
                && script_is_functional_copy(source, target, &other_script)
            {
                return Err(other_script);
            }
        }

        Ok(())
    }

    fn transformation_is_optimal(source: &[usize], target: &[usize]) {
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

    #[test]
    fn size_above() {
        assert_eq!(2, size_of::<Above<u8>>());
    }

    #[test]
    fn transformation_is_optimal_2_1() {
        for top0 in 0..2 {
            for top1 in 0..2 {
                let source = &[top1, top0];
                for target0 in 0..2 {
                    let target = &[target0];
                    transformation_is_optimal(source, target);
                }
            }
        }
    }

    #[test]
    fn transformation_is_optimal_2_2() {
        for top0 in 0..2 {
            for top1 in 0..2 {
                let source = &[top1, top0];
                for target0 in 0..2 {
                    for target1 in 0..2 {
                        let target = &[target1, target0];
                        transformation_is_optimal(source, target);
                    }
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn transformation_is_optimal_3_1() {
        for top0 in 0..3 {
            for top1 in 0..3 {
                for top2 in 0..3 {
                    let source = &[top2, top1, top0];
                    for target0 in 0..3 {
                        let target = &[target0];
                        transformation_is_optimal(source, target);
                    }
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn transformation_is_optimal_3_2() {
        for top0 in 0..3 {
            for top1 in 0..3 {
                for top2 in 0..3 {
                    let source = &[top2, top1, top0];
                    for target0 in 0..3 {
                        for target1 in 0..3 {
                            let target = &[target1, target0];
                            transformation_is_optimal(source, target);
                        }
                    }
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn transformation_is_optimal_3_3() {
        for top0 in 0..3 {
            for top1 in 0..3 {
                for top2 in 0..3 {
                    let source = &[top2, top1, top0];
                    for target0 in 0..3 {
                        for target1 in 0..3 {
                            for target2 in 0..3 {
                                let target = &[target2, target1, target0];
                                transformation_is_optimal(source, target);
                            }
                        }
                    }
                }
            }
        }
    }
}
