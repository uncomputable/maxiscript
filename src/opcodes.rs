use std::cmp::Ordering;
use std::collections::BinaryHeap;

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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ScriptFailed;

impl<T: Clone + Eq> StackOp<T> {
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
    pub fn reverse_apply(target: &[T]) -> Vec<(Self, Vec<T>)> {
        let mut sources = Vec::new();

        // OP_DUP
        if let Some((bottom, [top0_prime, top0])) = target.split_last_chunk() {
            if top0 == top0_prime {
                sources.push((Self::Dup, bottom.iter().chain([top0]).cloned().collect()));
            }
        }

        // OP_2DUP
        if let Some((bottom, [top1_prime, top0_prime, top1, top0])) = target.split_last_chunk() {
            if top0 == top0_prime && top1 == top1_prime {
                sources.push((
                    Self::_2Dup,
                    bottom.iter().chain([top1, top0]).cloned().collect(),
                ));
            }
        }

        // OP_3DUP
        if let Some((bottom, [top2_prime, top1_prime, top0_prime, top2, top1, top0])) =
            target.split_last_chunk()
        {
            if top0 == top0_prime && top1 == top1_prime && top2 == top2_prime {
                sources.push((
                    Self::_3Dup,
                    bottom.iter().chain([top2, top1, top0]).cloned().collect(),
                ));
            }
        }

        // OP_OVER
        if let Some((bottom, [top1_prime, top0, top1])) = target.split_last_chunk() {
            if top1 == top1_prime {
                sources.push((
                    Self::Over,
                    bottom.iter().chain([top1, top0]).cloned().collect(),
                ));
            }
        }

        // OP_2OVER
        if let Some((bottom, [top3_prime, top2_prime, top1, top0, top3, top2])) =
            target.split_last_chunk()
        {
            if top2 == top2_prime && top3 == top3_prime {
                sources.push((
                    Self::_2Over,
                    bottom
                        .iter()
                        .chain([top3, top2, top1, top0])
                        .cloned()
                        .collect(),
                ));
            }
        }

        // OP_TUCK
        if let Some((bottom, [top0_prime, top1, top0])) = target.split_last_chunk() {
            if top0 == top0_prime {
                sources.push((
                    Self::Tuck,
                    bottom.iter().chain([top1, top0]).cloned().collect(),
                ));
            }
        }

        // OP_PICK
        if let Some((bottom, [top0])) = target.split_last_chunk() {
            sources.push((Self::Pick(top0.clone()), Vec::from(bottom)));
        }

        sources
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct State<T> {
    pub script_bytes: usize,
    pub reversed_script: Vec<StackOp<T>>,
    target: Vec<T>,
}

impl<T> State<T> {
    pub fn new(target: Vec<T>) -> Self {
        Self {
            script_bytes: 0,
            reversed_script: vec![],
            target,
        }
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

pub fn find_shortest_transformation<T: Clone + Ord + std::fmt::Debug + std::hash::Hash>(
    source_stack: &[T],
    target_stack_top: &[T],
) -> Option<State<T>> {
    if target_stack_top
        .iter()
        .any(|name| !source_stack.contains(name))
    {
        return None;
    }

    let initial_state = State::new(target_stack_top.to_vec());
    let mut priority_queue = BinaryHeap::from([initial_state]);

    // Each reverse application of opcode reduces target by 1
    // Termination is guaranteed
    while let Some(state) = priority_queue.pop() {
        debug_assert!(
            state.target.len() <= target_stack_top.len(),
            "the target should never increase in size"
        );
        debug_assert!(
            state.script_bytes <= target_stack_top.len() * 2,
            "maximum transformation cost should be 2 times target size (using OP_PICK)"
        );
        if state.target.len() <= source_stack.len()
            && state.target == source_stack[source_stack.len() - state.target.len()..]
        {
            return Some(state);
        }

        for (next_op, next_target) in StackOp::reverse_apply(&state.target) {
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
            })
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_manipulation() {
        let source_target: [(&[u8], &[u8]); 3] = [
            (&[0], &[0, 0, 0]),
            (&[12, 11, 10, 0], &[0, 0, 0]),
            (&[2, 1, 0], &[0, 1, 2]),
        ];

        for (source_stack, target_stack_top) in source_target {
            let state = find_shortest_transformation(source_stack, target_stack_top)
                .expect("there should be a transformation");
            let script = state.reversed_script.into_iter().rev();
            let mut stack = Vec::from(source_stack);
            StackOp::apply(&mut stack, script).expect("script should not fail");
            assert!(
                state.script_bytes <= target_stack_top.len() * 2,
                "maximum transformation cost should be 2 * N for N target items"
            );
            assert!(
                target_stack_top.len() <= stack.len(),
                "result stack should be long enough to include target"
            );
            assert_eq!(
                &stack[stack.len() - target_stack_top.len()..],
                target_stack_top,
                "result stack top should be equal to target"
            );
        }
    }
}
