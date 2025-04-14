# Optimizing Bitcoin Script

## Maximum optimization

- produce value earlier? / produce value later?
- keep value on stack? / push value onto alt stack for later use?
    - alt stack is not strictly necessary
    - use alt stack to temporarily reduce stack size
- use value that is already on stack? / produce value on the fly?
    - only useful for values that can be produced within 2 bytes
    - (small) byte literals
    - introspection opcodes
    - copying / moving from stack takes at most 1 + log2(len(stack)) / 8 many bytes
- leave value on stack for later use? / consume value from stack?
    - copy value? / move value?
- keep values at special stack positions in order to use specialized opcodes?
    - `OP_PICK 0` → `OP_DUP`
    - `OP_PICK 1` → `OP_OVER`
    - `OP_ROLL 0` → no operation
    - `OP_ROLL 1` → `OP_SWAP`
    - `OP_ROLL 2` → `OP_ROT`
    - `OP_TOALTSTACK OP_FROMALTSTACK` → no operation
- which order for inputs / outputs of a function call?
    - current stack determines which input order can be fetched most efficiently
    - children determine which output order can be fetched (consumed) most efficiently
    - for maximum efficiency, each function call must be compiled separately
    - output order has nonlocal effects on children
- each function call expects its arguments on the top of the stack
    - the target (arguments) is fixed
    - the stack below the target is variable and determines the efficiency of following calls
    - `bot [ below: variable ][ target: fixed ] top`

## Tractible optimization

- optimize each function as a separate unit
    - order of inputs / outputs is fixed across all calls to the function
        - set by the bitfony programmer
        - todo: optimize by the compiler in a later version
    - fetch arguments from stack dynamically and optimally for each call
- each bitfony line is a chunk that produces and consumes variables
    - order chunks according to value dependency (topological order)
    - iterate over all valid orders and choose best result
    - best = smallest number of target code bytes
- arguments of some opcodes are swappable
    - `OP_EQUAL`, `OP_EQUALVERIFY`, `OP_ADD`, `OP_BOOLAND`, `OP_BOOLOR`, `OP_NUMEQUAL`, `OP_NUMEQUALVERIFY`, `OP_NUMNOTEQUAL`, `OP_MIN`, `OP_MAX`
    - todo: choose optimal order by compiler in a later version
        - multiple argument targets for same function call
        - choose target with smallest fetch script
- some opcode calls are interchangeable
    - `x y OP_LESSTHAN` = `y x OP_GREATERTHAN`
    - `x y OP_LESSTHANOREQUAL` = `y x OP_GREATERTHANOREQUAL`
    - alternative call might have smaller argument fetch script

## Function sanitation

- only declared inputs may be used
    - it is possible to run function on empty stack + arguments
    - stack before call: `bot [ below ][ args ] top`
    - stack after call: `bot [ below ][ output ] top`
- all inputs must be consumed
    - values that are not popped by softfork opcodes (e.g. `OP_CLTV`) must be explicitly dropped
- only declared outputs may be produced

## Variable sanitation

- variables are immutable
    - varibles cannot be reassigned
- each variable must have a fresh name
    - variables cannot be redefined
