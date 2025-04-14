# Use cases of opcodes

Some opcodes seem useless at first glance, but they have an actual use case.

## `OP_DROP`, `OP_2DROP`

- some operations don't consume their arguments for softfork-compatability reasons
    - `OP_CTV`
    - `OP_CSV`
    - `OP_CLTV`
    - Winternitz signaure verify
- topmost stack item is no longer used, items below are arguments of next op
- if and else branch use different arguments
    - drop padding
- drop lookup tables

```
OP_IF
    OP_2DROP # drop input
    OP_PUSHBYTES 0
OP_ELSE
    OP_ADD # process input
OP_ENDIF
```

## `OP_TUCK`

- copy topmost stack item, consume second-topmost item
