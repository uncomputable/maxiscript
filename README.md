# Maxiscript

Write Bitcoin smart contracts in a Rust-like programming language.
Compile to Bitcoin Script for use on the blockchain.

```rust
fn main() {
    let pubkey = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798;
    let signature = 0xd2bcee6a047e765467f3ed7c3e8f55edcfa4a5fd37a9bcd064c1b5041599b187c3f9f2be0665d539e38eb75989b4bc3f6dd2d9d18c5c123613615d1731e0523e;
    op::checksig_verify(signature, pubkey);
}
```

- ✅ variables instead of ever-shifting stack items
- ✅ functions instead of copy-paste code
- ✅ minimization of resulting Bitcoin Script target code
- 🚧 type safety (wip)
