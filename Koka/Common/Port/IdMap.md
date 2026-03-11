# Porting Audit: IdMap

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `IdMap` | [x] | - | - | 22 | 11 | No |

## Notes
- `IdMap a` is an alias for `Std.HashMap Int a` in Lean, which is the equivalent of Haskell's `IntMap a`.
- Functional parity maintained for the type definition.
