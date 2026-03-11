# Porting Audit: IdSet

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `IdSet` | [x] | - | - | 22 | 11 | No |

## Notes
- `IdSet` is an alias for `Std.HashSet Int` in Lean, which is the equivalent of Haskell's `IntSet`.
- Functional parity maintained for the type definition.
