# Porting Audit: NameMap

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `NameMap` | [x] | - | - | 25 | 16 | No |
| `NameMap.find` | [x] | - | - | 27 | 18 | No |

## Notes
- `NameMap a` is an alias for `Std.HashMap Name a` in Lean.
- Functional parity maintained for the type and the `find` helper.
