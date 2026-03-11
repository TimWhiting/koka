# Porting Audit: Common.QNameMap

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `QNameMap` | [x] | - | - | 36 | 20 | No |
| `Lookup` | [x] | - | - | 44-46 | 22-25 | No |
| `empty` | [x] | - | - | 48-49 | 28-29 | No |
| `isEmpty` | [x] | - | - | 51-53 | 31-32 | No |
| `safeCombine` | [x] | - | - | 111-117 | 34-40 | No |
| `insert` | [x] | - | - | 89-91 | 42-46 | No |
| `single` | [x] | - | - | 55-57 | 48-49 | No |
| `fromList` | [x] | - | - | 59-61 | 51-52 | No |
| `lookupQ` | [x] | - | - | 64-68 | 54-60 | No |
| `lookup` | [x] | - | - | 72-80 | 62-78 | No |
| `filterNames` | [x] | - | - | 83-87 | 80-84 | No |
| `union` | [x] | - | - | 93-95 | 86-91 | No |
| `unionLeftBias` | [x] | - | - | 97-99 | 93-98 | No |
| `unions` | [x] | - | - | 102-104 | 100-101 | No |
| `toAscList` | [x] | - | - | 106-108 | 103-106 | No |

## Notes
- Adapted Haskell's `Data.Map.Strict` to Lean 4's `Std.HashMap`.
- `toAscList` manually flattens and sorts the elements because `HashMap` doesn't maintain ascending order like `Data.Map` does.
- `safeCombine` uses explicit string construction for error messages due to lack of `Show` for some types, matching Koka's original error messages closely using `panic!`.
