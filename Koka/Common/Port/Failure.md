# Porting Audit: Failure

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `assertion` | [x] | - | - | 24 | 9 | No |
| `failure` | [x] | - | - | 30 | 12 | No |
| `todo` | [x] | - | - | 34 | 15 | No |
| `matchFailure` | [x] | - | - | 38 | 18 | No |
| `raise` | [x] | - | - | 42 | 21 | No |
| `raiseIO` | [x] | - | - | 48 | 24 | No |
| `catchIO` | [x] | - | - | 52 | 27 | No |

## Notes
- Functional parity maintained for all core error handling and assertion helpers.
- `catchIO` in Lean is simplified and does not perform the complex string cleaning/adjusting found in the Haskell version's `adjust` helper.
