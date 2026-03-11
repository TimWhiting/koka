# Porting Audit: IdNice

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Nice` | [x] | - | - | 25 | 13 | No |
| `niceEmpty` | [x] | - | - | 28 | 16 | No |
| `niceExtend` | [x] | - | - | 33 | 19 | No |
| `niceShow` | [x] | - | - | 40 | 27 | No |
| `nicePretty` | [~] | - | - | 47 | 32 | No |

## Notes
- `nicePretty` in Lean currently returns `String` instead of `Doc` (from `PPrint`). This was likely done to avoid a dependency on `Lib.PPrint` during the initial bootstrap. It is functionally identical for basic usage but should eventually be updated to return `Doc`.
- `niceExtend` implementation follows the Haskell logic of only extending with unused names and preserving existing mappings.
