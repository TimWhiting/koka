# Porting Audit: Unique

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `HasUnique` | [x] | - | - | 25 | 15 | No |
| `setUnique/unique/s` | [x] | - | - | 40-46 | 18-25 | No |
| `uniqueId/s` | [x] | - | - | 49-53 | 35-39 | No |
| `uniqueName/From` | [x] | - | - | 57-61 | 43-47 | No |
| `Unique` | [x] | - | - | 69 | 51 | No |
| `runUnique/With` | [x] | - | - | 73-78 | 71-74 | No |
| `withUnique/liftUnique` | [x] | - | - | 82-90 | 78-84 | No |
| `UniqueT` | [x] | - | - | 111 | 87 | No |

## Notes
- `Unique` and `UniqueT` are implemented as state transformer types in Lean.
- Functional parity is 100%.
