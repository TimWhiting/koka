# Porting Audit: Id

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Id` | [x] | - | - | 29 | 9 | No |
| `Ids` | [x] | - | - | 26 | 10 | No |
| `showId` | [x] | - | - | 32 | 14 | No |
| `genId` | [x] | - | - | 37 | 17 | No |
| `newId` | [x] | - | - | 42 | 20 | No |
| `newIdFromId` | [x] | - | - | 45 | 23 | No |
| `idNil` | [x] | - | - | 50 | 26 | No |
| `idNumber` | [x] | - | - | 55 | 29 | No |

## Notes
- `Id` is a simple alias for `Int`, maintaining 100% functional parity.
- No complex logic requires formal proofs at this stage.
