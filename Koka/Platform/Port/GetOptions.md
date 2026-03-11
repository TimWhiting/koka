# Porting Audit: Platform.GetOptions

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `ArgOrder` | [x] | - | - | 16 | 10-13 | No |
| `ArgDescr` | [x] | - | - | 18 | 15-18 | No |
| `OptDescr` | [x] | - | - | 17 | 20-25 | No |
| `usageInfo` | [x] | - | - | 15 | 27-36 | No |
| `getOpt` | [x] | - | - | 15 | 40-82 | Yes |

## Notes
- As Lean 4 lacks a built-in `System.Console.GetOpt`, I implemented a native Lean 4 version supporting basic POSIX-style argument parsing. 
- The `getOpt` function is marked partial due to list recursion and string manipulation matching that isn't trivially seen as structurally decreasing by Lean's checker, though it's practically safe for bounded argument lists.
