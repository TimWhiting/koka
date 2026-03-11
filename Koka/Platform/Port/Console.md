# Porting Audit: Platform.Console

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `setColor` | [x] | - | - | 23-26 | 15-16 | No |
| `setBackColor` | [x] | - | - | 28-31 | 18-19 | No |
| `setReverse` | [x] | - | - | 33-36 | 21-22 | No |
| `setUnderline` | [x] | - | - | 38-41 | 24-25 | No |
| `withConsole` | [x] | - | - | 44-49 | 28-29 | No |
| `bracketConsole` | [x] | - | - | 52-56 | 32-33 | No |
| `getProgramPath` | [x] | - | - | 59-62 | 36-38 | No |

## Notes
- `Platform.Console` FFI methods from `cconsole.c` are unlinked in the Lean branch. We replaced them with simple pure-IO stubs because Lean outputs natively to ANSI terminals.
- `getProgramPath` natively leverages `IO.appPath` instead of relying on the C shim.
