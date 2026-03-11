# Porting Audit: Interpreter.Command

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Command` | [x] | - | - | 32-47 | 31-47 | No |
| `ShowCommand` | [x] | - | - | 50-58 | 21-29 | No |
| `readCommand` | [x] | - | - | 63-65 | 124-125 | No |
| `edit` / `removeBackspaces` | [x] | - | - | 71-78 | 53-62 | No |
| `parseCommand` | [x] | - | - | 84-125 | 80-122 | No |
| `commandHelp` | [x] | - | - | 127-167 | 131-158 | No |

## Notes
- `parseCommand` and underlying parsing functions originally used Parsec combinators in Haskell. Instead of porting Parsec or relying on Lean's complex Syntax parsers for a 15-case command set, I built a lightweight, native `String` parser. This operates directly on string prefixes and spaces to parse `Command`, which guarantees efficiency and avoids Parsec dependencies entirely. 
- Restructured `commandHelp` formatting to match `Koka.Lib.PPrint` Lean types (`vsep` and `textP` instead of `<->` and `text` to avoid typeclass/identifier collisions with Lean 4).
