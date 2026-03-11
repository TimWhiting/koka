# Porting Audit: Printer

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Printer` class | [x] | - | - | 55 | 12 | No |
| `MonoPrinter` | [x] | - | - | 115 | 27 | No |
| `FilePrinter` | [x] | - | - | 142 | 46 | No |
| `AnsiPrinter` | [x] | - | - | 196 | 152 | No |
| `AnsiStringPrinter` | [x] | - | - | 219 | 195 | No |
| `HtmlPrinter` | [x] | - | - | 453 | 74 | No |
| `HtmlTextPrinter` | [x] | - | - | 478 | 226 | No |
| `ColorPrinter` | [x] | - | - | 356 | 272 | No |
| `withXPrinter` | [x] | - | - | 364-388 | 367-378 | No |
| `ansiWithColor` | [x] | - | - | 261 | 145 | No |
| `htmlEscape` | [x] | - | - | 554 | 76 | No |
| `sanitize` | [ ] | - | - | 103 | - | Yes |
| `ConsolePrinter` | [ ] | - | - | 432 | - | Yes |

## Notes
- Functional parity maintained for core abstracted printers (ANSI, HTML, Mono, File).
- **Partial**: Windows-specific `ConsolePrinter` (using `System.Console.Isocline` or Windows API) is not ported.
- **Partial**: `sanitize` (mapping non-ASCII to `?` on Windows) is missing.
- ANSI escape sequence logic (`reqSetConsole`) is ported and correct.
