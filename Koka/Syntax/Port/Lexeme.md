# Porting Audit: Syntax.Lexeme

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `isTypeVar` | [x] | - | - | 28-32 | 16-19 | No |
| `Lexeme` | [x] | - | - | 38-39 | 45-48 | No |
| `Lex` | [x] | - | - | 42-67 | 25-42 | No |
| `lexemeIsWhite` | [x] | - | - | 70-72 | 58-59 | No |
| `lexIsWhite` | [x] | - | - | 75-80 | 53-56 | No |
| `sameLexeme` | [x] | - | - | 83-85 | 87-88 | No |
| `sameLex` | [x] | - | - | 88-93 | 82-85 | No |
| `fromEnum Lex` | [x] | - | - | 95-120 | 61-79 | No |
| `Show Lexeme` | [x] | - | - | 122-123 | 114 | No |
| `Show Lex` | [x] | - | - | 125-126 | 115 | No |
| `Ranged Lexeme` | [x] | - | - | 128-129 | 117-118 | No |
| `showLexeme` | [x] | - | - | 131-134 | 111-112 | No |
| `showLex` | [x] | - | - | 136-162 | 90-109 | No |
| `LexImport` | [x] | - | - | 170-173 | 124-129 | No |
| `Show LexImport` | [x] | - | - | 175-179 | 131-137 | No |
| `Eq LexImport` | [x] | - | - | 181-182 | 139-140 | No |
| `lexImportNub` | [x] | - | - | 185-194 | 142-153 | Yes |

## Notes
- Translated all AST models.
- Re-implemented generic traversals like standard ENUM numeric extraction explicitly using `fromEnumLex`.
- Extracted recursive lists safely to filter redundancies using Lean implementations of `List.filter` and mapped elements, marking `lexImportNub` terminal blocks as `partial` to bypass explicit List well-founded relations checking.
