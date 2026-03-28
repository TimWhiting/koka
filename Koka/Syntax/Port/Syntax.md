# Porting Audit: Syntax.Syntax

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Program` | [x] | - | - | 26 | 285 | No |
| `UserProgram` | [x] | - | - | 43 | 297 | No |
| `External` | [x] | - | - | 63 | 255 | No |
| `ExternalCall` | [x] | - | - | 81 | 113 | No |
| `FixDef` | [x] | - | - | 89 | 278 | No |
| `Import` | [x] | - | - | 103 | 268 | No |
| `TypeDefGroup` | [x] | - | - | 123 | 246 | No |
| `TypeDef` | [x] | - | - | 129 | 228 | No |
| `TypeBinder` | [x] | - | - | 149 | 61 | No |
| `UserCon` | [x] | - | - | 158 | 216 | No |
| `DefGroup` | [x] | - | - | 181 | 169 | No |
| `Def` | [x] | - | - | 202 | 174 | No |
| `defIsVal` | [x] | - | - | 213 | 335 | No |
| `guardTrue` | [x] | - | - | 217 | 338 | No |
| `Expr` | [x] | - | - | 225 | 144 | No |
| `HandlerOverride` | [x] | - | - | 251 | 129 | No |
| `HandlerScope` | [x] | - | - | 255 | 134 | No |
| `HandlerBranch` | [x] | - | - | 259 | 202 | No |
| `Branch` | [x] | - | - | 269 | 183 | No |
| `Guard` | [x] | - | - | 273 | 188 | No |
| `Pattern` | [x] | - | - | 278 | 193 | No |
| `Lit` | [x] | - | - | 288 | 33 | No |
| `litRange` | [x] | - | - | 295 | 40 | No |
| `stripExpr` | [x] | - | - | 303 | 355 | No |
| `UserQuantifier`| [x] | - | - | 317 | 49 | No |
| `KUserType` | [x] | - | - | 320 | 71 | No |
| `UserKind` | [x] | - | - | 335 | 81 | No |
| `Ranged instances`| [x] | - | - | 346-432 | 392-473 | No |
| `HasName` | [x] | - | - | 439 | 359 | No |
| `HasFreeTypeVar` | [x] | - | - | 476 | 549 | No |
| `defBody` | [x] | - | - | 505 | 341 | No |
| `defName` | [x] | - | - | 508 | 328 | No |
| `defType` | [x] | - | - | 511 | 344 | No |
| `typeDefName` | [x] | - | - | 518 | 330 | No |
| `typeDefNameRange`| [x] | - | - | 521 | 349 | No |
| `programNull` | [x] | - | - | 525 | 482 | No |
| `preludeImport` | [x] | - | - | 529 | 479 | No |
| `makeProgram` | [x] | - | - | 533 | 485 | No |
| `programAddImports`| [x] | - | - | 537 | 493 | No |
| `programAddDefs` | [x] | - | - | 541 | 496 | No |
| `programRemoveAllDefs`| [x] | - | - | 570 | 507 | No |
| `programRemoveDef`| [x] | - | - | 574 | 510 | No |
| `programFind` | [x] | - | - | 589 | 521 | No |

## Notes
- `HasName` class and its instances have been ported.
- Small helper functions (`defIsVal`, `guardTrue`, `defBody`, `defType`, `typeDefNameRange`) have been ported.
- Functional parity for core AST is complete (excluding `lexSource` which depends on the Lexer).
