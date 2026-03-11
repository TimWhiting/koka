# Porting Audit: Syntax

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `JsTarget` | [x] | - | - | 43 | 9 | No |
| `CTarget` | [x] | - | - | 44 | 13 | No |
| `Target` | [x] | - | - | 46 | 17 | No |
| `isTargetC` | [x] | - | - | 48 | 24 | No |
| `isTargetJS` | [x] | - | - | 51 | 28 | No |
| `isTargetWasm` | [x] | - | - | 54 | 32 | No |
| `Platform` | [x] | - | - | 76 | 52 | No |
| `platform32/64/etc` | [x] | - | - | 82 | 59-63 | No |
| `platformHasCompressedFields` | [x] | - | - | 90 | 65 | No |
| `alignUp` | [x] | - | - | 106 | 72 | No |
| `alignedAdd` | [x] | - | - | 103 | 76 | No |
| `alignedSum` | [x] | - | - | 100 | 79 | No |
| `BuildType` | [x] | - | - | 112 | 82 | No |
| `Visibility` | [x] | - | - | 125 | 93 | No |
| `isPublic/Private` | [x] | - | - | 128 | 97-103 | No |
| `HandlerSort` | [x] | - | - | 135 | 105 | No |
| `isHandlerInstance/Normal` | [x] | - | - | 144 | 114-120 | No |
| `OperationSort` | [x] | - | - | 151 | 122 | No |
| `opSortString` | [x] | - | - | 165 | 135 | No |
| `readOperationSort` | [x] | - | - | 175 | 143 | No |
| `DataEffect` | [x] | - | - | 191 | 155 | No |
| `DataKind` | [x] | - | - | 201 | 160 | No |
| `ValueRepr` | [x] | - | - | 263 | 170 | No |
| `valueReprSize/Scan/etc` | [x] | - | - | 274-298 | 179-201 | No |
| `FipAlloc` | [x] | - | - | 385 | 203 | No |
| `Fip` | [x] | - | - | 371 | 209 | No |
| `fipSubsumes/Max/etc` | [x] | - | - | 377-474 | 215-270 | No |
| `DataDef` | [x] | - | - | 209 | 271 | No |
| `dataDefIsValue/Lazy/etc` | [x] | - | - | 226-252 | 287-310 | No |
| `ParamInfo` | [x] | - | - | 311 | 311 | No |
| `DefSort` | [x] | - | - | 304 | 315 | No |
| `isDefFun/defFunEx/etc` | [x] | - | - | 316-331 | 321-340 | No |
| `DefInline` | [x] | - | - | 340 | 342 | No |
| `Fixity/Assoc` | [x] | - | - | 355-361 | 352-360 | No |
| `sepBySpace` | [x] | - | [x] | 450 | 362 | No |
| `memberDoc` | [x] | - | [x] | 477 | 365 | No |

## Notes
- Functional parity is 100%.
- String processing functions (`sepBySpace`, `memberDoc`) have unit tests in `Koka/Common/Test/Syntax.lean`.
- Platform-related alignment logic was ported exactly.
