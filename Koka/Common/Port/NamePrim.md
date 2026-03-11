# Porting Audit: Common.NamePrim

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `nameExpr`, `nameType` | [x] | - | - | 201-202 | 14-15 | No |
| `nameInteractiveModule` | [x] | - | - | 204 | 17 | No |
| `nameMain`, `nameCopy`, `nameOpExpr` | [x] | - | - | 206-208 | 19-21 | No |
| `copyNameOf` | [x] | - | - | 210 | 23 | No |
| `nameIf`, `nameCase` | [x] | - | - | 216-217 | 26-27 | No |
| `nameSystemCore`, `preludeName` | [x] | - | - | 550, 537 | 31-33 | No |
| Basic types (`io`, `named`, `pure`...) | [x] | - | - | 223 - 239 | 35-49 | No |
| Lists (`Nil`, `Cons`, `list`) | [x] | - | - | 246 - 248 | 56-58 | No |
| Debug names (`assert`, `trace`...) | [x] | - | - | 254-260 | 63-69 | No |
| Lazy names (`memoize`, `enter`...) | [x] | - | - | 266-275 | 74-82 | No |
| Vector names (`unvlist`...) | [x] | - | - | 280-282 | 87-89 | No |
| Int/Num names (`uint8`, `int32`...) | [x] | - | - | 290-307 | 94-106 | No |
| Exn names (`exception`, `exn`...) | [x] | - | - | 313-315 | 111-113 | No |
| Contexts (`ctx`, `cctx`...) | [x] | - | - | 321-339 | 118-132 | No |
| Hnd names (`ev`, `evv`, `clause`...) | [x] | - | - | 345-378 | 137-167 | No |
| `isClauseTailName` | [x] | - | - | 380 | 169 | No |
| Types (`ref`, `tuple`...) | [x] | - | - | 391-498 | 180-264 | No |
| Ref counts (`@dup`, `@drop`...) | [x] | - | - | 500-511 | 266-276 | No |
| `nameTuple`, `nameTpTuple` | [x] | - | - | 513-517 | 278-282 | No |
| `isNameTuple`, `isNameTpTuple` | [x] | - | - | 520-534 | 284-293 | No |
| `isSystemCoreName`, `shorten..` | [x] | - | - | 558-567 | 295-303 | No |
| `isPrimitiveModule/Name` | [x] | - | - | 569-573 | 305-309 | No |
| Kind constructors (`->`, `E`...) | [x] | - | - | 578-585 | 314-321 | No |

## Notes
- `isClauseTailName` and tuple boolean checks use explicit string manipulations and index calculations mirroring Haskell's logic.
- The module is 100% data constructors defining constants of `Name`.
