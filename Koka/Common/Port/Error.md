# Porting Audit: Common.Error

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Errors` | [x] | - | - | 41-42 | 48-50 | No |
| `Warnings` | [x] | - | - | 44 | 52 | No |
| `ErrorMessage` | [x] | - | - | 46-51 | 41-46 | No |
| `ErrorSeverity` | [x] | - | - | 53-54 | 18-24 | No |
| `ErrorKind` | [x] | - | - | 56-57 | 26-39 | No |
| `Ranged ErrorMessage` | [x] | - | - | 62-63 | 54-55 | No |
| `Ranged Errors` | [x] | - | - | 65-66 | 57-58 | No |
| `Show ErrorMessage` | [x] | - | - | 68-69 | 138-139 | No |
| `Show Errors` | [x] | - | - | 71-72 | 141-142 | No |
| `isWarning` | [x] | - | - | 74-75 | 60-63 | No |
| `infoMessageKind` | [x] | - | - | 78-79 | 65-66 | No |
| `warningMessageKind` | [x] | - | - | 81-82 | 68-69 | No |
| `errorMessageKind` | [x] | - | - | 84-85 | 71-72 | No |
| `warningMessage` | [x] | - | - | 87-88 | 74-75 | No |
| `errorMessage` | [x] | - | - | 90-91 | 77-78 | No |
| `errorsNil` | [x] | - | - | 94-95 | 80-81 | No |
| `errorsSingle` | [x] | - | - | 97-98 | 83-84 | No |
| `errorsAdd` | [x] | - | - | 100-101 | 86-87 | No |
| `mergeErrors` | [x] | - | - | 103-105 | 89-90 | No |
| `Pretty ErrorMessage` | [x] | - | - | 111-112 | 132-133 | No |
| `Pretty Errors` | [x] | - | - | 114-115 | 135-136 | No |
| `ppErrorSeverity` | [x] | - | - | 117-131 | 96-107 | No |
| `ppErrorMessage` | [x] | - | - | 134-136 | 118-123 | No |
| `ppErrors` | [x] | - | - | 138-140 | 125-126 | No |
| `toWarning` | [x] | - | - | 143-145 | 144-145 | No |
| `ErrorM` | [x] | - | - | 155-157 | 151-155 | No |
| `checkError` | [x] | - | - | 160-165 | 159-162 | No |
| `checkPartial` | [x] | - | - | 167-171 | 164-167 | No |
| `setPartial` | [x] | - | - | 173-177 | 169-172 | No |
| `handleError` | [x] | - | - | 179-183 | 179-182 | No |
| `ok` | [x] | - | - | 185-186 | 184-185 | No |
| `errorMsgs` | [x] | - | - | 188-189 | 187-188 | No |
| `errorMsg` | [x] | - | - | 191-192 | 190-191 | No |
| `errorMsgsPartial` | [x] | - | - | 194-195 | 193-194 | No |
| `errorMsgPartial` | [x] | - | - | 197-198 | 196-197 | No |
| `addErrorMsg` | [x] | - | - | 200-202 | 202-203 | No |
| `warningMsgs` | [x] | - | - | 204-205 | 205-206 | No |
| `warningMsg` | [x] | - | - | 207-208 | 199-200 | No |
| `addWarnings` | [x] | - | - | 210-215 | 208-214 | No |
| `addPartialResult` | [x] | - | - | 217-221 | 174-177 | No |
| `overridePartialResult` | [x] | - | - | 223-227 | 216-219 | No |
| `ignoreWarnings` | [x] | - | - | 229-233 | 221-224 | No |
| `Functor ErrorM` | [x] | - | - | 240-243 | 230-234 | No |
| `Applicative ErrorM` | [x] | - | - | 245-247 | 236-243 | No |
| `Monad ErrorM` | [x] | - | - | 249-253 | 245-249 | No |
| `Alternative ErrorM` | [x] | - | - | 258-269 | 251-258 | No |
| `MonadFail ErrorM` | [ ] | - | - | 255-256 | - | No |

## Notes
- Renamed the parameterized Haskell output type `Error b a` to `ErrorM b a` to avoid confusion with `Except.error` constructor spaces.
- Skipped `MonadFail` derivation as Lean 4 does not provide a standard typeclass for it implicitly within custom structures. Instead, logic should safely project or unwrap failures using standard `.error` branches.
- Type class conversions for `LessEq` were replaced with native definition derivations and explicit enums matching.
