# Porting Audit: Lib.JSON

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `JsValue` | [x] | - | - | 26-32 | 19-26 | No |
| `JsObject` | [x] | - | - | 35 | 26 | No |
| `toString` | [x] | - | - | 38-42 | 32-40 | Yes |
| `Show JsValue` | [x] | - | - | 44-56 | 42 | No |
| `jsLookup` | [x] | - | - | 60-72 | 46-62 | Yes |
| `jsFind` | [x] | - | - | 75-79 | 65-68 | No |
| `fromLeanJson` | [NEW] | - | - | - | 73-88 | Yes |
| `readJSON` | [x] | - | - | 88-92 | 96-99 | No |
| `parseJSON` | [x] | - | - | 96-100 | 103-106 | No |
| `readJSONFromFile` | [x] | - | - | 104-109 | 109-114 | No |
| `parseJSONFromFile` | [x] | - | - | 112-115 | 117-122 | No |

## Notes
- Haskell's `Lib.JSON` was entirely implemented with a custom Parsec frontend. We have discarded the custom parser in favor of natively integrating `Lean.Data.Json` to parse strings, then using an adapter (`fromLeanJson`) to cast it to Koka's `JsValue` ADT.
- The lookup and serialization operations continue to directly traverse the native Koka `JsValue` ADT as expected.
- String slicing and floating point logic were adapted to use native Lean List structures and Float coercions.
