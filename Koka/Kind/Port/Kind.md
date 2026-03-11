# Porting Audit: Kind.Kind

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Kind` | [x] | - | - | 36-39 | 18-21 | No |
| `KindCon` | [x] | - | - | 42 | 15 | No |
| `Flavour` | [x] | - | - | 47-50 | 29-32 | No |
| `hasKindStarResult` | [x] | - | - | 52-54 | 115-116 | No |
| `hasKindLabelResult` | [x] | - | - | 56-58 | 118-119 | No |
| `kindStar` | [x] | - | - | 65-67 | 45-46 | No |
| `kindLabel` | [x] | - | - | 70-72 | 49-50 | No |
| `kindArrow` | [x] | - | - | 75-77 | 53-54 | No |
| `kindAddArg` | [x] | - | - | 79-84 | 136-143 | Yes |
| `kindEffect` | [x] | - | - | 87-89 | 61-62 | No |
| `kindScope` | [x] | - | - | 91-93 | 64-65 | No |
| `kindHeap` | [x] | - | - | 95-97 | 67-68 | No |
| `kindLocal` | [x] | - | - | 99-101 | 70-71 | No |
| `kindHandled` | [x] | - | - | 104-106 | 74-75 | No |
| `kindHandled1` | [x] | - | - | 109-111 | 78-79 | No |
| `kindExtend` | [x] | - | - | 114-116 | 82-83 | No |
| `kindCon` | [x] | - | - | 119-121 | 124-125 | No |
| `kindConOver` | [x] | - | - | 123-124 | 121-122 | No |
| `kindFunN` | [x] | - | - | 127-129 | 127-128 | No |
| `kindFun` | [x] | - | - | 132-134 | 57-58 | No |
| `isKindFun` | [x] | - | - | 136-140 | 101-104 | No |
| `extractKindFun` | [x] | - | - | 143-149 | 106-113 | Yes |
| `isKindStar` | [x] | - | - | 151-153 | 86-87 | No |
| `isKindEffect` | [x] | - | - | 155-157 | 89-90 | No |
| `isKindLabel` | [x] | - | - | 159-161 | 92-93 | No |
| `isKindScope` | [x] | - | - | 163-165 | 95-96 | No |
| `isKindHeap` | [x] | - | - | 164-166 | 98-99 | No |
| `isKindHandled1` | [x] | - | - | 167-168 | 127-128 | No |
| `isKindHandled` | [x] | - | - | 170-174 | 122-125 | No |
| `isKindAnyLabel` | [x] | - | - | 179-181 | 130-131 | No |
| `builtinKinds` | [x] | - | - | 184-194 | 146-153 | No |

## Notes
- Discarded `DecidableEq` implementation in favor of `BEq` because Koka's internal generic enumerations naturally derive `BEq` over values cleanly in Lean without necessarily providing computational proofs.
- Switched generic `show n` to `toString n` to circumvent macro misinterpretations by Lean 4's type annotation syntax.
- Functions utilizing `List` and tuple folds were correctly typed and adjusted for Lean syntax.
