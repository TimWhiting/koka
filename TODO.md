# Monadic Optimization Progress

## Latest Status: WORKING! 🎉
Successfully finding and applying annotations, though not all analysis contexts matched yet.

### Test Results (analysis/test/opt-yield-always.kk)
- **Analysis found**: 9 alwaysMon + 42 neverMon = 51 contexts
- **Optimization matched**: 2 alwaysMon + 5 neverMon = **7 annotations applied**
- **Match rate**: 13.7% (7/51)

### Successfully Matched Paths
✓ Direct function body expressions:
- `.../yield -> LamB([item]) (App)` - alwaysMon
- `.../flip -> LamB([]) (App)` - alwaysMon  
- `.../#yield/@tag` - neverMon
- `.../#flip/@tag` - neverMon
- `.../#flip/@handle -> LamB([hnd,ret,action]) (App)` - neverMon
- `.../amb -> LamB([@action]) (App)` - neverMon
- `.../example4 -> LamB([]) (App)` - neverMon

### Missing Matches (44 contexts)
Most involve deeper nesting that current traversal doesn't reach:
- `-> AppP1 -> LamB([]) (App)` - Lambda expressions passed as arguments
- `-> LtD _ -> CaseM (App)` - Let-bound definitions with case expressions
- Multiple levels of nested applications and let bindings

## Implementation Summary

### Core.EffOpt Module
**Key Functions**:
- `opt`: Entry point, preprocesses cache using ppContextPath
- `preprocessCache`: Converts FixInput/FixOutput to Text-keyed ExprContext maps  
- `optDefGroup/optDef/optExpr`: Recursive traversal building shadow contexts
- `optLetGroups`: Mirrors Monad.hs makeGroups for nested Let structure
- `annotate`: Matches ppContextPath, wraps with nameAlwaysMon/nameNeverMon

**Integration**: Build.hs line 442, only for root module with `--dmcfar` flag

## Next Priority: Deeper Traversal

**Problem**: Analysis creates contexts like `.../example4 -> LamB([]) -> AppP1 -> LamB([])` for nested lambda arguments, but our current traversal only goes one level deep into App expressions.

**Solution Options**:
1. In `optExpr` App case, recursively create contexts for non-trivial argument expressions (Lam, Let, Case)
2. Create intermediate contexts for each sub-expression before optimizing
3. Match analysis traversal order more precisely (depth-first with explicit intermediate nodes)

## Completed
- ✅ Core.EffOpt module with shadow ExprContext tracking
- ✅ Build.hs integration with forced evaluation
- ✅ Preprocessed cache using ppContextPath for Text-based matching
- ✅ Nested DefGroup structure (optLetGroups mirrors makeGroups)
- ✅ Successfully finding and applying 7 annotations

## Pending
- 🔧 Deeper traversal to match nested analysis contexts (AppP1 -> LamB, etc)
- Core.Monadic updates to consume nameAlwaysMon/nameNeverMon
- Testing optimized code correctness and performance
- Remove debug traces for production 