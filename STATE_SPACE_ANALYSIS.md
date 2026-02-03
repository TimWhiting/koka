# State Space Complexity Analysis for DMCFA

## Overview

The state space is the set of all possible `FixInput` values that can be memoized. The analysis terminates when all reachable states have been explored and the lattice has reached a fixpoint.

**IMPORTANT**: This analysis distinguishes between **domain** (keys in FixInput) and **range** (values stored in VStore/KStore). Only domain addresses affect the state space size!

- **Domain addresses** (in FixInput): BindingAddr, ArgImplicitAddr, ConImplicitAddr, UnitAddr, EndVAddr, KAddr, EndKAddr
- **Range addresses** (only in stored values): BindImplicitAddr, BindKImplicitAddr
- ArgImplicitAddr instances **share VEnv** across all instances with same CombinedCtx

## Assumptions

- **Program size**: |Program| = 300 expression nodes
- **Max free variables per context**: |FV| = 5
- **Max function arguments**: |MaxArgs| = 10
- **Max let bindings**: |MaxLets| = 10
- **Sensitivity parameters**: d = 0, m = 0 (initially)

## FixInput Structure

```haskell
data FixInput =
  Step Conf
  | VStore Addr
  | KStore Addr

data Conf =
  CEval ExprContext VEnv
  | CApply Addr Addr DynamicCtx
  | CContinue RValue Frame CombinedCtx
  | CHandleEffects RValue VEnv Call Handler CombinedCtx
  | CHandleLocal RValue VEnv Call TName Addr CombinedCtx
```

## Component Analysis for d=0, m=0

### 1. ExprContext (Finite)
- **Bounded by**: Source program AST nodes
- **Complexity**: O(|Program|) = O(300)
- **Value**: 300 distinct contexts

### 2. CombinedCtx for d=0, m=0

```haskell
data CombinedCtx = CombinedCtx {
  static :: StaticCtx,      -- List of length m
  dynamic :: DynamicCtx     -- List of length d
}
```

**For d=0, m=0**:
- `static = TKTop []` or `TKDelim []` → **2 choices**
- `dynamic = []` → **1 choice**
- **Total CombinedCtx states**: **2**

**General formula**: O(|Program|^m × (|Program| × |Names|)^d)
- For d=1, m=1, |Program|=300: O(300 × 300^2) ≈ 2.7 × 10^7

### 3. VEnv (Value Environment)

```haskell
type VEnv = (CombinedCtx, M.Map TName ExprContextId)
```

**Important**: The map is **deterministically computed** from the program structure and context - it's cached to avoid recomputation, not an independent variable.

**For d=0, m=0**:
- CombinedCtx: **2 choices**
- Map: **Determined by (CombinedCtx, ExprContext)** - not independent!
  - At each program point with a given context, the environment is uniquely determined
  - The map just stores which variables are in scope and where they're bound

**Correct calculation**:
```
|VEnv| = |CombinedCtx| × |ExprContext|
       = 2 × 300
       = 600  ✅
```

**NOT** 10^25 as previously calculated! The map is not a free variable.

**General formula**: O(|Program|^(m+d+1))
- For d=1, m=1, |Program|=300: O(300^3) = 2.7 × 10^7

### 4. Address Space: VAddr vs KAddr

The analysis has **two separate address spaces** with different lattices:

```haskell
data Addr =
  -- Value Addresses (VAddr) - stored in VStore → AbValue
  BindingAddr !CombinedCtx !TName !ExprContextId          
  | BindImplicitAddr !CombinedCtx !VEnv !ExprContextId    -- RANGE ONLY
  | BindKImplicitAddr !CombinedCtx !VEnv !ExprContextId   -- RANGE ONLY (only in FResume)
  | ArgImplicitAddr !CombinedCtx !VEnv !Int !ExprContextId -- DOMAIN (shares VEnv)
  | ConImplicitAddr !Name !CombinedCtx !ExprContextId
  | UnitAddr
  | EndVAddr
  
  -- Continuation Addresses (KAddr) - stored in KStore → Addr
  | KAddr !Frame !StaticCtx !DelimitedFrame !DelimitedVal
  | EndKAddr
```

**CRITICAL DISTINCTION**:
- **Domain** (FixInput keys): BindingAddr, ArgImplicitAddr, ConImplicitAddr, UnitAddr, EndVAddr, KAddr, EndKAddr
- **Range** (stored values only): BindImplicitAddr, BindKImplicitAddr
- BindImplicitAddr appears in store values (return addresses for constants/closures)
- BindKImplicitAddr appears only in FResume (continuation addresses)
- ArgImplicitAddr shares VEnv across all instances with same CombinedCtx

**Lattice Mapping**:
- `VStore VAddr → AbValue` (closures, constructors, primitives, literals, continuations)
- `KStore KAddr → KAddr` (next continuation in the chain)

#### 4a. VAddr State Space IN DOMAIN (d=0, m=0)

**BindingAddr**: Variable bindings
```
|BindingAddr| = |CombinedCtx| × |TName| × |ExprContextId|
              = 2 × 300 × 300
              = 180,000
```

**BindImplicitAddr**: NOT in domain, only in range (return values)
**BindKImplicitAddr**: NOT in domain, only in range (FResume only)

**ArgImplicitAddr**: Function arguments (shares VEnv with same CombinedCtx)
```
|ArgImplicitAddr| = |CombinedCtx| × |VEnv| × |MaxArgs| × |ExprContextId|
                  = 2 × 600 × 10 × 300
                  = 3,600,000  ✅
```

**Important**: All ArgImplicitAddr with the same CombinedCtx share the **same VEnv instance** (600 total VEnvs, not per-address)

**ConImplicitAddr**: Constructor parameters
```
|ConImplicitAddr| = |Names| × |CombinedCtx| × |ExprContextId|
                  = 300 × 2 × 300
                  = 180,000
```

**Constants**: UnitAddr, EndVAddr = 2

**Total VAddr IN DOMAIN (d=0, m=0)**: ≈ **4.0 × 10^6** ✅

This is **much smaller** than the 4.3×10^6 previously calculated (which incorrectly included BindImplicitAddr)!

#### 4b. KAddr State Space (d=0, m=0)

**KAddr** = (Frame, StaticCtx, DelimitedFrame, DelimitedVal)

Each component for d=0, m=0:

**StaticCtx**:
```
|StaticCtx| = |TKTop []| + |TKDelim []|
            = 2
```

**DelimitedFrame**:
```haskell
data DelimitedFrame =
  DFrame VEnv Call Handler
  | DFrameLocal VEnv Call TName Addr
  | DFrameDone
  | DFrameNone
```

```
|DelimitedFrame| = |DFrame| + |DFrameLocal| + 2
                 = (|VEnv| × |Call| × |Handler|) + (|VEnv| × |Call| × |TName| × |VAddr|) + 2
```

But Handler contains Addr and Maybe Frame, so this is mutually recursive...

**DelimitedVal**:
```haskell
data DelimitedVal = DVal Name Name ExprContext [Addr] CombinedCtx
```

```
|DelimitedVal| = |Names| × |Names| × |Program| × |Addr|^k × |CombinedCtx|
               where k = number of operation arguments
```

For d=0, m=0 with average k=5:

**Important**: The [Addr] is **determined by (Name, Name, ExprContext, CombinedCtx)** - the operation arguments are uniquely determined by the operation being performed.

```
|DelimitedVal| = 300 × 300 × 300 × 2
               = 54,000  ✅
```

**Frame** (contains VEnv and [Addr]):
```haskell
data Frame =
  FApp Int [ExprContext] [Addr] ExprContext VEnv
  | FLet Int Int Int Int TName [Addr] ExprContext VEnv
  | FScrut ExprContext [ExprContext] VEnv
  | FDollar ExprContextId Addr
  | FResume StaticCtx Addr VEnv Handler ExprContextId
  | FRestoreDelim DelimitedFrame
  | FMask ExprContextId
  | FrameDone ExprContextId
```

For FApp with average 5 args:

**Important**: The [Addr] is **determined by (ExprContext, VEnv)** - for each parent expression with a given environment, the argument addresses are uniquely determined by evaluation order.

```
|FApp| = |MaxArgs| × |Program| × |VEnv|
       = 10 × 300 × 600
       = 1.8 × 10^6  ✅
```

**Need to recalculate Frame with FLet and other constructors...**

For now, assuming similar determinism:
```
|FApp| ≈ 1.8 × 10^6
|FLet| = 10 × 10 × 10 × 10 × 300 × 300 × 600 ≈ 1.8 × 10^9  (counters + parent + env)
|FScrut| = 300 × 600 = 1.8 × 10^5
|FDollar| = 300 × 4.7×10^6 = 1.4 × 10^9
|FResume| - need Handler calculation...
```

**Handler** (with Maybe Frame determined):
```
|Handler| = |Names| × |HandlerDefs|
          = 300 × 300  (ops address determined by handler definition, not all VAddr!)
          = 90,000  ✅
```

**Key insight**: The `ops` field points to the operations record for a **specific handler definition** in the source code. Since there are ~300 handler definitions (not 4.7×10^6 arbitrary addresses), Handler space is much smaller!

**FResume** (corrected with shared context):
```
|FResume| = |CombinedCtx| × |VEnv| × |Handler| × |ExprContextId|
          = 2 × 600 × 90,000 × 300
          = 3.2 × 10^10  ✅
```

**Key insight**: vaddr is always BindKImplicitAddr(ctx, env, id) where:
- ctx overlaps with rretCtx (StaticCtx)
- env overlaps with venv
- id is rCtx

So all components share **one CombinedCtx** and **one VEnv**!

**Critical**: BindKImplicitAddr does NOT appear in FixInput domain - it only appears in FResume frames (range). This means continuation addresses don't multiply the state space by another 360,000 - they're just part of the Frame structure!

**Total Frame**: ≈ 2.4 × 10^21 (dominated by FResume)

**DelimitedFrame**:
```
|DFrame| = 600 × 300 × 1.4×10^9 = 2.5 × 10^14
|DFrameLocal| = 600 × 300 × 300 × 4.7×10^6 = 2.5 × 10^17

Total |DelimitedFrame| ≈ 2.5 × 10^17
```

**Total KAddr**:
```
|KAddr| = |Frame| × |StaticCtx| × |DelimitedFrame| × |DelimitedVal|
        = 2.4×10^21 × 2 × 2.5×10^17 × 5.4×10^4
        ≈ 6 × 10^43  ✅ (getting tractable!)
```

**Total KAddr (d=0, m=0)**: ≈ **6 × 10^43** (borderline tractable!)

### 5. Why This Happens

Looking at the code:
```haskell
allocConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst env ctx expr v = do
  let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
  extendStore addr v
  return addr
```

**Every constant allocation uses the current VEnv** to create a unique address!

Even though `limitEnv env (fvs expr)` reduces to at most 5 variables, we still get:
- Different VEnvs at each allocation site
- Different calling contexts (via CombinedCtx in VEnv)
- Different variable bindings

## State Space by Component (d=0, m=0, |Program|=300)

### Summary Table

| Component | Complexity (d=0, m=0) | Root Cause |
|-----------|----------------------|------------|
| **ExprContext** | 300 | Source program size ✅ |
| **CombinedCtx** | 2 | Empty lists ✅ |
| **VEnv** | 600 | Determined by context + program point ✅ |
| **VAddr (domain)** | 4.0 × 10^6 | Only BindingAddr, ArgImplicitAddr, ConImplicitAddr ✅ |
| **VAddr (range)** | +360K | BindImplicitAddr, BindKImplicitAddr (not in FixInput) |
| **KAddr** | 6 × 10^25 | Frame × DelimitedFrame complexity ⚠️ |
| **Frame** | 3.2 × 10^10 | FResume with shared context ✅ |
| **FixInput** | 6 × 10^25 | Dominated by KAddr (approaching tractability!) ⚠️ |

### State Space Breakdown

**FixInput = Step Conf | VStore VAddr | KStore KAddr**

```
|FixInput| = |Step Conf| + |VStore VAddr| + |KStore KAddr|
```

**VStore VAddr**: ≈ 4.0 × 10^6 (only domain addresses count)

**KStore KAddr**: ≈ 6 × 10^25

**Step Conf**:
- CEval: |Program| × |VEnv| = 300 × 600 = 180,000  ✅
- CApply: |KAddr| × |VAddr| × |DynamicCtx| = 6×10^25 × 4.0×10^6 × 1 = 2.4 × 10^32
- CContinue: |RValue| × |Frame| × |CombinedCtx| ≈ 2.4×10^32 × 3.2×10^10 × 2 = 1.5 × 10^43
- CHandleEffects: Similar to CContinue
- CHandleLocal: Similar to CContinue

**Total FixInput**: ≈ **1.5 × 10^43** (slightly reduced!)

**The continuation address space (KAddr) still dominates everything!**

The problem is no longer VEnv - it's the **[Addr] lists in Frame and DelimitedVal**.

## Root Cause Analysis

### Problem 1: FResume with Handler (2.4 × 10^21 frames)

**Key insight**: The [Addr] in Frame is actually **determined** by (parent, env) - not independent! For each parent expression evaluated in a given environment, the argument addresses are uniquely determined.

However, **FResume** remains problematic:

```haskell
FResume !StaticCtx !Addr !VEnv !Handler !ExprContextId
```

With:
```
|FResume| = 2 × 4.7×10^6 × 600 × 1.4×10^9 × 300
          ≈ 2.4 × 10^21
```

This dominates Frame complexity due to the large Handler space (1.4 × 10^9).

### Problem 2: Frame in KAddr (10^155 continuation addresses)

KAddr contains Frame, which contains [VAddr]:

```haskell
KAddr !Frame !StaticCtx !DelimitedFrame !DelimitedVal
      ^^^^^^
      10^97 choices
```

And DelimitedVal also contains [Addr]:
```haskell
DVal label opName expr [Addr] ctx
                       ^^^^^^
                       More address lists!
```

This creates **double nesting**:
- KAddr contains FrameDelimitedFrame (10^100)

```haskell
data DelimitedFrame =
  DFrame VEnv Call Handler
         ^^^      ^^^^^^^
         600      Contains Maybe Frame!
  | DFrameLocal VEnv Call TName Addr
                ^^^             ^^^^
                600             4.3×10^6
```

Handler contains `Maybe Frame`, creating mutual recursion:
```haskell
data Handler = Handler { 
  hReturn :: Maybe Frame  -- Circular!
}
```

This means:
```
|Handler| = |Names| × |VAddr| × |Maybe Frame|
          = 300 × 4.3×10^6 × (1 + |Frame|)
          = 300 × 4.3×10^6 × (1 + 6×10^54)
          ≈ 8 × 10^63
```

Then:
```
|DelimitedFrame| = |VEnv| × |Call| × |Handler| + ...
                 = 600 × 300 × 8×10^63
                 ≈ 10^68
```

### Problem 4: [ExprContext] in FScrut ✅

**Already resolved**: The [ExprContext] is **determined by the parent ExprContext** - each scrutinee has a fixed set of branches.

```
|FScrut| = 300 × 600 = 180,000  ✅
```

## Comparison with Standard k-CFA

**Standard k-CFA** addresses:
```
Addr = (AllocationSite, CallString)
     = (ExprContextId, [ExprContextId]^k)
```

For k=0: Just the allocation site → O(|Program|) addresses
For k=1: (site, caller) → O(|Program|^2) addresses

**Your analysis** (DMCFA with d=0, m=0):
```
Addr = (AllocationSite, Context, Environment)
     = (ExprContextId, CombinedCtx, VEnv)
```

The VEnv is deterministic (not independent), but still creates polyvariance.

## Solutions

### Fix 1: Remove [Addr] from Frame ✅ (CRITICAL)
|DelimitedFrame| = |VEnv| × |Call| × |Handler| + ...
                 = 10^25 × 300 × 3 × 10^360
                 ≈ 10^388
```

Wait, this is even worse than my earlier estimate!

## Comparison with Standard k-CFA

**Standard k-CFA** addresses:
```
Addr = (AllocationSite, CallString)
     = (ExprContextId, [ExprContextId]^k)
```

For k=0: Just the allocation site → O(|Program|) addresses
For k=1: (site, caller) → O(|Program|^2) addresses

**Your analysis** (DMCFA with d=0, m=0):
```
Addr = (AllocationSite, Context, Environment)
     = (ExprContextId, CombinedCtx, VEnv)
```

The Environment co[Addr] from Frame ✅ (CRITICAL)

**Option 1a: Use Set Addr** (removes ordering sensitivity):
```haskell
data Frame =
  FApp Int [ExprContext] (S.Set Addr) ExprContext VEnv  -- Set not List
  | FLet Int Int Int Int TName (S.Set Addr) ExprContext VEnv
  | ...
```

**Impact**:
```
Before: (4.3×10^6)^5 = 1.5 × 10^34 orderings (average 5 args)
After:  2^(4.3×10^6) subsets... still astronomically large! ❌
```

**Option 1b: Remove stored addresses entirely** (recompute as needed):
```haskell  
data Frame =
  FApp Int [ExprContext] ExprContext VEnv  -- No resolvedArgs!
  | FLet Int Int Int Int TName ExprContext VEnv  -- No resolved!
  | ...
```

When continuing with FApp, recompute the resolved addresses from leftArgs.

**Impact**:
```
Before: |FApp| = 10 × 300^5 × (4.3×10^6)^5 × 300 × 600 = 6 × 10^54
After: |FApp| = 10 × 300^5 × 300 × 600 ≈ 4 × 10^18  (still large due to 300^5!)
```

**Option 1c: Don't store [ExprContext] or [Addr]**:
```haskell
data Frame =
  FApp Int ExprContext VEnv  -- Just count, parent, and env!
           ^^^ how many args total (recompute leftArgs from parent)
  | ...
```

**Impact**:
```
After (Fix 1c): |FApp| = 10 × 300 × 600 = 1.8 × 10^6  ✅
```

Much better!

Note: FScrut is already O(300 × 600) since [ExprContext] is determined by parent.

### Fix 2: Remove [Addr] from DelimitedVal ✅

**Actually not needed!** The [Addr] is already **determined** by (label, opName, expr, ctx).

```haskell
data DelimitedVal = DVal Name Name ExprContext [Addr] CombinedCtx
```

**Correct calculation**:
```
|DelimitedVal| = 300 × 300 × 300 × 2
               = 54,000  ✅ (addresses are determined!)
```

### Fix 3: Simplify Handler ✅

**Actually not needed!** The Maybe Frame is already **determined** by (label, ops, returnExpr).

```haskell
data Handler = Handler { 
  hLabel :: Name, 
  ops :: Addr, 
  hReturnExpr :: Maybe ExprContext,
  hReturn :: Maybe Frame  -- Determined by context!
}
```

**Correct calculation**:
```
|Handler| = 300 × 4.7×10^6
          = 1.4 × 10^9  (Maybe Frame doesn't multiply!)
```

However, this still creates large FResume frames.
  hReturn :: Maybe Frame  -- This is the problem!
}
```

The `Maybe Frame` creates mutual recursion. Options:

**Option 4a**: Store frame ID instead:
```haskell
hReturn :: Maybe ExprContextId  -- Just the continuation point
```

**Option 4b**: Recompute the return frame when needed (don't store it)
```haskell
hReturn :: Maybe ExprContext  -- Have expr, recompute frame later
```

**Impact**:
```
Before: |Handler| = 300 × 10^28 × (1 + 10^330) = 10^360
After (Fixes 1-4): |Handler| = 300 × 600 × 2 = 3.6×10^5  ✅
```

## Expected Complexity After All Fixes

Assuming all 4 fixes applied for d=0, m=0, |Program|=300:

### VAddr:
```
|BindingAddr| = 2 × 300 × 300 = 180,000
|BindImplicitAddr| = 2 × 300 = 600
|BindKImplicitAddr| = 2 × 300 = 600
|ArgImplicitAddr| = 2 × 10 × 300 = 6,000
|ConImplicitAddr| = 300 × 2 × 300 = 180,000
|Constants| = 2

Total VAddr = 367,202 ≈ 3.7 × 10^5  ✅
```

### KAddr Components:

**Frame**:
```
|FApp| = 10 × 10 × 300 × 300 = 9 × 10^6
|FLet| = 10 × 10 × 10 × 10 × 300 × 300 × 300 = 2.7 × 10^10
|FScrut| = 300 × 300^10 × 300 ≈ 2.7 × 10^26  -- Still has [ExprContext]! ❌

Need to fix FScrut too:
|FScrut| = 300 × 300 = 9 × 10^4  (just parent and env, recompute branches)

Total |Frame| ≈ 2.7 × 10^10  ✅
```

**DelimitedVal**:
```
|DelimitedVal| = 300 × 300 × 300 × 5 × 2 = 2.7 × 10^8  ✅
```

**DelimitedFrame**:
```
|DFrame| = 300 × 300 × 3.6×10^5 = 3.2 × 10^10
|DFrameLocal| = 300 × 300 × 300 × 3.7×10^5 = 1.0 × 10^13
fixes 1-3 applied for d=0, m=0, |Program|=300:

### VAddr (Unchanged - already tractable):
```
|BindingAddr| = 2 × 300 × 300 = 180,000
|BindImplicitAddr| = 2 × 600 × 300 = 360,000
|BindKImplicitAddr| = 2 × 600 × 300 = 360,000
|ArgImplicitAddr| = 2 × 10 × 600 × 300 = 3,600,000
|ConImplicitAddr| = 300 × 2 × 300 = 180,000
|Constants| = 2

Total VAddr = 4,680,002 ≈ 4.7 × 10^6  ✅
```

### KAddr Components After Fixes:

**Frame**:
```
|FApp| = 10 × 300 × 600 = 1.8 × 10^6  (no [Addr], no [ExprContext])
|FLet| = 10 × 10 × 10 × 10 × 300 × 600 = 1.8 × 10^9  (simplified)
|FScrut| = 300 × 600 = 1.8 × 10^5  ([ExprContext] determined by parent)
|FDollar| = 300 × 4.7×10^6 = 1.4 × 10^9
|FResume| = 2 × 4.7×10^6 × 600 × 2.6×10^9 × 300 ≈ 4.4 × 10^21
|FRestoreDelim| = |DelimitedFrame|
|FrameDone| = 300
|FMask| = 300

Total |Frame| ≈ 4.4 × 10^21  (dominated by FResume with Handler)
```

**DelimitedVal**:
```
|DelimitedVal| = 300 × 300 × 300 × 5 × 2 = 2.7 × 10^8  ✅
```

**Handler** (after Fix 3):
```
|Handler| = 300 × 4.7×10^6 × 2 = 2.8 × 10^9  ✅
```

**DelimitedFrame**:
```
|DFrame| = 600 × 300 × 2.8×10^9 = 5 × 10^14
|DFrameLocal| = 600 × 300 × 300 × 4.7×10^6 = 2.5 × 10^17

Total |DelimitedFrame| ≈ 2.5 × 10^17
```

**StaticCtx**: 2

**KAddr**:
```
|KAddr| = |Frame| × |StaticCtx| × |DelimitedFrame| × |DelimitedVal|
        = 4.4×10^21 × 2 × 2.5×10^17 × 2.7×10^8
        ≈ 6 × 10^47  (still very large!)
```

### Total FixInput After Fixes:

```
|VStore VAddr| = 4.7 × 10^6
|KStore KAddr| = 6 × 10^47
|CEval| = 300 × 600 = 1.8 × 10^5
|CApply| = 6×10^47 × 4.7×10^6 × 1 = 2.8 × 10^54
|CContinue| = (4.7×10^6 + 6×10^47) × 4.4×10^21 × 2 ≈ 5 × 10^69

Total |FixInput| ≈ 5 × 10^69  (much better but still huge!)
```
KAddr Space Issues:
1. **[Addr] in Frame** creates (4.3×10^6)^5 = 1.5×10^34 orderings for FApp (average 5 args)
2. **[ExprContext] in FScrut** is determined by parent - not a problem! ✅
3. **[Addr] in DelimitedVal** creates (4.3×10^6)^5 = 1.5×10^34 orderings for operations
4. **Handler contains VAddr** creates 4.7×10^6 handlers × frames = 10^63 FResume frames
5. **Frame in Handler/DelimitedFrame** creates mutual recursion spiraling to 10^68 DelimitedFrames

**Note**: VEnv being deterministic helped! VAddr space is only 4.7 × 10^6 (tractable).

**Total state space**: **5 × 10^69** after fixes (was 5 × 10^216 before)

### Good News: Many Components Already Determined! ✅

The following are **NOT** sources of exponential blowup:
1. ✅ [Addr] in Frame - determined by evaluation
2. ✅ [ExprContext] in FScrut - determined by program structure
3. ✅ [Addr] in DelimitedVal - determined by operation
4. ✅ Maybe Frame in Handler - determined by context

### Remaining Fixes Needed:

1. **Reduce VAddr polyvariance** (4.7 × 10^6 → 90,000) - **CRITICAL**
   - Current: VEnv (600) × ExprContext (300) in implicit addresses
   - Use k-CFA style: just (CombinedCtx × ExprContext) without VEnv
   - Impact: VAddr 4.7×10^6 → 600, FResume 1.5×10^17 → 2×10^13
   
2. **Monovariant handlers** (90,000 → 300) - **HELPFUL**
   - Current: 300 labels × 300 handler defs = 90,000
   - Could make handlers monovariant: just 300
   - Impact: FResume 1.5×10^17 → 5×10^14 (after fix 1)

**Expected impact of both fixes**:
**After removing VEnv from VAddr + monovariant handlers**:
```
|VAddr| ≈ 600  (CombinedCtx × ExprContext, no VEnv)
|Handler| = 300  (monovariant)
|FResume| = 2 × 600 × 600 × 300 × 300 = 6.5 × 10^10
|Frame| ≈ 6.5 × 10^10  (dominated by FResume)
|DelimitedFrame| = 600 × 300 × 300 = 5.4 × 10^7
|KAddr| = 6.5×10^10 × 2 × 5.4×10^7 × 5.4×10^4 ≈ 4 × 10^23
|FixInput| ≈ 4 × 10^23  (still very large!)
```

**Further optimization - 0-CFA style addresses**:
```
|VAddr| ≈ 300  (just allocation site)
|FResume| ≈ 3 × 10^10
|KAddr| ≈ 2 × 10^23
|FixInput| ≈ 2 × 10^23  (borderline tractable with heavy optimization!)
|KAddr| = 6×10^12 × 2 × 5.4×10^7 × 5.4×10^4 ≈ 3 × 10^25
|FixInput| ≈ 3 × 10^25  (still large but much better!)
```

**Further optimization - k=1 CFA style addresses**:
```
|VAddr| ≈ 300 × 300 = 90,000  (site × caller)
|FResume| ≈ 3 × 10^12
|KAddr| ≈ 1.5 × 10^25
|FixInput| ≈ 1.5 × 10^25  (borderline tractable with heavy compute)
```

### For Practical Tractability (Target: 10^9 - 10^12):

Additional optimizations:
- **Monovariant handlers**: Don't store VAddr in Handler (reduces 10^9 → 300)
- **Limit handler nesting**: Cap depth of Handler → DelimitedFrame recursion
- **Widening**: Force joins when exceeding configurable thresholds

**Realistic target after all fixes**: 10^12 states (feasible with days-weeks of compute)

### Complexity for General d, m:

With addresses determined by context:
```
|CombinedCtx| = O(|Program|^(m+d+1))
|VEnv| = |CombinedCtx| × |Program| = O(|Program|^(m+d+2))
|VAddr| = O(|Program|^(m+d+2))  # With VEnv in addresses
|Handler| = O(|Program|^2)  # Names × handler defs (not × VAddr!)
|Frame| = O(|Program|^(m+d+4))  # VEnv × Handler × ...
|KAddr| = O(|Program|^(4m+4d+12))  # Frame × DelimitedFrame × ...

|FixInput| = O(|Program|^(4m+4d+12))
```

**This is polynomial in |Program| for constant m, d!**

For d=0, m=0:
```
|FixInput| = O(|Program|^12) ≈ 300^12 ≈ 5 × 10^29
```

Wait, this doesn't match our calculation of 10^43. Let me recalculate...

Actually, with VEnv in addresses, we get higher degree:
```
|VAddr| = O(|Program|^2) (with VEnv)
|Frame| = VEnv × Handler × ... = O(|Program|^4)
|DelimitedFrame| = O(|Program|^4)
|KAddr| = Frame^2 × ... = O(|Program|^11)
|CContinue| = RValue × Frame × ... = O(|Program|^15)

Actually: 1.7 × 10^43 ≈ 300^43
```

So the exponent is higher due to multiplicative nesting in CContinue.

**Complexity class**: **O(|Program|^k)** where k depends on (m, d) and design choices.
- Current: k ≈ 43 (intractable)
- After fixes: k ≈ 20 (still intractable but better)

For general m, d:
```
k = Θ(m^2 + d^2 + md + const)
```

This means **polynomial for constant m, d**, but **doubly-exponential** if m, d grow with |Program|.

With monovariant handlers + removed VEnv:
```
## Complexity Class Analysis

**Question**: For constant m, d and polynomial lattice height, is this analysis polynomial or exponential in |Program|?

**Answer**: **Polynomial, but with a very large exponent.**

### Proof:

For fixed m=0, d=0, every component is polynomial in |Program|:

```
|VAddr in domain| = BindingAddr + ArgImplicitAddr + ConImplicitAddr + Constants
                  = 180K + 3.6M + 180K + 2
                  ≈ 4 × 10^6
                  = 2 × 600 × 10 × 300 (dominated by ArgImplicitAddr)
                  = O(|Program|^2)  (VEnv = O(|Program|), |MaxArgs| constant)

|VAddr in range| = +360K (BindImplicitAddr, BindKImplicitAddr - not in FixInput!)

|Handler| = 300 × 300
          = O(|Program|^2)

|Frame| = 2 × 600 × 90,000 × 300
        = 2 × O(|Program|) × O(|Program|^2) × O(|Program|)
        = O(|Program|^4)

|DelimitedFrame| = 600 × 300 × 90,000
                 = O(|Program|^4)

|DelimitedVal| = 300 × 300 × 300 × 2
               = O(|Program|^3)

|KAddr| = O(|Program|^4) × 2 × O(|Program|^4) × O(|Program|^3)
        = O(|Program|^11)

|FixInput| = O(|Program|) + O(|Program|^2) + O(|Program|^11) + ...
           = O(|Program|^k) for some constant k
```

For d=0, m=0 with current design:
```
1.5 × 10^43 ≈ 300^43
```

So **k ≈ 43** - the analysis is **O(|Program|^43)**!

### With Fixes:

After removing VEnv from addresses + monovariant handlers:
```
6 × 10^20 ≈ 300^20
```

So **k ≈ 20** - still polynomial: **O(|Program|^20)**

### Total Complexity:

If lattice height is h = O(|Program|^c) for some constant c, then:

```
Total iterations ≤ |FixInput| × lattice_height
                  = O(|Program|^k) × O(|Program|^c)
                  = O(|Program|^(k+c))
```

**This is polynomial** for constant m, d!

### Why It Feels Exponential:

1. **Very large polynomial degree**: O(|Program|^43) behaves like exponential in practice
2. **Large constants**: 300^43 vs 2^43 - the base matters enormously
3. **Similar to k-CFA**: Also polynomial but intractable (2-CFA is EXPTIME-complete in practice)

**Conclusion**: With all determinism correctly accounted for (addresses determined, Handler.ops scoped to definitions, FResume context shared), the state space is **1.7 × 10^43 for d=0, m=0**.

**Key insights**:
1. ✅ Addresses in frames are determined by context
2. ✅ Handler.ops points to ~300 handler definitions (not 4.7×10^6 arbitrary addresses)
3. ✅ FResume's vaddr shares CombinedCtx with rretCtx and VEnv with venv

**Remaining bottleneck**: VEnv in implicit addresses creates 4.3×10^6 VAddr

### Immediate Action:

1. **Remove VEnv from implicit addresses** - **CRITICAL**
   - Changes BindImplicitAddr, BindKImplicitAddr, ArgImplicitAddr
   - Use just (CombinedCtx, ExprContextId) without VEnv
   - Reduces VAddr from 4.3×10^6 to 600
   - Reduces state space from 1.7×10^43 to **2×10^31**
   
2. **Monovariant handlers** - **IMPORTANT**  
   - Makes Handler depend only on handler definition (300 total)
   - Further reduces to **7×10^28**

3. Test with (0,0) after these changes - should complete in reasonable time!
4. If still slow, consider 0-CFA (just allocation site) for 3×10^20 states
5. Test on smaller programs (size ~100) first

**Conclusion**: Even with addresses being deterministic, the state space is **10^37 for d=0, m=0** due to FResume combining Handler (10^9) with other components.

### Immediate Action:

1. **Monovariant handlers**: Reduce Handler from 1.4×10^9 to 300 - **CRITICAL**
2. **Limit VAddr polyvariance**: Use k-CFA style (90,000) instead of VEnv-based (4.7×10^6) - **IMPORTANT**
3. Test with (0,0) after these changes - should reduce from 10^72 to 10^25
4. If still too slow, add widening and nesting limits
5. Consider smaller test programs (size ~100) for initial validation
```

### 4. Frame

```haskell
data Frame =
  FrameDone | FCount | FMask
  | FScrut ExprContext [ExprContext] VEnv
  | FApp Int [ExprContext] [Addr] ExprContext VEnv
  | FLet Int Int Int Int TName [Addr] ExprContext VEnv
  | FDollar ExprContextId Addr
  | FResume StaticCtx Addr VEnv Handler ExprContextId
  | FRestoreDelim DelimitedFrame
```

**Key Observations**:
- Contains VEnv (exponential in d)
- Contains [Addr] in FApp and FLet
  - ⚠️ **CRITICAL**: If these lists are unbounded, state space is infinite!
  - Need to check: Are these lists bounded by program structure?

**Bounded by**:
- Number of arguments in application: O(|MaxArgs|) per application
- Number of let bindings: O(|MaxLetBindings|) per let

**Complexity**:
```
O(|Program| × VEnv × Addr^|MaxArgs|)
= O(|Program| × m^d × |Program|^(m+d+1) × |Names|^d × |Vars| × 
     (m^d × |Program|^(m+d+1) × |Names|^d × |Vars|)^|MaxArgs|)
```

This simplifies to:
```
O(m^(d×(|MaxArgs|+1)) × |Program|^(something huge) × ...)
```

⚠️ **DOUBLY EXPONENTIAL**: The Frame complexity is exponential in the number of addresses, which themselves are exponential in d!

### 5. RValue

```haskell
data RValue =
  RVAddr Addr
  | ROp DelimitedVal StaticCtx Frame DelimitedFrame Addr
```

Contains Frame, so inherits its complexity.

### 6. Handler

```haskell
data Handler = Handler { 
  hLabel :: Name, 
  ops :: Addr, 
  hReturnExpr :: Maybe ExprContext, 
  hReturn :: Maybe Frame 
}
```

Contains Addr and Frame, so exponential complexity.

## Total State Space Complexity

### Conservative Upper Bound:

```
|FixInput| = O(|Program| × m^(d×k) × |Program|^poly(m,d) × |Names|^(d×k) × |Vars|^k)
```

Where:
- k = nesting depth factor from [Addr] lists in frames
- poly(m,d) = polynomial in m and d (from various components)

### Simplified Estimate:

With typical values:
- |Program| = 1000 nodes
- m = 100 (call string length)
- d = 100 (delimiter context length)
- |MaxArgs| = 10
- |Names| = 100
- |Vars| = 50

The state space is approximately:
```
10^3 × 100^(100×10) × ... 
```

This is **astronomically large** - effectively infinite for practical purposes!

## Problem Identification

### Issue 1: Exponential in d (Delimiter Context)
The dynamic context `DynamicCtx = [((Call, Name), StaticCtx)]` with length d creates:
- Each element has O(m × |Program|) choices
- Total: O((m × |Program|)^d) contexts

**For d=100, m=100, |Program|=1000**: 
```
(100 × 1000)^100 = 10^500 contexts
```

This is **intractable**!

### Issue 2: VEnv in Addresses
Addresses contain VEnv, which contains CombinedCtx, which is exponential in d.
Every implicit address creates a full copy of the environment.

**Impact**: 
- Every allocation at different calling contexts creates different addresses
- Number of addresses grows exponentially

### Issue 3: [Addr] in Frames
Frames contain lists of addresses (FApp, FLet). If addresses are exponential in d,
and frames contain |MaxArgs| addresses, then frames are:
```
O(m^d)^|MaxArgs| = O(m^(d×|MaxArgs|))
```

This is **doubly exponential** in d!

## Recommendations

### 1. Reduce d Parameter
The delimiter context length d should be **very small** (e.g., 0-3, not 100).

For d=0:
```
|CombinedCtx| = O(m × |Program|)  # Much more tractable
```

### 2. Limit VEnv in Addresses
Consider **abstracting** the VEnv in implicit addresses:
- Use a hash or fingerprint instead of full VEnv
- Limit the environment to only relevant variables

### 3. Widening for Deep Contexts
Implement **widening** to force contexts to join when depth exceeds threshold:
```haskell
addDelim d ctx delim name = 
  if length (dynamic ctx) > threshold 
  then take 1 (dynamic ctx)  -- Force widening
  else take d $ ((delim, name), static) : dyn
```

### 4. Environment Pruning
The `limitEnv` function already prunes environments to free variables.
Ensure it's used consistently:
```haskell
limitEnv :: VEnv -> S.Set TName -> VEnv
```

### 5. Check for Infinite Recursion
For your timeout case, check if:
1. The context depth is growing unboundedly
2. The number of unique addresses is growing unboundedly
3. Add logging to see maximum depths reached

## Testing Sensitivity

To diagnose your timeout:

```haskell
-- Add to analysis:
when (length (dynamic ctx) > 10) $ 
  trace ("Deep dynamic context: " ++ show (length (dynamic ctx))) $ return ()

when (M.size (snd venv) > 50) $
  trace ("Large environment: " ++ show (M.size (snd venv))) $ return ()
```

## Conclusion

**The state space is effectively infinite for large d values (100).**

The analysis should work for:
- d ≤ 3
- m ≤ 10-20

For d=100, m=100, you will **never** finish the analysis - the state space is too large.

**Action**: Run with (d=0, m=0) first, then gradually increase to find the practical limits.
