# Faithfulness Audit: Bauer & Pretnar (B&P) Big-Step Semantics

This document checks, rule by rule, that the locally-nameless Lean
formalization of the source (Bauer–Pretnar) calculus
(`DMCFA/LNBPSemantics.lean`, `DMCFA/LNBPSyntax.lean`) faithfully represents the
**big-step** semantics of core Eff.

**Paper source.** Bauer & Pretnar, *An Effect System for Algebraic Effects and
Handlers* (2014), §2 (syntax) and §3.2 (big-step semantics `c ⇓ r`).
(`~/research/dmcfa/papers/Bauer and Pretnar - 2014 - ...pdf`.)

**Substitution vs. opening.** B&P is substitution-based and named: a rule like
`c[e/x] ⇓ r` substitutes `e` for the binder `x`. The Lean version is locally
nameless: the innermost binder is `bvar 0`, so `c[e/x] = c.open_ e`
(`= compOpenRec 0 e c`). A computation that binds *two* variables
(`x` and `k` in an operation case) is instantiated with two openings,
`compOpenRec 0 e (compOpenRec 1 k' c)`. This is a change of representation only.

---

## Part 1 — Syntax

B&P §2 vs. `LNBPSyntax.lean` (`Expr`, `Comp`, `BPHandler`, `Result`):

**Expressions** `e ::= x | () | true | false | succ e | fun x ↦ c | ι | h`
```lean
inductive Expr | bvar (Nat) | fvar (Var) | true_ | false_ | unit | zero | succ (Expr) | lam (Comp)
```
- variable `x` → `bvar`/`fvar`; constants → `true_/false_/unit/zero/succ`;
  `fun x ↦ c` → `lam c` (binds 1, the parameter = `bvar 0`). ✓
- Effect instances `ι` and first-class handlers `h` are **not** separate
  expression forms (see §4): operations are named directly, and a handler
  appears only inside `withHandle`.

**Handler** `h ::= (handler val x ↦ cv | ocs)`,
  `ocs ::= nilC | (e#op x k ↦ c | ocs)`
```lean
structure BPHandler := (returnClause : Comp) (opClauses : List (OpName × Comp))
```
- value case `val x ↦ cv` → `returnClause` (binds 1, the returned value
  = `bvar 0`).
- each operation case **`op x k ↦ c` binds two**, the parameter `x` and the
  continuation `k` → each `(op, c) ∈ opClauses` has `c` binding 2
  (`bvar 0 = x`, `bvar 1 = k`/`resume`). ✓ (This is what licenses treating
  `resume` as an ordinary binder.)

**Computations** `c ::= val e | e1 #op e2 (y.c) | if e then c1 else c2 |
  with e handle c | absurdC e | e1 e2 | match e with 0 ↦ c1 | succ x ↦ c2 |
  let x = c1 in c2 | let rec f x = c1 in c2`
```lean
inductive Comp | val | app | letIn | letRec | ifThenElse | matchNat | withHandle | opCall
```
- `val e`→`val`, `e1 e2`→`app`, `let`→`letIn`, `let rec`→`letRec`,
  `if`→`ifThenElse`, `match`→`matchNat`, `with h handle c`→`withHandle`,
  operation call→`opCall` (generic-effect form; see §4). ✓
- `absurdC e` (eliminator for the empty type) is not modeled — irrelevant to
  effects.

**Results** `r ::= val e | ι#op e (x.c)`
```lean
inductive Result | value (Expr) | op (OpName) (Expr) (Comp)
```
- `val e`→`Result.value e`; `ι#op e (x.c)`→`Result.op op e c_op`, where the
  delimited continuation `(x.c)` is the 1-hole computation `c_op`
  (`bvar 0 = x`, the value the suspended computation resumes with). ✓

---

## Part 2 — Big-step rules `c ⇓ r`

Each B&P rule (§3.2) and its Lean constructor in `LNBPSemantics.Eval`
(the height-indexed `EvalN` is identical up to the explicit `Nat`).

**val**
```
─────────────────
val e ⇓ val e
```
```lean
| val : Eval (Comp.val e) (Result.value e)
```
**✓**

**if-true / if-false**
```
c1 ⇓ r                                  c2 ⇓ r
────────────────────────────   ────────────────────────────
if true then c1 else c2 ⇓ r     if false then c1 else c2 ⇓ r
```
```lean
| if_true  : Eval c1 r → Eval (Comp.ifThenElse Expr.true_  c1 c2) r
| if_false : Eval c2 r → Eval (Comp.ifThenElse Expr.false_ c1 c2) r
```
**✓**

**match-zero / match-succ**
```
c1 ⇓ r                                         c2[e/x] ⇓ r
──────────────────────────────────   ───────────────────────────────────────
(match 0 with 0↦c1 | succ x↦c2) ⇓ r   (match succ e with 0↦c1 | succ x↦c2) ⇓ r
```
```lean
| match_zero : Eval c1 r → Eval (Comp.matchNat Expr.zero c1 c2) r
| match_succ : Eval (c2.open_ e') r → Eval (Comp.matchNat (Expr.succ e') c1 c2) r
```
**✓** `c2[e/x]` = `c2.open_ e'` (the `succ` binder = `bvar 0`).

**app (β)**
```
c[e/x] ⇓ r
────────────────────
(fun x ↦ c) e ⇓ r
```
```lean
| app_lam : Eval (cbody.open_ e_arg) r → Eval (Comp.app (Expr.lam cbody) e_arg) r
```
**✓** `c[e/x]` = `cbody.open_ e_arg`.

**op-call** (operation call evaluates to itself; here the generic effect `op e`)
```
─────────────────────────────────
ι#op e (x.c) ⇓ ι#op e (x.c)
```
```lean
| op_call : Eval (Comp.opCall op e) (Result.op op e (Comp.val (Expr.bvar 0)))
```
**✓** Source operation calls are generic effects `op e = e#op e (y. val y)`,
whose continuation is the trivial `(y. val y)` = `val (bvar 0)`. The general
form `ι#op e (x.c)` is recovered by `let y = op e in c` via **let-op** below.
See §4.

**let-op** (propagate an operation through a let, extending the continuation)
```
c1 ⇓ ι#op e (y. c)
──────────────────────────────────────────────────
let x = c1 in c2 ⇓ ι#op e (y. let x = c in c2)
```
```lean
| let_op :
    Eval c1 (Result.op op e_op c_op) →
    Eval (Comp.letIn c1 c2) (Result.op op e_op (Comp.letIn c_op c2))
```
**✓** the continuation `(y. c)` = `c_op` (1-hole, `bvar 0 = y`) becomes
`(y. let x = c in c2)` = `letIn c_op c2`. (`x` = `bvar 0` in `c2`, one binder
deeper, so resuming `letIn c_op c2` with `v` runs `c_op[v]` and binds the result
to `x` in `c2`.)

**let-val**
```
c1 ⇓ val e      c2[e/x] ⇓ r
──────────────────────────────
let x = c1 in c2 ⇓ r
```
```lean
| let_val :
    Eval c1 (Result.value e') →
    Eval (c2.open_ e') r →
    Eval (Comp.letIn c1 c2) r
```
**✓** `c2[e/x]` = `c2.open_ e'`.

**let-rec**
```
c2[(fun x ↦ let rec f x = c1 in c1)/f] ⇓ r
──────────────────────────────────────────
let rec f x = c1 in c2 ⇓ r
```
```lean
| let_rec :
    Eval (c2.open_ (Expr.lam (Comp.letRec c1 c1))) r →
    Eval (Comp.letRec c1 c2) r
```
**✓** the recursive value `fun x ↦ let rec f x = c1 in c1` is encoded as
`lam (letRec c1 c1)` and substituted for `f` (= `bvar 0` in `c2`), i.e.
`c2.open_ (lam (letRec c1 c1))`. (Standard locally-nameless recursive-closure
encoding: the `letRec` body `c1` binds the parameter and the recursive name.)

**handle-return** (the value case `val x ↦ cv`)
```
c ⇓ val e      cv[e/x] ⇓ r
───────────────────────────────────────────────
with (handler val x ↦ cv | ocs) handle c ⇓ r
```
```lean
| handle_val :
    Eval c (Result.value e') →
    Eval (h.returnClause.open_ e') r →
    Eval (Comp.withHandle h c) r
```
**✓** `cv` = `h.returnClause`; `cv[e/x]` = `h.returnClause.open_ e'`.

**handle-op** (an operation handled by the matching clause `op x k ↦ c_op`)
```
h = (handler val x ↦ cv | ocs)
c ⇓ ι#op e (y. c')
ocs_{ι#op}( e, (fun y ↦ with h handle c') ) ⇓ r
─────────────────────────────────────────────────
with h handle c ⇓ r
```
where `ocs_{ι#op}(e, k) = c_op[e/x, k/k']` for the clause `ι#op x k' ↦ c_op`
(informal §3: "`ci` with `xi` and `ki` bound to `e'` and
`fun y ↦ with h handle c'`").
```lean
| handle_op :
    Eval c (Result.op op e_op c_op) →
    h.findOp op = some c_h →
    Eval (compOpenRec 0 e_op
          (compOpenRec 1 (Expr.lam (Comp.withHandle h c_op)) c_h)) r →
    Eval (Comp.withHandle h c) r
```
**✓** `c ⇓ ι#op e (y.c')` = `Eval c (Result.op op e_op c_op)`
(`e = e_op`, `(y.c')` = `c_op`); `h.findOp op = some c_h` finds the clause body
`c_op` (here `c_h`), which binds the parameter `x` (`bvar 0`) and the
continuation `k`/`resume` (`bvar 1`). The two substitutions
`c_h[e/x, (fun y ↦ with h handle c')/k]` are the two openings:
`compOpenRec 0 e_op (·)` instantiates the parameter `x`, and
`compOpenRec 1 (lam (withHandle h c_op)) c_h` instantiates `k` with the
resumption `fun y ↦ with h handle c'` = `lam (withHandle h c_op)`. The handler
`h` wraps the captured continuation `c_op`, so subsequent operations are handled
too (deep handlers). ✓

**handle-forward** (operation *not* listed by the handler; B&P informal §3(3),
the implicit default clause `ι#op x k ↦ ι#op x (y. k y)`)
```
c ⇓ ι#op e' (y. c')      ι#op ∉ h
──────────────────────────────────────────
with h handle c ⇓ ι#op e' (y. with h handle c')
```
```lean
| handle_forward :
    Eval c (Result.op op e_op c_op) →
    h.hasOp op = false →
    Eval (Comp.withHandle h c) (Result.op op e_op (Comp.withHandle h c_op))
```
**✓** when `op ∉ h` (`hasOp op = false`), the call is re-raised with the
handler wrapped around the continuation: `ι#op e' (y. with h handle c')` =
`Result.op op e_op (withHandle h c_op)`. This is B&P's forwarding default made
into an explicit rule (rather than an implicit clause in `ocs_{ι#op}`).

---

## Part 3 — Intentional modeling specializations (faithful)

These pre-date the locally-nameless rework and restrict B&P's general calculus
without changing rule meaning on the modeled fragment.

1. **Generic effects + `let` instead of explicit operation calls.** The source
   has only generic effect calls `op e` (`= e#op e (y. val y)`); the general
   call `e1 #op e2 (y. c)` is `let y = e1 #op e2 in c`, exactly as B&P note
   ("A general operation call … may then be expressed in terms of a generic
   effect and a let binding"). So **op-call** produces the trivial continuation
   and **let-op** builds up arbitrary continuations.

2. **Operations named directly; handlers only in `withHandle`.** We drop B&P's
   first-class effect *instances* `ι` and first-class *handlers* as expression
   forms: operations are identified by `OpName`, and a `BPHandler` occurs only
   as the first argument of `withHandle`. This matches our ANF target, which is
   likewise instance-free and uses syntactic handlers.

3. **Single operation argument.** Operation calls/clauses carry one parameter
   (`op e`, result `#op e c`, clause body binds `x` + `resume`), matching the
   ANF side. (B&P operation cases are single-parameter as well: `op x k ↦ c`.)

4. **Ground-type constructor set.** Booleans (`true/false`), `unit`, and the
   naturals (`zero`/`succ`, with `match … with 0 | succ x`) are modeled;
   `absurdC` is omitted.

## Conclusion

Every rule of B&P's big-step semantics (§3.2) — `val`, `if-true`, `if-false`,
`match-zero`, `match-succ`, β/`app`, the operation call, `let-op`, `let-val`,
`let-rec`, `handle-return`, `handle-op`, and the forwarding case — corresponds
to exactly one Lean constructor with matching premises and conclusion, modulo
the locally-nameless representation of binders (substitution `c[e/x]` rendered
as opening `c.open_ e`) and the four faithful specializations in §3. In
particular, B&P's operation cases `op x k ↦ c` already bind both the parameter
and the continuation, so the locally-nameless `handle-op` — which opens `bvar 0`
with the argument and `bvar 1` with the resumption `fun y ↦ with h handle c'` —
is a direct transcription of `c[e/x, (fun y ↦ with h handle c')/k]`, with the
handler wrapped around the continuation to realize deep handlers.
