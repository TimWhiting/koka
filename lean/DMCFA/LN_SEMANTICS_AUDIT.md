# Faithfulness Audit: ANF Concrete Big-Step Semantics

This document checks, rule by rule, that the locally-nameless Lean formalization
of our concrete ANF machine (`DMCFA/LNSemantics.lean`, `DMCFA/LNComponents.lean`,
`DMCFA/LNSyntax.lean`) faithfully represents the big-step semantics in the paper.

**Paper sources** (`~/research/dmcfa/tables/handlers/`):
- `anf-syntaxh.mdk` — ANF syntax
- `big-steph-components.mdk` — runtime components
- `big-steph-value.mdk` — the `A` (atomic-value) meta-function
- `big-steph.mdk` — the big-step rules (`⇓e`, `⇓ec`, `⇒c`, `⇓h`, `⇓a`)

**Locally-nameless convention.** The paper uses named variables and an
environment `ρ : Var → VAddr`. The Lean version is locally nameless: every
binder is a de Bruijn index and `Env` is an *address stack*, so `ρ[x ↦ a]`
becomes `ρ.push a` (`x` = `bvar 0`) and `ρ(x)` becomes `ρ.lookup i`. A named
binding `ρ[x ↦ a, y ↦ b]` with `x` innermost is `(ρ.push b).push a`. This is a
change of representation only; the correspondence is noted per rule.

---

## Part 1 — Runtime components

| Paper (`big-steph-components.mdk`) | Lean (`LNComponents.lean`) | Notes |
|---|---|---|
| `VAddr` = an infinite set | `abbrev VAddr := Nat` | infinite ✓ |
| `Store ::= VAddr → Denotable` | `abbrev Store := VAddr → Option Denotable` | partiality via `Option` ✓ |
| `Env ::= Var → VAddr` | `structure Env := (stack : List VAddr)` | **LN re-encoding**: named map → de Bruijn stack |
| `Closure ::= Var* × Exp × Env` | `structure Closure := (body : Exp) (env : Env) (selfAddr : Option VAddr)` | param names are positional; `selfAddr` carries the recursive self-address (see [eval-fun]) |
| `Frame ::= LetFrame ∣ Handler × Env` | `inductive Frame := letFrame (Exp×Env) ∣ handlerFrame (Handler×Env)` | `LetFrame`'s bound `Var` is positional ✓ |
| `LetFrame ::= Var × Exp × Env` | `Frame.letFrame : Exp → Env → Frame` | ✓ |
| `Kont ::= Frame*` | `abbrev Kont := List Frame` | ✓ |
| `Denotable ::= Closure ∣ Handler × Env × Kont ∣ ConLabel × VAddr*` | `inductive Denotable := closure ∣ kontClosure (Handler×Env×Kont) ∣ conLabel (ConLabel) ∣ succVal (VAddr)` | `ConLabel × VAddr*` is **specialized** to the nullary constructors (`conLabel`) and the unary successor (`succVal a`); see §4 |
| `Value ::= OpName × VAddr* × Kont ∣ Denotable` | `inductive Value := suspended (OpName × List VAddr × Kont) ∣ den (Denotable)` | ✓ |

---

## Part 2 — The `A` meta-function

Paper (`big-steph-value.mdk`), `A : AExp × Env × Store → Denotable`, vs.
Lean `evalAtomic : AExp → Env → Store → Option Denotable`:

| Paper | Lean (`LNSemantics.evalAtomic`) | Verdict |
|---|---|---|
| `A(x, ρ, σ) = σ(ρ(x))` | `\| .bvar i => do let a ← ρ.lookup i; σ a` | ✓ `ρ(x)` = `ρ.lookup i`, then store deref |
| `A(c(x̄), ρ, σ) = (c, ρ(x̄))` | `\| .con c => some (.conLabel c)` and `\| .succE ae => do let a ← evalAddr ae ρ; let _ ← σ a; some (.succVal a)` | ✓ specialized to nullary `c` and unary `S(x)` (the address `a = ρ(x)`) |
| `A(fn(xs) e_body, ρ_λ, σ) = (xs, e_body, ρ_λ)` | `\| .lam e => some (.closure ⟨e, ρ, none⟩)` | ✓ captures the current env, no `selfAddr` |

The auxiliary `evalAddr ae ρ` (used for the `S(x)`/`op(x)` argument positions)
returns `ρ.lookup i` for `bvar i` — i.e. `ρ(x)` — and is undefined otherwise. ✓

---

## Part 3 — Evaluation rules

For each rule: the paper statement, the Lean constructor, and a verdict.
Judgements: `⇓e` = `EvalExp`, `⇓ec` = `EvalCExp`, `⇒c` = `ContinueFrame`,
`⇓h` = `HandleValue`, `⇓a` = `ApplyKont`.

### `⇓e` (expressions)

**[eval-let]**
```
(ce,ρ,σ) ⇓ec (v,σ')      ((y,e,ρ),v,σ') ⇒c (v',σ'')
─────────────────────────────────────────────────── 
(let y=ce; e, ρ, σ) ⇓e (v',σ'')
```
```lean
| eval_let :
    EvalCExp ce ρ σ v σ' →
    ContinueFrame (Frame.letFrame e ρ) v σ' v' σ'' →
    EvalExp (Exp.letE ce e l) ρ σ v' σ''
```
**✓** `(y,e,ρ)` = `Frame.letFrame e ρ`; the binder `y` is `bvar 0`, introduced by
[continue-let]. (`l` is the program label, threaded but semantically inert.)

**[eval-tail]**
```
(ce,ρ,σ) ⇓ec (v,σ')
───────────────────
(ce,ρ,σ) ⇓e (v,σ')
```
```lean
| eval_tail : EvalCExp ce ρ σ v σ' → EvalExp (Exp.tail ce l) ρ σ v σ'
```
**✓**

### `⇓ec` (complex expressions)

**[eval-atomic]**
```
────────────────────────────
(ae,ρ,σ) ⇓ec (A(ae,ρ,σ), σ)
```
```lean
| eval_atomic : evalAtomic ae ρ σ = some d → EvalCExp (CExp.atomic ae) ρ σ (Value.den d) σ
```
**✓** store unchanged; result `= A(ae,ρ,σ)`.

**[eval-fun]**
```
v_f = (xs, e1, ρ[f ↦ a_v])      a_v is fresh
──────────────────────────────────────────────
(fun f(xs) e1, ρ, σ) ⇓ec (v_f, σ[a_v ↦ v_f])
```
```lean
| eval_fun :
    σ a_v = none →
    v_f = Denotable.closure ⟨e1, ρ, some a_v⟩ →
    σ' = σ.extend a_v v_f →
    EvalCExp (CExp.funDef e1) ρ σ (Value.den v_f) σ'
```
**✓** `a_v` fresh (`σ a_v = none`); store extended with the self-referential
closure. The paper captures the self-binding `f ↦ a_v` *inside* the closure's
env; the LN version instead records `a_v` as `selfAddr` and re-pushes it at call
time ([eval-app-clos]). These are equivalent (`a_v` holds the closure either
way); see §4.

**[eval-app-clos]**
```
(xs, e_body, ρ_λ) = A(f,ρ,σ)
σ_λ = σ[ a_v ↦ A(ae,ρ,σ) ]      as_v are fresh
(e_body, ρ_λ[ x ↦ a_v ], σ_λ) ⇓e (v',σ')
──────────────────────────────────────────────
(f(ae), ρ, σ) ⇓ec (v',σ')
```
```lean
| eval_funApp_clos :
    evalAtomic f ρ σ = some (Denotable.closure ⟨e_body, ρ_lam, selfAddr⟩) →
    List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes ds →
    List.Forall₂ (fun a _ => σ a = none) as_v ds →
    as_v.Nodup →
    as_v.length = aes.length →
    σ_new = (List.zip as_v ds).foldl (fun s (a,d) => s.extend a d) σ →
    ρ_new = (match selfAddr with
      | none    => Env.pushMany ρ_lam as_v
      | some a_f => (Env.pushMany ρ_lam as_v).push a_f) →
    EvalExp e_body ρ_new σ_new v' σ' →
    EvalCExp (CExp.funApp f aes) ρ σ v' σ'
```
**✓** `A(f)` is the closure; `A(ae)` are the argument denotables `ds`; `as_v`
fresh and distinct; `σ_λ = σ[a_v ↦ ds]`. `ρ_λ[x ↦ a_v]` = `pushMany ρ_lam as_v`
(args become `bvar 0..`). For a recursive closure (`selfAddr = some a_f`) the
self-address is additionally pushed (`bvar 0` = self, args shift up by one),
realizing the paper's `f ↦ a_v` self-binding at call time. See §4.

**[eval-app-op]**
```
v = (op, ρ(x̄), [])
──────────────────────
(op(xs), ρ, σ) ⇓ec (v, σ)
```
```lean
| eval_opApp :
    evalAddr ae ρ = some a_v →
    EvalCExp (CExp.opApp op ae) ρ σ (Value.suspended op [a_v] []) σ
```
**✓** the argument address `ρ(x)` = `evalAddr ae ρ`; suspends with empty
continuation; store unchanged. (Single argument; see §4.)

**[eval-app-kont]**
```
(κ, A(ae,ρ,σ), σ) ⇓a (v',σ')
(h, ρ_h, κ) = A(f,ρ,σ)      (h, ρ_h, v', σ') ⇓h (v'',σ'')
──────────────────────────────────────────────────────
(f(ae), ρ, σ) ⇓ec (v'',σ'')
```
```lean
| eval_funApp_kont :
    evalAtomic f ρ σ = some (Denotable.kontClosure h ρ_h κ) →
    evalAtomic ae ρ σ = some d →
    ApplyKont κ d σ v' σ' →
    HandleValue h ρ_h v' σ' v'' σ'' →
    EvalCExp (CExp.funApp f [ae]) ρ σ v'' σ''
```
**✓** `A(f)` is the captured continuation `(h,ρ_h,κ)`; apply `κ` to `A(ae)=d`,
then re-handle under the captured handler `(h,ρ_h)`.

**[eval-match]** (general; LN splits into nullary and successor cases)
```
c(as_v) = A(ae,ρ,σ)      as_v' are fresh
b(c) = (xs, e)      ρ_b = ρ[ x̄ ↦ a_v' ]
σ_b = σ[ a_v' ↦ σ(a_v) ]      (e, ρ_b, σ_b) ⇓e (v',σ')
──────────────────────────────────────────────────────
(match(ae){b}, ρ, σ) ⇓ec (v',σ')
```
*Nullary constructors (`xs = []`, so `ρ_b = ρ`, `σ_b = σ`):*
```lean
| eval_match :
    evalAtomic ae ρ σ = some d →
    d = Denotable.conLabel c →
    findBranch bs c = some e →
    EvalExp e ρ σ v' σ' →
    EvalCExp (CExp.matchE ae bs) ρ σ v' σ'
```
*Unary successor (`xs = [x]`, rebinds the predecessor):*
```lean
| eval_match_succ :
    evalAtomic ae ρ σ = some (Denotable.succVal a_inner) →
    findBranch bs ConLabel.succ = some e →
    σ a_inner = some d_inner →
    σ a_fresh = none →
    σ_new = σ.extend a_fresh d_inner →
    ρ_new = ρ.push a_fresh →
    EvalExp e ρ_new σ_new v' σ' →
    EvalCExp (CExp.matchE ae bs) ρ σ v' σ'
```
**✓** `eval_match` is the paper rule with no binders (`a_inner = a_v`, none of
which is rebound). `eval_match_succ` rebinds the single predecessor:
`a_fresh` fresh, `σ_new = σ[a_fresh ↦ σ(a_inner)]` (exactly `σ_b = σ[a_v' ↦ σ(a_v)]`),
`ρ_new = ρ.push a_fresh` (`x ↦ a_v'`). Faithful specialization to the
`{0, S}`/`{true,false}`/`unit` constructor set; see §4.

**[eval-handler]**
```
(e_body, ρ, σ) ⇓e (v',σ')      (h, ρ, v', σ') ⇓h (v'',σ'')
──────────────────────────────────────────────────────
(h(e_body), ρ, σ) ⇓ec (v'',σ'')
```
```lean
| eval_handler :
    EvalExp e_body ρ σ v' σ' →
    HandleValue h ρ v' σ' v'' σ'' →
    EvalCExp (CExp.handler h e_body l_h) ρ σ v'' σ''
```
**✓**

### `⇒c` (let-frame continuation)

**[continue-let]**
```
σ_let = σ[a_v ↦ d]      a_v is fresh
(e, ρ[y ↦ a_v], σ_let) ⇓e (v',σ')
──────────────────────────────────
((y,e,ρ), d, σ) ⇒c (v',σ')
```
```lean
| continue_let :
    σ a_v = none →
    σ_let = σ.extend a_v d →
    EvalExp e (ρ.push a_v) σ_let v' σ' →
    ContinueFrame (Frame.letFrame e ρ) (Value.den d) σ v' σ'
```
**✓** `a_v` fresh; `ρ[y ↦ a_v]` = `ρ.push a_v` (`y` = `bvar 0`). Fires only on a
denotable (`Value.den d`).

**[continue-op]**
```
v = (op, as_v, clo:κ)
────────────────────────────
(clo, (op, as_v, κ), σ) ⇒c (v, σ)
```
```lean
| continue_op :
    ContinueFrame (Frame.letFrame e ρ) (Value.suspended op as_v κ) σ
                  (Value.suspended op as_v (Frame.letFrame e ρ :: κ)) σ
```
**✓** when the value is a suspended op, push the let-frame onto its
continuation; store unchanged. (`clo` = the `letFrame`.)

### `⇓h` (handle a value)

**[handle-return]**
```
h(return) = (x_ret, e_ret)
σ_ret = σ[a_v ↦ d]      a_v is fresh
(e_ret, ρ[x_ret ↦ a_v], σ_ret) ⇓e (v',σ')
──────────────────────────────────────────
(h, ρ, d, σ) ⇓h (v',σ')
```
```lean
| handle_return :
    e_ret = h.returnClause →
    σ a_v = none →
    σ_ret = σ.extend a_v d →
    EvalExp e_ret (ρ.push a_v) σ_ret v' σ' →
    HandleValue h ρ (Value.den d) σ v' σ'
```
**✓** return clause `(x_ret, e_ret)`; `a_v` fresh; `ρ[x_ret ↦ a_v]` =
`ρ.push a_v` (`x_ret` = `bvar 0`). Fires on a denotable value.

**[handle-op]**
```
h(op) = (xs, e_op)
σ_op = σ[ a_vk ↦ (h,ρ,κ), a_v' ↦ σ(a_v) ]      a_vk, as_v' are fresh
(e_op, ρ[ resume ↦ a_vk, x̄ ↦ a_v' ], σ_op) ⇓e (v,σ')
──────────────────────────────────────────────────────────────────
(h, ρ, (op, as_v, κ), σ) ⇓h (v,σ')
```
```lean
| handle_op :
    h.findOp op = some e_op →
    σ a_v' = none →
    σ a_vk = none →
    a_v' ≠ a_vk →
    σ a_arg = some d_arg →
    σ_op = (σ.extend a_vk (Denotable.kontClosure h ρ κ)).extend a_v' d_arg →
    EvalExp e_op ((ρ.push a_vk).push a_v') σ_op v σ' →
    HandleValue h ρ (Value.suspended op [a_arg] κ) σ v σ'
```
**✓** `h(op) = (xs, e_op)` = `findOp op = some e_op`; `a_vk`, `a_v'` fresh and
distinct; store `σ_op = σ[a_vk ↦ (h,ρ,κ), a_v' ↦ σ(a_v)]` — the kont closure
`(h,ρ,κ)` at `a_vk` and the argument value `σ(a_v) = d_arg` at `a_v'` (same
`a_vk`-first order as the paper). The body runs in `ρ[resume ↦ a_vk, x ↦ a_v']`,
i.e. `(ρ.push a_vk).push a_v'`: **`resume` is an ordinary binder** at `bvar 1`,
the argument `x` at `bvar 0`. (Single op argument; see §4.)

**[handle-capture-op]**
```
op ∉ h
v = (op, as_v, (h,ρ):κ)
─────────────────────────────
(h, ρ, (op, as_v, κ), σ) ⇓h (v, σ)
```
```lean
| handle_capture_op :
    h.hasOp op = false →
    v' = Value.suspended op as_v (Frame.handlerFrame h ρ :: κ) →
    HandleValue h ρ (Value.suspended op as_v κ) σ v' σ
```
**✓** unhandled op (`op ∉ h` = `hasOp op = false`): re-suspend with the handler
frame `(h,ρ)` pushed onto the continuation; store unchanged.

### `⇓a` (apply/restore a continuation)

**[apply-continue]**
```
──────────────────
([], d, σ) ⇓a (d, σ)
```
```lean
| apply_continue : ApplyKont [] d σ (Value.den d) σ
```
**✓**

**[apply-restore]**
```
(κ, d, σ) ⇓a (v',σ')      (clo, v', σ') ⇒c (v'',σ'')
──────────────────────────────────────────────────
(clo:κ, d, σ) ⇓a (v'',σ'')
```
```lean
| apply_restore :
    ApplyKont κ d σ v' σ' →
    ContinueFrame (Frame.letFrame e ρ) v' σ' v'' σ'' →
    ApplyKont (Frame.letFrame e ρ :: κ) d σ v'' σ''
```
**✓** `clo` = the let-frame; restore the rest of `κ`, then continue the frame.

**[apply-restore-handle]**
```
(κ, d, σ) ⇓a (v',σ')      (h, ρ, v', σ') ⇓h (v'',σ'')
──────────────────────────────────────────────────
((h,ρ):κ, d, σ) ⇓a (v'',σ'')
```
```lean
| apply_restore_handle :
    ApplyKont κ d σ v' σ' →
    HandleValue h ρ v' σ' v'' σ'' →
    ApplyKont (Frame.handlerFrame h ρ :: κ) d σ v'' σ''
```
**✓** handler frame on the continuation: restore the rest, then re-handle under
`(h,ρ)`.

---

## Part 4 — Intentional modeling specializations (faithful)

These are pre-existing choices in the formalization (not introduced by the
locally-nameless rework). Each restricts the paper's general form without
changing the rules' meaning on the modeled fragment.

1. **Single operation/branch argument.** Operations are invoked and handled
   with one argument (`op(x)`, `(op, [a], κ)`, op-clauses bind one value +
   `resume`), where the paper writes `op(xs)` / `(op, as_v, κ)`. Function
   application still takes an argument *list* (`funApp f aes`), matching
   `f(aes)`.

2. **Specialized constructor set.** The paper's `ConLabel × VAddr*` is realized
   as the nullary constructors `true/false/unit/zero` (`Denotable.conLabel`) and
   the unary successor `S(x)` (`Denotable.succVal a`). Accordingly `A`'s
   `c(x̄)` clause and `[eval-match]` are specialized to these (the `succ`
   branch is the only one that binds and rebinds, in `eval_match_succ`).

3. **Recursion representation.** The paper binds a recursive function's own name
   in its captured environment at definition time (`ρ[f ↦ a_v]`). The LN version
   records the self-address as `Closure.selfAddr` and re-pushes it at call time
   (`bvar 0` = self). Since `a_v` holds the closure in both cases, the recursive
   call resolves identically; this matches the B&P side's `letRec` (whose body
   binds self and argument).

4. **Program labels.** `Exp.letE`/`Exp.tail`/`CExp.handler` carry a `Label`
   (`l`, `l_h`) used only for naming handler/let frames in the abstraction; it is
   threaded unchanged and has no effect on the concrete evaluation relation.

## Conclusion

Every rule of the paper's concrete ANF big-step semantics (`⇓e`, `⇓ec`, `⇒c`,
`⇓h`, `⇓a`) corresponds to exactly one Lean constructor with matching premises
and conclusion, modulo the locally-nameless representation of binders
(de Bruijn indices + an address-stack `Env`) and the four faithful
specializations in §4. In particular `[handle-op]` matches the paper precisely:
the continuation closure `(h,ρ,κ)` and argument are stored at `a_vk`, `a_v'`
(in the paper's order), and the clause body runs with `resume` and the argument
bound in the environment — here as ordinary de Bruijn binders rather than a
reserved name.
