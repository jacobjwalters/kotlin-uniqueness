# Best Practices for Kotlin Uniqueness Formalization

Lessons learned during formalization in Lean 4 with Mathlib.
Includes patterns from the TaPL autoformalization project that apply here.

## Definitions

### Make key predicates `Decidable`
Adding `Decidable` instances for `Value`, `ClosedAt`, etc. enables `decide`
and `native_decide` in proofs and lets you write computational tests
(`example : Closed id' := by native_decide`).

### Derive `DecidableEq` and `Repr` on inductive types
Enables `native_decide` for concrete examples and `#eval` for debugging.

### Use `@[simp]` lemmas for impossible cases
Lemmas like `@[simp] lemma Eval.not_val : ¬ Eval ⟨.value v, E, []⟩ s := nofun`
pay for themselves across many proofs. Good candidates:
- Value predicates on non-value constructors
- Evaluation steps on irreducible/terminal states

## Proofs

### Preservation: `induction ht <;> cases he <;> solve_by_elim`
The standard preservation proof pattern works across typed languages:
```lean
theorem preservation (ht : Γ ⊢ t ⦂ T) (he : t ⟶ t') : Γ ⊢ t' ⦂ T := by
  induction ht generalizing t' <;> cases he <;>
    solve_by_elim [...]
```
For larger languages, add fallbacks:
- `first | assumption | solve_by_elim [...]` for cases closed by hypothesis
- `cases_type HasType; assumption` for cases needing one extra inversion

### Canonical forms: `cases hv <;> cases ht`
The most compact style for canonical-form lemmas:
```lean
lemma canonical_bool (hv : Value v) (ht : Typ .Expr Γ (liftValue v) (.Expr .bool)) :
    v = .True ∨ v = .False := by
  cases hv <;> cases ht <;> simp_all
```

### Inversion lemmas: when and how
- **Proofs by induction on a derivation** (preservation, progress):
  you already have the rule — `cases` or `solve_by_elim` suffice.
- **Proofs that reason about a known term form** (canonical forms,
  simulation, decidable type checking): named inversion lemmas pay off.

Keep inversion proofs trivial:
```lean
lemma Typ.inv_natConst (h : Typ .Expr Γ (.Nat n) r) : r = .Expr .nat := by
  cases h; rfl
```

### Start with `sorry`, fill in later
The iterative approach (definitions -> statements -> sorry proofs -> real proofs)
avoids wasted effort when definitions need to change. Mark sorry's with a
comment explaining what's needed.

### Use `omega` for arithmetic side-goals
Most goals involving `Nat` arithmetic in index manipulation proofs are
closed by `omega`. Use `by_cases` to set up the right hypotheses first,
then `simp [...]; omega`.

### Use `nofun` and `nomatch` for impossible cases
- `nofun` for impossible function goals
- `nomatch` for impossible match targets
These are more concise than `intro h; cases h` patterns.

### Use `ReflTransGen.lift` for congruence and inclusion lemmas
When proving that a multi-step relation is preserved by a function or
included in another relation, `ReflTransGen.lift` is a one-liner:
```lean
lemma MultiEval.lift (h : t ⟶* t') (f : CEK → CEK) (hf : ∀ a b, a ⟶ b → f a ⟶ f b) :
    f t ⟶* f t' :=
  h.lift f hf
```

### native_decide for concrete computations
For verifying specific reductions, `native_decide` is much faster than
building proof terms by hand. Requires `DecidableEq` on the relevant types.

## CEK Machine Proofs

### Type safety via continuation typing
The `ContType` inductive tracks how the continuation stack relates to the
typing context. Preservation for the CEK machine amounts to showing each
`Eval` step preserves the `ContType` invariant.

### PopLoopK reasoning
`PopLoopK` (for `break`) requires induction on the continuation stack.
Helper lemmas about how `PopLoopK` interacts with `ContType` simplify
the `break` case in preservation.

### Environment–context correspondence
A key invariant is that the runtime `Environment` matches the typing
`Ctx` (each `E[i]` has the type `Γ[i]`). Define this as a predicate
and maintain it across all evaluation rules.

## CFG Correspondence Proofs

### Use `CFGReach` bridge fields instead of transitive-closure constructors
When relating a CEK machine to a CFG, avoid adding a "step" constructor to
the continuation invariant (`ContCFGInv`) that allows shifting the anchor
node to an arbitrary predecessor. This makes the relation non-functional
(multiple nodes for the same CEK state), blocking `step_complete` proofs.

Instead, store a `CFGReach` (reflexive-transitive closure) witness in the
**entry-state** constructors of the relation, bridging from the child exit
node to the `ContCFGInv` anchor. Exit-state constructors anchor `ContCFGInv`
directly at the current node. This keeps the relation functional while
providing the bridging edges needed for `step_sound`.

### `WFCFG s` as the structural-invariant carrier
Prefer stating new correspondence lemmas against `WFCFG s` (see
`LBaseCFG/WFCFG.lean`) rather than threading `stmtCFG s` plus
per-constructor `ExprEntryEdgeInv` / `StmtEntryEdgeInv` obligations.
`WFCFG` bundles `CFG.OfStmt s g` once; `WFCFG.ofStmt s hbb` produces the
canonical witness from `StmtBreaksBounded 0 s`. This is the Option C
foundation that `cfgcekRel` should eventually migrate onto.

### Option A: `CFGState'`-based relation for `step_complete`
The projected relation `wfRel s` (see `LBaseCFG/WFCorrespondenceProofs.lean`)
wraps `wfRelFull`, which relates a CEK state to a `CFGState'` carrying
`pc + K + breakTargets + anchorNode + ContCFGInv + BreakTargetsWellFormed`.
This makes the relation injective on the CFG side: given `Eval σ σ'` and
`wfRelFull s σ' st'`, the pre-state `st` (and its pc) can be recovered from
the continuation invariants, enabling `step_complete`. The `step_sound` proof
mirrors `cfgcekRelReq.step_sound` from `CorrespondenceProofs.lean`.

### Use `cases` not `induction` on `ContCFGInv` in exit→entry proofs
With the `CFGReach` bridge design, continuation-pop cases in `step_sound`
should use `cases hContInv` to directly extract the stored edges, rather
than `induction hc` which was needed when a `step` constructor existed.

## Common Pitfalls

### `List.get?` does not exist — use bracket syntax
In recent Lean/Mathlib, `List.get?` has been removed. Use `Γ[x]?` (bracket
notation with `?`) instead. The relevant lemmas are named `List.getElem?_*`:
- `List.getElem?_append`, `List.getElem?_append_left`, `List.getElem?_append_right`
- `List.getElem?_cons_succ` (definitional: `(a :: l)[i+1]? = l[i]?`)

Note: `List.getElem?_cons_succ` only fires when the index is syntactically
`n + 1`. If you have `k - m` where you know `k - m ≥ 1`, first rewrite with
`have : k - m = (k - m - 1) + 1 := by omega`.

### `convert` requires an explicit import
`convert` is not available from `Mathlib.Logic.Relation` alone — add
`import Mathlib.Tactic.Convert` if needed.

### ReflTransGen API
In current Mathlib, `Relation.ReflTransGen` constructors are `refl` and `tail`
(not `head`). The lemma `ReflTransGen.head` exists for prepending a step but
`head` is not a constructor alternative name for pattern matching.
