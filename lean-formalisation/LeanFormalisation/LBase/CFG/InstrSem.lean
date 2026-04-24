/-
  Instrumented CFG semantics (Options B and C from the design report
  at https://bot.jesyspa.dev/kotlin/uniqueness/cfg/instr-sem-old1/).

  This file provides the definitional scaffolding that the previous
  `cfgcekRel`/`TranslationReq` formulation was missing:

  * `CFGState`             — a CFG-indexed operational state that carries
                             the cursor alongside the (unchanged) CEK
                             components `E`, `J`, `K` and an optional
                             `pending` value at `exprExit` nodes.
  * `CFGSilent`/`CFGNormal` — the silent/observable split of the
                             instrumented step relation, following the
                             standard weak-bisimulation pattern.
  * `CFGWeakStep`          — the composition
                             `CFGSilent* ;; CFGNormal ;; CFGSilent*`
                             used for the re-stated translation
                             obligations.
  * `TranslationReqW`      — the weak-bisimulation analogue of the
                             original `TranslationReq`. The plain
                             `TranslationReq` is recovered by the
                             forgetful map `φ st := st.cursor` and a
                             concrete instance in
                             `CorrespondenceProofs.lean`.
  * `cekCursor`            — Option C: a partial function from the CEK
                             state to its unique CFG cursor node. The
                             report calls for this to dissolve the
                             non-functional-in-`n` problem that blocks
                             the current `step_complete` attempt.

  Non-trivial obligations are stated with `sorry` and clearly tagged
  with `-- ROADBLOCK:` comments; see the accompanying PR description for
  the full catalogue.
-/

import LeanFormalisation.LBase.CFG.Correspondence
import LeanFormalisation.LBase.CFG.CorrespondenceProofs

open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal

namespace LeanFormalisation
namespace AltCFGProofs

section InstrSem

/-!
## Instrumented CFG state

The state keeps the `E`, `J`, `K` components from the CEK machine
verbatim — the instrumentation only adds a graph-indexed `cursor` and a
`pending` slot for the "hot" value at an `exprExit` node (between a
value being produced and the enclosing continuation consuming it).
-/

structure CFGState (g : CFG) where
  cursor : NodeOf g
  E : Environment
  J : JStackCtx
  K : List Cont
  pending : Option Value

/-- The forgetful map used to recover a plain `NodeOf g` relation from
    the instrumented bisimulation. -/
@[simp] def CFGState.project {g : CFG} (st : CFGState g) : NodeOf g := st.cursor

/-- Reify the CEK-visible components of an instrumented state. The
    `pending` slot gives rise to a `Control.value` when present,
    otherwise we read the control from the cursor's kind. -/
def CFGState.toCEK {g : CFG} (st : CFGState g) : CEK :=
  match st.pending, st.cursor.1.kind with
  | some v, _             => ⟨.value v, st.E, st.J, st.K⟩
  | none, .exprEntry e    => ⟨.sourceExpr e, st.E, st.J, st.K⟩
  -- `exprExit` with `pending = none` is not reachable in well-formed states;
  -- we return a dummy `.skip` to keep the function total.
  | none, .exprExit _     => ⟨.skip, st.E, st.J, st.K⟩
  | none, .stmtEntry s'   => ⟨.sourceStmt s', st.E, st.J, st.K⟩
  | none, .stmtExit _     => ⟨.skip, st.E, st.J, st.K⟩

/-!
## Silent and normal transitions

A *silent* step only moves the cursor along a structural CFG edge
without changing the environment or jump context. It may push a
continuation frame onto `K` (the descent into `BinOp`'s left operand,
for instance) or clear a `pending` value once it has been consumed at
the matching `exprExit`. A *normal* step performs a CEK-observable
update: a variable load, an operator application, a branch choice, a
`Decl`/`Assign` commit, or a `Break`/loop transition.

The split is dictated by the source-node kind together with the
outgoing edge kind in `AltCFG`. We capture the two predicates as plain
inductive relations here and delay a mechanical per-edge case split to
`InstrSemProofs`.
-/

/-- `CFGSilent g st st'` holds when the transition from `st` to `st'`
    corresponds to a single structural CFG edge that does **not** reach
    into the abstract domain: the environment and jump stack are
    unchanged, and the cursor moves along an edge of `g`. The `K` and
    `pending` slots may shift when descending into or returning from a
    sub-expression. -/
inductive CFGSilent (g : CFG) : CFGState g → CFGState g → Prop where
  /-- Structural descent or return edge: the cursor advances along a
      CFG edge, the environment and jump context are unchanged, and
      no value is produced. The continuation stack may be adjusted
      (e.g. a new frame pushed when descending into `BinOp`'s left
      operand, or a frame popped when returning from a sub-expression
      whose value has already been deposited in `pending`). Concrete
      per-kind clauses — which determine the exact `K` adjustment from
      the source/destination node kinds — live in `InstrSemProofs`. -/
  | struct {st st' : CFGState g} :
      CFGStep g st.cursor st'.cursor →
      st'.E = st.E → st'.J = st.J →
      CFGSilent g st st'

/-- `CFGNormal g st st'` holds when the transition from `st` to `st'`
    corresponds to a CEK small step that is observable to the dataflow
    analysis: a value read, operator application, branch resolution,
    commit of a declaration/assignment, loop iteration decision, or
    break jump.

    Each constructor pins down exactly the CFG-edge / `Eval` alignment
    for one CEK rule. The alignment is asymmetric: `step_sound` has to
    produce a matching `CFGNormal` given an `Eval`, while
    `step_complete` has to produce an `Eval` given a `CFGNormal`. -/
inductive CFGNormal (g : CFG) : CFGState g → CFGState g → Prop where
  /-- A variable-load step: from `exprEntry (.Var x)` we step to the
      matching `exprExit` with the variable value deposited in
      `pending`. -/
  | varLoad {st st' : CFGState g} (x : VarName) :
      CFGStep g st.cursor st'.cursor →
      st.pending = none →
      st'.pending = some (st.E[x]!) →
      st'.E = st.E → st'.J = st.J → st'.K = st.K →
      CFGNormal g st st'
  /-- A binary operation resolves at the `exprExit` of the RHS: the two
      operand values (`pending` holds v₂, the `.binopRK` frame holds
      v₁) are combined and the cursor moves to the enclosing exit. -/
  | binop {st st' : CFGState g} (op : BinOp) (v₁ v₂ result : Value) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some v₂ →
      st.K = (.binopRK op v₁) :: st'.K →
      op.step v₁ v₂ result →
      st'.pending = some result →
      st'.E = st.E → st'.J = st.J →
      CFGNormal g st st'
  /-- Unary operation resolves at the operand's `exprExit`. -/
  | unop {st st' : CFGState g} (op : UnOp) (v result : Value) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some v →
      st.K = (.unopK op) :: st'.K →
      op.step v result →
      st'.pending = some result →
      st'.E = st.E → st'.J = st.J →
      CFGNormal g st st'
  /-- Commit a `Decl`: the pending value is pushed onto `E`, cursor
      moves to the enclosing `stmtExit`, and the `.declK` frame is
      popped. -/
  | declDone {st st' : CFGState g} (ty : Ty) (v : Value) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some v →
      st.K = (.declK ty) :: st'.K →
      st'.pending = none →
      st'.E = v :: st.E → st'.J = st.J →
      CFGNormal g st st'
  /-- Commit an `Assign`: the pending value overwrites the named slot
      in `E`. -/
  | assignDone {st st' : CFGState g} (x : VarName) (v : Value) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some v →
      st.K = (.assignK x) :: st'.K →
      st'.pending = none →
      st'.E = st.E.set x v → st'.J = st.J →
      CFGNormal g st st'
  /-- Branch resolution on `True`: the `.ifCondK` frame is consumed and
      the cursor follows the `.trueBranch` edge. -/
  | ifTrue {st st' : CFGState g} (e₁ e₂ : Lang .Expr) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some .True →
      st.K = (.ifCondK e₁ e₂) :: st'.K →
      st'.pending = none →
      st'.E = st.E → st'.J = st.J →
      CFGNormal g st st'
  /-- Branch resolution on `False`. -/
  | ifFalse {st st' : CFGState g} (e₁ e₂ : Lang .Expr) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some .False →
      st.K = (.ifCondK e₁ e₂) :: st'.K →
      st'.pending = none →
      st'.E = st.E → st'.J = st.J →
      CFGNormal g st st'
  /-- Loop body chosen: follow the `.trueBranch` edge to the body
      entry; push a `.loopContK` frame and record the loop depth on
      `J`. -/
  | loopTrue {st st' : CFGState g} (c body : Lang .Expr) (n : Nat) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some .True →
      st.K = (.loopK c body n) :: st'.K →
      st'.pending = none →
      st'.K = (.loopContK c body n) :: st.K.tail →
      st'.E = st.E → st'.J = ⟨n, st.K.tail⟩ :: st.J →
      CFGNormal g st st'
  /-- Loop exits: follow the `.falseBranch`; trim `E` to its pre-loop
      length and deposit `.Unit`. -/
  | loopFalse {st st' : CFGState g} (c body : Lang .Expr) (n : Nat) :
      CFGStep g st.cursor st'.cursor →
      st.pending = some .False →
      st.K = (.loopK c body n) :: st'.K →
      st'.pending = some .Unit →
      st'.E = st.E.drop (st.E.length - n) →
      st'.J = st.J →
      CFGNormal g st st'
  /-- Break jump: cursor follows a `.breakOut` edge; `J` is trimmed
      and `K` is replaced by the saved continuation of the target
      loop. -/
  | breakJump {st st' : CFGState g} (l : Nat)
      (hj : l < st.J.length) :
      CFGStep g st.cursor st'.cursor →
      st.pending = none →
      st'.pending = some .Unit →
      st'.E = st.E.drop (st.E.length - (st.J[l]'hj).1) →
      st'.J = st.J.drop (l + 1) →
      st'.K = (st.J[l]'hj).2 →
      CFGNormal g st st'

/-- Reflexive–transitive closure of silent steps. -/
abbrev CFGSilentStar (g : CFG) : CFGState g → CFGState g → Prop :=
  Relation.ReflTransGen (CFGSilent g)

/-- `st ~w~> st'` — one "weak" step:
    `CFGSilent* ;; CFGNormal ;; CFGSilent*`. -/
def CFGWeakStep (g : CFG) (st st' : CFGState g) : Prop :=
  ∃ stₐ stᵦ, CFGSilentStar g st stₐ ∧ CFGNormal g stₐ stᵦ ∧ CFGSilentStar g stᵦ st'

lemma CFGSilent.toCFGStep {g : CFG} {st st' : CFGState g} (h : CFGSilent g st st') :
    CFGStep g st.cursor st'.cursor := by
  cases h <;> assumption

lemma CFGNormal.toCFGStep {g : CFG} {st st' : CFGState g} (h : CFGNormal g st st') :
    CFGStep g st.cursor st'.cursor := by
  cases h <;> assumption

/-- Silent closure respects the cursor projection: every silent walk on
    `CFGState g` projects down to a `CFGReach` walk. -/
lemma CFGSilentStar.toCFGReach {g : CFG} {st st' : CFGState g}
    (h : CFGSilentStar g st st') : CFGReach g st.cursor st'.cursor := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail hs.toCFGStep

/-- A weak step projects to `CFGReach`. This is what the downstream
    `translation_sound_reachability` needs. -/
lemma CFGWeakStep.toCFGReach {g : CFG} {st st' : CFGState g}
    (h : CFGWeakStep g st st') : CFGReach g st.cursor st'.cursor := by
  obtain ⟨stₐ, stᵦ, hs₁, hn, hs₂⟩ := h
  exact (hs₁.toCFGReach.tail hn.toCFGStep).trans hs₂.toCFGReach

/-!
## Weak translation obligations (Option B)

The obligations are the silent-closure-wrapped analogue of the original
`TranslationReq`. A concrete relation `R : CEK → CFGState g → Prop`
must satisfy:

* `step_sound`    – every `Eval σ σ'` at a related state `st` is
                    matched by a weak step `CFGWeakStep g st st'` with
                    `R σ' st'`;
* `step_complete` – every `Eval σ σ'` at a related state `st'` is
                    reached from *some* `st` with `R σ st` via a weak
                    step;
* `init_related`/`terminal_related`/`init_uniq` carry over unchanged.

The point of the silent-closure wrapping is that the non-functional
ambiguity captured by `ContCFGInv.step` in the old `cfgcekRel` becomes
*explicit* rather than hidden: the many CFG predecessors that map to
the same CEK state are exactly the endpoints of a `CFGSilentStar` walk.
-/

class TranslationReqW
    (s : Lang .Stmt) (R : CEK → CFGState (stmtCFG s) → Prop) : Prop where
  init_related :
    R (initState s)
      { cursor  := ⟨(stmtCFG s).entry, (stmtCFG s).entry_in_nodes⟩
      , E := [], J := [], K := [], pending := none }
  terminal_related : ∀ E,
    R (terminalState E [])
      { cursor  := ⟨(stmtCFG s).exit, (stmtCFG s).exit_in_nodes⟩
      , E := E, J := [], K := [], pending := none }
  init_uniq : ∀ {st}, R (initState s) st → st.cursor = (stmtCFG s).entry
  step_sound :
    ∀ {σ σ' st}, R σ st → Eval σ σ' →
      ∃ st', R σ' st' ∧ CFGWeakStep (stmtCFG s) st st'
  step_complete :
    ∀ {σ σ' st'}, Eval σ σ' → R σ' st' →
      ∃ st, R σ st ∧ CFGWeakStep (stmtCFG s) st st'

/-!
### Recovering the plain `TranslationReq`

Any weak instance induces a plain one by existential-quantifying over
the instrumented state and projecting with `φ`. The converse would
require a choice of `CFGState` per CEK state; the canonical one is the
image of `cekCursor` (Option C, below).
-/

/-- The forgetful plain relation obtained by composition with the
    cursor projection. -/
def plainRel
    {s : Lang .Stmt} (R : CEK → CFGState (stmtCFG s) → Prop) :
    @StateRel (stmtCFG s) :=
  fun σ n => ∃ st : CFGState (stmtCFG s), R σ st ∧ st.cursor = n

/-- A weak `TranslationReqW` gives rise to a plain `TranslationReq` via
    the forgetful projection. -/
instance TranslationReqW.toTranslationReq
    (s : Lang .Stmt) (R : CEK → CFGState (stmtCFG s) → Prop)
    [w : TranslationReqW s R] :
    TranslationReq s (plainRel R) where
  init_related := ⟨_, w.init_related, rfl⟩
  terminal_related E := ⟨_, w.terminal_related E, rfl⟩
  init_uniq := by
    intro n ⟨_, hR, hcur⟩
    exact hcur ▸ w.init_uniq hR
  step_sound := by
    rintro σ σ' n ⟨st, hR, rfl⟩ hEval
    obtain ⟨st', hR', hstep⟩ := w.step_sound hR hEval
    exact ⟨st'.cursor, ⟨st', hR', rfl⟩, hstep.toCFGReach⟩
  step_complete := by
    rintro σ σ' n' hEval ⟨st', hR', rfl⟩
    obtain ⟨st, hR, hstep⟩ := w.step_complete hEval hR'
    exact ⟨st.cursor, ⟨st, hR, rfl⟩, hstep.toCFGReach⟩

/-!
## Option C — `cekCursor`

`cekCursor s σ` is the CFG cursor that the reachable CEK state `σ`
canonically points at in `stmtCFG s`. It is partial in general; for
CEK states obtained by evaluation from `initState s`, it is total.

Making the cursor a function rather than a relation is what forces the
bisimulation to be functional in the CFG component by construction —
that is, it directly discharges the `rel_uniq` / functionality
obligation that was the original obstacle to `step_complete`.

### Design

The cursor is determined by the control component of `σ` together with
a *walk* through `σ.K`:

* `sourceExpr e` at depth `d` in the continuation stack pins the
  cursor at the `exprEntry e` node of the unique static occurrence of
  `e` reached by threading the builder-level parent/break-target stack
  through `K`.
* `sourceStmt s'` is analogous with `stmtEntry s'`.
* `value v` or `skip` pins the cursor at the matching `exprExit` /
  `stmtExit` node of the frame currently at the top of `K`, or at
  `stmtExit s` when `K = []`.

The recursion is naturally on the size of the continuation stack, not
on the CEK state itself — the control component and the topmost frame
together determine the next node, and the tail of `K` fixes the
enclosing context.
-/

/-- Skeletal definition: walk the continuation stack to find the CFG
    cursor node. See the per-case spec below.
    ROADBLOCK: the concrete implementation has to mirror every
    constructor of `ContCFGInv` and is mutually recursive with a node
    *lookup* function over the AltCFG builder; it is ~200 lines of
    boilerplate once the builder traversal lemmas in
    `CorrespondenceProofs.lean` are factored out. -/
noncomputable def cekCursor (s : Lang .Stmt) (_σ : CEK) :
    Option (NodeOf (stmtCFG s)) := by
  -- The concrete recursion should be written by case analysis on
  -- `σ.C` and, for `.value`/`.skip`, on the head of `σ.K`. Every case
  -- picks the *unique* node in `(stmtCFG s).nodes` whose kind agrees
  -- with the surrounding syntactic position — the same data that is
  -- non-deterministically witnessed inside `ContCFGInv` today.
  -- See the design-note, section "Option C — CEK-reflection".
  exact none  -- ROADBLOCK: implementation deferred

/-- Totality on reachable states: for any `σ` reached from `initState
    s` by `Eval*`, `cekCursor s σ` is `some _`. This is the
    statement-level form of the reachability invariant. -/
theorem cekCursor_total
    (s : Lang .Stmt) (hbb : StmtBreaksBounded 0 s)
    {σ : CEK} (hreach : CEKReach (initState s) σ) :
    ∃ n, cekCursor s σ = some n := by
  -- ROADBLOCK: requires the per-constructor recursion above to be in
  -- place, together with a reachability lemma that no `Break` ever
  -- dangles beyond `J` (provided by `hbb`).
  sorry

/-- Uniqueness: any two nodes related to the same `σ` via
    `cfgcekRel s` coincide. This is the function-level statement of
    what `TranslationReq.init_uniq` only requires at `initState s`. -/
theorem cfgcekRel_functional
    (s : Lang .Stmt) {σ : CEK} {n m : NodeOf (stmtCFG s)}
    (hn : cfgcekRel s σ n) (hm : cfgcekRel s σ m) :
    cekCursor s σ = some n ∧ n = m := by
  -- ROADBLOCK: Two parts.
  -- (1) `n = m`: the natural statement of `rel_uniq`. The current
  --     `cfgcekRel` is NOT functional in `n` because of
  --     `ContCFGInv.step`, so this lemma only holds once `cfgcekRel`
  --     is tightened to its "anchored" (non-.step) subrelation.
  -- (2) the `cekCursor` equation: follows from the functional
  --     recursion once (1) holds.
  sorry

/-!
## Relating Option B and Option C

The weak bisimulation of Option B admits a canonical witness: given
Option C's `cekCursor`, define
`R σ st := cekCursor s σ = some st.cursor ∧ σ = st.toCEK`. Functionality
is built in; the `step_sound`/`step_complete` obligations reduce to
case analyses on `Eval` and the CFG edge taxonomy.
-/

/-- The canonical weak-bisimulation witness built from `cekCursor`. -/
def cekCursorRel (s : Lang .Stmt) (σ : CEK) (st : CFGState (stmtCFG s)) : Prop :=
  cekCursor s σ = some st.cursor ∧ σ = st.toCEK

/-- Instance sketch for the canonical witness. All obligations are
    left as `sorry` with per-case notes; see the PR description for
    the breakdown. -/
noncomputable instance cekCursorRel_req
    (s : Lang .Stmt) (hbb : StmtBreaksBounded 0 s) :
    TranslationReqW s (cekCursorRel s) where
  init_related := by
    -- ROADBLOCK: follows from `cekCursor (initState s) = some entry`;
    -- needs the skeletal `cekCursor` implementation filled in.
    sorry
  terminal_related := by
    -- ROADBLOCK: as above but for the exit node.
    sorry
  init_uniq := by
    -- Direct: `cekCursor (initState s) = some entry` pins the cursor.
    sorry
  step_sound := by
    -- ROADBLOCK: per-constructor case analysis on `Eval`. Each rule
    -- decomposes as zero-or-more silent edges (frame pushes /
    -- literal loads), exactly one normal edge (the CEK-observable
    -- update), and zero-or-more silent edges again (returning to the
    -- enclosing exit).
    sorry
  step_complete := by
    -- Follows once step_sound is in place: `cekCursor` is a function,
    -- so the predecessor instrumented state is uniquely determined
    -- by `st'` and `σ = st.toCEK`.
    sorry

end InstrSem

end AltCFGProofs
end LeanFormalisation
