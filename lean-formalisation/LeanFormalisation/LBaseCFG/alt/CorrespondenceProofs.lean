/-
  need to formulate theorems on the CFG representation, relating back to the
  cek semantics.

  the main goals are

  1. correctness of the cfg translation in `altcfg` (both directions), and
  2. correctness of the forward worklist solver in `analysis` (both directions).

  the strategy is to define a concrete CEK-to-CFG relation (kind compatibility
  plus synchronized reachability from entry), prove one-step soundness and
  completeness obligations against cfg edges, and then lift these obligations
  to whole-path correspondence via reflexive-transitive induction.
-/

import LeanFormalisation.LBaseCFG.alt.Correspondence


open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal

namespace LeanFormalisation
namespace AltCFGProofs

section Translation

/-!
## structural cfg obligations
-/
-- stupid theorems that have to be proven.
/--
Characterizes membership in `eraseDupsBy.loop`: an element in the result comes
from either the remaining input list or the accumulator. Use: helper for proving
the user-facing `List.mem_eraseDups` equivalence below.
-/
private theorem mem_eraseDupsBy_loop [BEq A] [LawfulBEq A] {l acc : List A} {a : A} :
    a ∈ List.eraseDupsBy.loop (· == ·) l acc <-> a ∈ l ∨ a ∈ acc := by
  fun_induction List.eraseDupsBy.loop with grind

/--
Shows `eraseDups` preserves and reflects list membership. Use: converts goals
about `CFG.nodes` (defined via `eraseDups`) back to plain list membership.
-/
private theorem List.mem_eraseDups [BEq A] [LawfulBEq A] {l : List A} {a : A} :
    a ∈ l <-> a ∈ l.eraseDups := by
  constructor <;> intros ha
  case mp =>
    simp [List.eraseDups, List.eraseDupsBy, mem_eraseDupsBy_loop, ha]
  case mpr =>
    cases mem_eraseDupsBy_loop.1 ha
    case inl h => exact h
    case inr h => cases h

/--
Proves every CFG contains its designated entry node in `nodes`. Use: first half
of the exported `stmtCFG_entry_exit_in_nodes` structural sanity theorem.
-/
private theorem cfg_entry_in_nodes (g : CFG) : g.entry ∈ g.nodes := by
  unfold CFG.nodes
  apply List.mem_eraseDups.1
  induction g.edges with
  | nil => simp
  | cons h t ih => simp [ih]

/--
Proves every CFG contains its designated exit node in `nodes`. Use: second half
of the exported `stmtCFG_entry_exit_in_nodes` structural sanity theorem.
-/
private theorem cfg_exit_in_nodes (g : CFG) : g.exit ∈ g.nodes := by
  unfold CFG.nodes
  apply List.mem_eraseDups.1
  induction g.edges with
  | nil => simp
  | cons h t ih => simp [ih]

/--
For statement CFGs, both distinguished endpoints are present in the node set.
Use: baseline well-formedness fact for any argument that quantifies over nodes.
-/
theorem stmtCFG_entry_exit_in_nodes (s : Lang .Stmt) :
    (stmtCFG s).entry ∈ (stmtCFG s).nodes ∧ (stmtCFG s).exit ∈ (stmtCFG s).nodes := by
   exact ⟨cfg_entry_in_nodes (stmtCFG s), cfg_exit_in_nodes (stmtCFG s)⟩

/--
Computes the kind of the exit node returned by `buildExpr`: it is always
`exprExit expr`. Use: discharges the direct branch-edge cases in mutual proofs.
-/
theorem buildExpr_exit_kind
    (breakTargets : List CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTargets nextId fuel expr).exit.kind = .exprExit expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

/--
Computes the kind of the entry node returned by `buildExpr`: it is always
`exprEntry expr`. Use: identifies the destination of `.back` edges in while.
-/
theorem buildExpr_entry_kind
    (breakTargets : List CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTargets nextId fuel expr).entry.kind = .exprEntry expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

theorem buildStmt_entry_kind
    (breakTargets : List CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    (buildStmt breakTargets nextId fuel stmt).entry.kind = .stmtEntry stmt := by
  cases fuel <;> cases stmt <;> simp [buildStmt]

theorem buildStmt_exit_kind
    (breakTargets : List CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    (buildStmt breakTargets nextId fuel stmt).exit.kind = .stmtExit stmt := by
  cases fuel <;> cases stmt <;> simp [buildStmt]

/--
Mutual fuel-induction core: any `.trueBranch`/`.falseBranch` edge produced by
either builder has source kind `exprExit _`. Use: single shared engine for the
two public branch-shape theorems immediately below.
-/
private theorem branch_src_exprExit_mutual :
    ∀ fuel,
      (∀ (breakTargets : List CFGNode) (nextId : Nat) (stmt : Lang .Stmt)
          (ed : CFGEdge),
          ed ∈ (buildStmt breakTargets nextId fuel stmt).edges ->
          ed.kind = .trueBranch ∨ ed.kind = .falseBranch ->
          ∃ cond, ed.src.kind = .exprExit cond) ∧
      (∀ (breakTargets : List CFGNode) (nextId : Nat) (expr : Lang .Expr)
          (ed : CFGEdge),
          ed ∈ (buildExpr breakTargets nextId fuel expr).edges ->
          ed.kind = .trueBranch ∨ ed.kind = .falseBranch ->
          ∃ cond, ed.src.kind = .exprExit cond) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTargets nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTargets nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTargets nextId stmt ed hed hkind
      cases stmt
        <;> simp only [buildStmt, List.cons_append,
          List.nil_append, List.mem_cons, List.mem_append] at hed
      case Decl τ init =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
      case Assign x rhs =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
      case Seq s₁ s₂ =>
        rcases hed with h | h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h with h | h
          · exact ihStmt _ _ _ _ h hkind
          · exact ihStmt _ _ _ _ h hkind
      case Do e =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
    · intro breakTargets nextId expr ed hed hkind
      cases expr <;>
        try
          (simp only [buildExpr, List.mem_cons, List.not_mem_nil,
            or_false, List.cons_append, List.nil_append, List.append_assoc,
            List.mem_append] at hed)
      all_goals
        try (subst ed; simp [mkEdge] at hkind)
      case BinOp a₁ a₂ op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · simp only [mkEdge] at h₃
          rcases h₃ with h₁ | (h₂ | h₃)
          · subst ed
            simp at hkind
          · exact ihExpr _ _ _ _ h₂ hkind
          · exact ihExpr _ _ _ _ h₃ hkind
      case UnOp a op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h₃ hkind
      case If cond e₁ e₂ =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind breakTargets (nextId + 2) n cond)
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind breakTargets (nextId + 2) n cond)
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₆ with h | h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case While cond body =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind ({
                id := nextId + 1,
                kind := .exprExit (.While cond body)
              } :: breakTargets)
              (nextId + 2) n cond)
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind ({
                id := nextId + 1,
                kind := .exprExit (.While cond body)
              } :: breakTargets)
              (nextId + 2) n cond)
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₅ with h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case Break l =>
        split at hed
        · simp [mkEdge] at hed; subst ed; simp at hkind
        · simp at hed
      case Scope s res =>
        rcases hed with h₁ | h₂ | h₃ | h₄
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₄ with h | h
          · exact ihStmt _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind

/--
Statement-builder specialization of `branch_src_exprExit_mutual`. Use: direct
input to `stmtCFG_true_false_edges_from_exprExit` after unfolding `stmtCFG`.
-/
theorem buildStmt_branch_src_exprExit
    (breakTargets : List CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    ∀ ed ∈ (buildStmt breakTargets nextId fuel stmt).edges,
    ed.kind = .trueBranch ∨ ed.kind = .falseBranch ->
    ∃ cond, ed.src.kind = .exprExit cond := by
  intro ed hed hkind
  exact (branch_src_exprExit_mutual fuel).1 breakTargets nextId stmt ed hed hkind

/--
Expression-builder specialization of `branch_src_exprExit_mutual`. Use: reusable
branch-edge invariant for later expression-local arguments.
-/
theorem buildExpr_branch_src_exprExit
    (breakTargets : List CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    ∀ ed ∈ (buildExpr breakTargets nextId fuel expr).edges,
    ed.kind = .trueBranch ∨ ed.kind = .falseBranch ->
    ∃ cond, ed.src.kind = .exprExit cond := by
  intro ed hed hkind
  exact (branch_src_exprExit_mutual fuel).2 breakTargets nextId expr ed hed hkind

/--
Mutual fuel-induction core for back edges: every `.back` edge produced by either
builder goes from `exprExit body` to `exprEntry cond`. Use: shared engine for
`buildStmt_back_edge_shape` and `buildExpr_back_edge_shape`.
-/
private theorem back_edge_shape_mutual :
    ∀ fuel,
      (∀ (breakTargets : List CFGNode) (nextId : Nat) (stmt : Lang .Stmt)
          (ed : CFGEdge),
          ed ∈ (buildStmt breakTargets nextId fuel stmt).edges ->
          ed.kind = .back ->
          ∃ c body,
            ed.src.kind = .exprExit body ∧
            ed.dst.kind = .exprEntry c) ∧
      (∀ (breakTargets : List CFGNode) (nextId : Nat) (expr : Lang .Expr)
          (ed : CFGEdge),
          ed ∈ (buildExpr breakTargets nextId fuel expr).edges ->
          ed.kind = .back ->
          ∃ c body,
            ed.src.kind = .exprExit body ∧
            ed.dst.kind = .exprEntry c) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTargets nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTargets nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTargets nextId stmt ed hed hkind
      cases stmt
        <;> simp only [buildStmt, List.cons_append,
          List.nil_append, List.mem_cons, List.mem_append] at hed
      case Decl τ init =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
      case Assign x rhs =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
      case Seq s₁ s₂ =>
        rcases hed with h | h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h with h | h
          · exact ihStmt _ _ _ _ h hkind
          · exact ihStmt _ _ _ _ h hkind
      case Do e =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h hkind
    · intro breakTargets nextId expr ed hed hkind
      cases expr <;>
        try
          (simp only [buildExpr, List.mem_cons, List.not_mem_nil,
            or_false, List.cons_append, List.nil_append, List.append_assoc,
            List.mem_append] at hed)
      all_goals
        try (subst ed; simp [mkEdge] at hkind)
      case BinOp a₁ a₂ op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · simp only [mkEdge] at h₃
          rcases h₃ with h₁ | (h₂ | h₃)
          · subst ed
            simp at hkind
          · exact ihExpr _ _ _ _ h₂ hkind
          · exact ihExpr _ _ _ _ h₃ hkind
      case UnOp a op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr _ _ _ _ h₃ hkind
      case If cond e₁ e₂ =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₆ with h | h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case While cond body =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          refine ⟨cond, body, ?_⟩
          constructor
          · simpa [mkEdge] using
              (buildExpr_exit_kind
                ({ id := nextId + 1, kind := .exprExit (.While cond body) } :: breakTargets)
                ((buildExpr ({
                    id := nextId + 1,
                    kind := .exprExit (.While cond body)
                  } :: breakTargets)
                  (nextId + 2) n cond).nextId)
                n body)
          · simpa [mkEdge] using
              (buildExpr_entry_kind
                ({ id := nextId + 1, kind := .exprExit (.While cond body) } :: breakTargets)
                (nextId + 2) n cond)
        · rcases h₅ with h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case Break l =>
        split at hed
        · simp [mkEdge] at hed; subst ed; simp at hkind
        · simp at hed
      case Scope s res =>
        rcases hed with h₁ | h₂ | h₃ | h₄
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₄ with h | h
          · exact ihStmt _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind

/--
Statement-builder specialization of back-edge shape. Use: one-step bridge from
builder internals to stmtCFG-level theorem `stmtCFG_back_edge_shape`.
-/
theorem buildStmt_back_edge_shape
    (breakTargets : List CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    ∀ ed ∈ (buildStmt breakTargets nextId fuel stmt).edges,
      ed.kind = .back ->
      ∃ c body,
        ed.src.kind = .exprExit body ∧
        ed.dst.kind = .exprEntry c := by
  intro ed hed hkind
  exact (back_edge_shape_mutual fuel).1 breakTargets nextId stmt ed hed hkind

/--
Expression-builder specialization of back-edge shape. Use: reusable local fact
for expression-only analyses involving while-loop back edges.
-/
theorem buildExpr_back_edge_shape
    (breakTargets : List CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    ∀ ed ∈ (buildExpr breakTargets nextId fuel expr).edges,
      ed.kind = .back ->
      ∃ c body,
        ed.src.kind = .exprExit body ∧
        ed.dst.kind = .exprEntry c := by
  intro ed hed hkind
  exact (back_edge_shape_mutual fuel).2 breakTargets nextId expr ed hed hkind

/--
Lifts builder-level back-edge shape to full statement CFGs. Use: canonical
stmtCFG-level formulation consumed by `stmtCFG_back_edges_are_loop_back`.
-/
theorem stmtCFG_back_edge_shape (s : Lang .Stmt) :
    ∀ e ∈ (stmtCFG s).edges,
      e.kind = .back ->
      ∃ c body,
        e.src.kind = .exprExit body ∧
        e.dst.kind = .exprEntry c := by
  unfold stmtCFG
  intro e he hkind
  exact buildStmt_back_edge_shape [] 0 (stmtSize s) s e he hkind

/--
In any statement CFG, boolean branch edges originate at condition exits. Use:
structural precondition for branch-sensitive transfer/soundness arguments.
-/
theorem stmtCFG_true_false_edges_from_exprExit (s : Lang .Stmt) :
    ∀ e ∈ (stmtCFG s).edges,
      e.kind = .trueBranch ∨ e.kind = .falseBranch ->
      ∃ cond, e.src.kind = .exprExit cond := by
  intro e he hk
  unfold stmtCFG at he
  simpa using
    buildStmt_branch_src_exprExit _ _ _ s e he hk

/--
User-facing back-edge theorem: every back edge in a statement CFG is a loop-back
from body exit to condition entry. Use: loop structure invariant at CFG level.
-/
theorem stmtCFG_back_edges_are_loop_back (s : Lang .Stmt) :
    ∀ e ∈ (stmtCFG s).edges,
      e.kind = .back ->
      ∃ c body,
        e.src.kind = .exprExit body ∧
        e.dst.kind = .exprEntry c := by
  intros e he hkind
  simpa using stmtCFG_back_edge_shape s e he hkind

/--
Specifies when a list of break targets is valid for proofs: every entry is an
`exprExit` node of some loop expression. Use: invariant threaded through the
mutual break-edge proof.
-/
private def BreakTargetsWellFormed : List CFGNode -> Prop
  | [] => True
  | t :: ts => (∃ loopExpr, t.kind = .exprExit loopExpr) ∧ BreakTargetsWellFormed ts

private theorem BreakTargetsWellFormed.getIdx
    {targets : List CFGNode} (hwf : BreakTargetsWellFormed targets)
    {i : Nat} (hi : i < targets.length) :
    ∃ loopExpr, (targets[i]).kind = .exprExit loopExpr := by
  induction targets generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => exact hwf.1
    | succ j =>
      refine ih hwf.2 _

/--
Mutual fuel-induction core for break edges under a well-formed break target:
every `.breakOut` edge points to an `exprExit _`. Use: shared engine for
`buildStmt_break_edge_target_exprExit`.
-/
private theorem break_edge_target_exprExit_mutual :
    ∀ fuel,
      (∀ (breakTargets : List CFGNode),
          BreakTargetsWellFormed breakTargets ->
          ∀ (nextId : Nat) (stmt : Lang .Stmt) (ed : CFGEdge),
          ed ∈ (buildStmt breakTargets nextId fuel stmt).edges ->
          ed.kind = .breakOut ->
          ∃ loopExpr, ed.dst.kind = .exprExit loopExpr) ∧
      (∀ (breakTargets : List CFGNode),
          BreakTargetsWellFormed breakTargets ->
          ∀ (nextId : Nat) (expr : Lang .Expr) (ed : CFGEdge),
          ed ∈ (buildExpr breakTargets nextId fuel expr).edges ->
          ed.kind = .breakOut ->
          ∃ loopExpr, ed.dst.kind = .exprExit loopExpr) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTargets hbt nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTargets hbt nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTargets hbt nextId stmt ed hed hkind
      cases stmt
        <;> simp only [buildStmt, List.cons_append,
          List.nil_append, List.mem_cons, List.mem_append] at hed
      case Decl τ init =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTargets hbt _ _ _ h hkind
      case Assign x rhs =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTargets hbt _ _ _ h hkind
      case Seq s₁ s₂ =>
        rcases hed with h | h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h with h | h
          · exact ihStmt breakTargets hbt _ _ _ h hkind
          · exact ihStmt breakTargets hbt _ _ _ h hkind
      case Do e =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTargets hbt _ _ _ h hkind
    · intro breakTargets hbt nextId expr ed hed hkind
      cases expr <;>
        try
          (simp only [buildExpr, List.mem_cons, List.not_mem_nil,
            or_false, List.cons_append, List.nil_append, List.append_assoc,
            List.mem_append] at hed)
      all_goals
        try (subst ed; simp [mkEdge] at hkind)
      case BinOp a₁ a₂ op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · simp only [mkEdge] at h₃
          rcases h₃ with h₁ | (h₂ | h₃)
          · subst ed
            simp at hkind
          · exact ihExpr breakTargets hbt _ _ _ h₂ hkind
          · exact ihExpr breakTargets hbt _ _ _ h₃ hkind
      case UnOp a op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTargets hbt _ _ _ h₃ hkind
      case If cond e₁ e₂ =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₆ with h | h | h
          · exact ihExpr breakTargets hbt _ _ _ h hkind
          · exact ihExpr breakTargets hbt _ _ _ h hkind
          · exact ihExpr breakTargets hbt _ _ _ h hkind
      case While cond body =>
        rcases hed with h₁ | h₂ | h₃ | h₄ | h₅
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₅ with h | h
          · exact ihExpr
              ({ id := nextId + 1, kind := .exprExit (.While cond body) } :: breakTargets)
              (by exact ⟨⟨.While cond body, rfl⟩, hbt⟩)
              _ _ _ h hkind
          · exact ihExpr
              ({ id := nextId + 1, kind := .exprExit (.While cond body) } :: breakTargets)
              (by exact ⟨⟨.While cond body, rfl⟩, hbt⟩)
              _ _ _ h hkind
      case Break l =>
        split at hed
        next h =>
          simp only [mkEdge, List.mem_cons, List.not_mem_nil, or_false] at hed
          subst ed
          exact BreakTargetsWellFormed.getIdx hbt h
        next h =>
          simp at hed
      case Scope s res =>
        rcases hed with h₁ | h₂ | h₃ | h₄
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₄ with h | h
          · exact ihStmt breakTargets hbt _ _ _ h hkind
          · exact ihExpr breakTargets hbt _ _ _ h hkind

/--
Statement-builder specialization of break-edge target shape, parameterized by a
well-formed break target. Use: final step to derive the stmtCFG theorem below.
-/
theorem buildStmt_break_edge_target_exprExit
    (breakTargets : List CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt)
    (hbt : BreakTargetsWellFormed breakTargets) :
    ∀ ed ∈ (buildStmt breakTargets nextId fuel stmt).edges,
      ed.kind = .breakOut ->
      ∃ loopExpr, ed.dst.kind = .exprExit loopExpr := by
  intro ed hed hkind
  exact (break_edge_target_exprExit_mutual fuel).1 breakTargets hbt nextId stmt ed hed hkind

/--
User-facing break theorem: every `.breakOut` edge in a statement CFG targets a
loop-exit node (`exprExit _`). Use: validates break-flow structure in analyses.
-/
theorem stmtCFG_break_edges_target_loop_exit (s : Lang .Stmt) :
    ∀ e ∈ (stmtCFG s).edges,
      e.kind = .breakOut ->
        ∃ loopExpr, e.dst.kind = .exprExit loopExpr := by
  intros e he hkind
  unfold stmtCFG at he
  exact buildStmt_break_edge_target_exprExit [] 0 (stmtSize s) s
    (by simp [BreakTargetsWellFormed]) e he hkind

end Translation

open Internal
section BuilderEdgeLemmas

/-- Literals and Var: entry -> exit (normal edge). -/
theorem buildExpr_literal_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (e : Lang .Expr)
    (hlit : e = .True ∨ e = .False ∨ e = .Nat n ∨ e = .Unit) :
    let entry : CFGNode := { id := nextId, kind := .exprEntry e }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit e }
    mkEdge entry exit ∈ (buildExpr breakTargets nextId (fuel + 1) e).edges := by
  rcases hlit with (rfl | rfl | rfl | rfl) <;> simp [buildExpr]

theorem buildExpr_var_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (e : Lang .Expr)
    (hvar : e = .Var x) :
    let entry : CFGNode := { id := nextId, kind := .exprEntry e }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit e }
    mkEdge entry exit ∈ (buildExpr breakTargets nextId (fuel + 1) e).edges := by
  simp [buildExpr, hvar]

/-- BinOp: entry -> r₁.entry, r₁.exit -> r₂.entry, r₂.exit -> exit. -/
theorem buildExpr_binop_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (e₁ e₂ : Lang .Expr) (op : BinOp) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.BinOp e₁ e₂ op)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.BinOp e₁ e₂ op) }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit (.BinOp e₁ e₂ op) }
    let r₁ := buildExpr breakTargets (nextId + 2) fuel e₁
    let r₂ := buildExpr breakTargets r₁.nextId fuel e₂
    mkEdge entry r₁.entry ∈ r.edges
    ∧ mkEdge r₁.exit r₂.entry ∈ r.edges
    ∧ mkEdge r₂.exit exit ∈ r.edges := by
  split_ands <;> simp [buildExpr]

/-- UnOp: entry -> r.entry, r.exit -> exit. -/
theorem buildExpr_unop_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (arg : Lang .Expr) (op : UnOp) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.UnOp arg op)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.UnOp arg op) }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit (.UnOp arg op) }
    let rArg := buildExpr breakTargets (nextId + 2) fuel arg
    mkEdge entry rArg.entry ∈ r.edges
    ∧ mkEdge rArg.exit exit ∈ r.edges := by
  split_ands <;> simp [buildExpr]

/-- If: entry -> c.entry, c.exit -> t.entry (trueBranch), c.exit -> f.entry (falseBranch),
    t.exit -> exit, f.exit -> exit. -/
theorem buildExpr_if_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.If cond e₁ e₂)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.If cond e₁ e₂) }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit (.If cond e₁ e₂) }
    let c := buildExpr breakTargets (nextId + 2) fuel cond
    let t := buildExpr breakTargets c.nextId fuel e₁
    let f := buildExpr breakTargets t.nextId fuel e₂
    mkEdge entry c.entry ∈ r.edges
    ∧ mkEdge c.exit t.entry .trueBranch ∈ r.edges
    ∧ mkEdge c.exit f.entry .falseBranch ∈ r.edges
    ∧ mkEdge t.exit exit ∈ r.edges
    ∧ mkEdge f.exit exit ∈ r.edges := by
  split_ands <;> simp [buildExpr]

/-- While: entry -> c.entry, c.exit -> b.entry (trueBranch),
    c.exit -> exit (falseBranch), b.exit -> c.entry (back). -/
theorem buildExpr_while_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (cond body : Lang .Expr) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.While cond body)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.While cond body) }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit (.While cond body) }
    let c := buildExpr (exit :: breakTargets) (nextId + 2) fuel cond
    let b := buildExpr (exit :: breakTargets) c.nextId fuel body
    mkEdge entry c.entry ∈ r.edges
    ∧ mkEdge c.exit b.entry .trueBranch ∈ r.edges
    ∧ mkEdge c.exit exit .falseBranch ∈ r.edges
    ∧ mkEdge b.exit c.entry .back ∈ r.edges := by
  split_ands <;> simp [buildExpr]

/-- Break l: if `l < breakTargets.length`, emits a breakOut edge
    from entry to `breakTargets[l]`. -/
theorem buildExpr_break_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (l : Nat) (hl : l < breakTargets.length) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.Break l)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.Break l) }
    mkEdge entry (breakTargets[l]) .breakOut ∈ r.edges := by
  grind [buildExpr, mkEdge]

/-- Scope: entry -> sRes.entry, sRes.exit -> rRes.entry, rRes.exit -> exit. -/
theorem buildExpr_scope_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (s : Lang .Stmt) (res : Lang .Expr) :
    let r := buildExpr breakTargets nextId (fuel + 1) (.Scope s res)
    let entry : CFGNode := { id := nextId, kind := .exprEntry (.Scope s res) }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit (.Scope s res) }
    let sRes := buildStmt breakTargets (nextId + 2) fuel s
    let rRes := buildExpr breakTargets sRes.nextId fuel res
    mkEdge entry sRes.entry ∈ r.edges
    ∧ mkEdge sRes.exit rRes.entry ∈ r.edges
    ∧ mkEdge rRes.exit exit ∈ r.edges := by
  split_ands <;> simp [buildExpr]

/-- Decl: entry -> r.entry, r.exit -> exit. -/
theorem buildStmt_decl_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (ty : Ty) (init : Lang .Expr) :
    let r := buildStmt breakTargets nextId (fuel + 1) (.Decl ty init)
    let entry : CFGNode := { id := nextId, kind := .stmtEntry (.Decl ty init) }
    let exit : CFGNode := { id := nextId + 1, kind := .stmtExit (.Decl ty init) }
    let rInit := buildExpr breakTargets (nextId + 2) fuel init
    mkEdge entry rInit.entry ∈ r.edges
    ∧ mkEdge rInit.exit exit ∈ r.edges := by
  split_ands <;> simp [buildStmt]

/-- Assign: entry -> r.entry, r.exit -> exit. -/
theorem buildStmt_assign_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (v : VarName) (rhs : Lang .Expr) :
    let r := buildStmt breakTargets nextId (fuel + 1) (.Assign v rhs)
    let entry : CFGNode := { id := nextId, kind := .stmtEntry (.Assign v rhs) }
    let exit : CFGNode := { id := nextId + 1, kind := .stmtExit (.Assign v rhs) }
    let rRhs := buildExpr breakTargets (nextId + 2) fuel rhs
    mkEdge entry rRhs.entry ∈ r.edges
    ∧ mkEdge rRhs.exit exit ∈ r.edges := by
  split_ands <;> simp [buildStmt]

/-- Seq: entry -> r₁.entry, r₁.exit -> r₂.entry, r₂.exit -> exit. -/
theorem buildStmt_seq_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (s₁ s₂ : Lang .Stmt) :
    let r := buildStmt breakTargets nextId (fuel + 1) (.Seq s₁ s₂)
    let entry : CFGNode := { id := nextId, kind := .stmtEntry (.Seq s₁ s₂) }
    let exit : CFGNode := { id := nextId + 1, kind := .stmtExit (.Seq s₁ s₂) }
    let r₁ := buildStmt breakTargets (nextId + 2) fuel s₁
    let r₂ := buildStmt breakTargets r₁.nextId fuel s₂
    mkEdge entry r₁.entry ∈ r.edges
    ∧ mkEdge r₁.exit r₂.entry ∈ r.edges
    ∧ mkEdge r₂.exit exit ∈ r.edges := by
  split_ands <;> simp [buildStmt]

/-- Do (ExprStmt): entry -> r.entry, r.exit -> exit. -/
theorem buildStmt_do_edges (breakTargets : List CFGNode) (nextId fuel : Nat)
    (e : Lang .Expr) :
    let r := buildStmt breakTargets nextId (fuel + 1) (.Do e)
    let entry : CFGNode := { id := nextId, kind := .stmtEntry (.Do e) }
    let exit : CFGNode := { id := nextId + 1, kind := .stmtExit (.Do e) }
    let rExpr := buildExpr breakTargets (nextId + 2) fuel e
    mkEdge entry rExpr.entry ∈ r.edges
    ∧ mkEdge rExpr.exit exit ∈ r.edges := by
  split_ands <;> simp [buildStmt]

end BuilderEdgeLemmas

section TranslationTests

set_option relaxedAutoImplicit true

/-!
## Entry-edge invariants

`ExprEntryEdgeInv g e n ex` stores all CFG edges emanating from the entry
node `n` of expression `e`, together with the kinds and membership of
intermediate child nodes.  One constructor per expression form.

`StmtEntryEdgeInv g st n ex` is the analogous invariant for statements.
-/
mutual
inductive ExprEntryEdgeInv (g : CFG) : List CFGNode -> Lang .Expr ->
    CFGNode -> CFGNode -> Prop where
  /-- Literal True: single edge entry -> exit. -/
  | litTrue (breakTargets : List CFGNode) (n ex : CFGNode) :
      CFGStep g n ex ->
      ExprEntryEdgeInv g breakTargets .True n ex
  /-- Literal False: single edge entry -> exit. -/
  | litFalse (breakTargets : List CFGNode) (n ex : CFGNode) :
      CFGStep g n ex ->
      ExprEntryEdgeInv g breakTargets .False n ex
  /-- Literal Nat: single edge entry -> exit. -/
  | litNat (breakTargets : List CFGNode) (v : Nat) (n ex : CFGNode) :
      CFGStep g n ex ->
      ExprEntryEdgeInv g breakTargets (.Nat v) n ex
  /-- Literal Unit: single edge entry -> exit. -/
  | litUnit (breakTargets : List CFGNode) (n ex : CFGNode) :
      CFGStep g n ex ->
      ExprEntryEdgeInv g breakTargets .Unit n ex
  /-- Variable: single edge entry -> exit. -/
  | var (breakTargets : List CFGNode) (x : VarName) (n ex : CFGNode) :
      CFGStep g n ex ->
      ExprEntryEdgeInv g breakTargets (.Var x) n ex
  /-- BinOp: entry -> e₁.entry; also stores e₁.exit -> e₂.entry, e₂.exit -> exit,
      plus child node kinds and membership for building ContCFGInv. -/
  | binop (breakTargets : List CFGNode) (op : BinOp) (e₁ e₂ : Lang .Expr)
      (n ex e₁en e₁ex e₂en e₂ex : CFGNode) :
      CFGStep g n e₁en ->
      e₁en.kind = .exprEntry e₁ -> e₁ex.kind = .exprExit e₁ ->
      e₂en.kind = .exprEntry e₂ -> e₂ex.kind = .exprExit e₂ ->
      CFGStep g e₁ex e₂en -> CFGStep g e₂ex ex ->
      e₁en ∈ g.nodes -> e₁ex ∈ g.nodes ->
      e₂en ∈ g.nodes -> e₂ex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets e₁ e₁en e₁ex ->
      ExprEntryEdgeInv g breakTargets e₂ e₂en e₂ex ->
      ExprEntryEdgeInv g breakTargets (.BinOp e₁ e₂ op) n ex
  /-- UnOp: entry -> arg.entry; also stores arg.exit -> exit. -/
  | unop (breakTargets : List CFGNode) (op : UnOp) (arg : Lang .Expr) (n ex aen aex : CFGNode) :
      CFGStep g n aen ->
      aen.kind = .exprEntry arg -> aex.kind = .exprExit arg ->
      CFGStep g aex ex ->
      aen ∈ g.nodes -> aex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets arg aen aex ->
      ExprEntryEdgeInv g breakTargets (.UnOp arg op) n ex
  /-- If: entry -> cond.entry; stores cond.exit -> t/f entries, t/f exits -> exit. -/
  | ife (breakTargets : List CFGNode) (cond e₁ e₂ : Lang .Expr)
      (n ex cen cex e₁en e₁ex e₂en e₂ex : CFGNode) :
      CFGStep g n cen ->
      cen.kind = .exprEntry cond -> cex.kind = .exprExit cond ->
      e₁en.kind = .exprEntry e₁ -> e₁ex.kind = .exprExit e₁ ->
      e₂en.kind = .exprEntry e₂ -> e₂ex.kind = .exprExit e₂ ->
      CFGStep g cex e₁en -> CFGStep g cex e₂en ->
      CFGStep g e₁ex ex -> CFGStep g e₂ex ex ->
      cen ∈ g.nodes -> cex ∈ g.nodes ->
      e₁en ∈ g.nodes -> e₁ex ∈ g.nodes ->
      e₂en ∈ g.nodes -> e₂ex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets cond cen cex ->
      ExprEntryEdgeInv g breakTargets e₁ e₁en e₁ex ->
      ExprEntryEdgeInv g breakTargets e₂ e₂en e₂ex ->
      ExprEntryEdgeInv g breakTargets (.If cond e₁ e₂) n ex
  /-- While: entry -> cond.entry; stores cond.exit -> body/exit, body.exit -> cond.entry. -/
  | whil (breakTargets : List CFGNode) (cond body : Lang .Expr) (n ex cen cex ben bex : CFGNode) :
      CFGStep g n cen ->
      cen.kind = .exprEntry cond -> cex.kind = .exprExit cond ->
      ben.kind = .exprEntry body -> bex.kind = .exprExit body ->
      CFGStep g cex ben -> CFGStep g cex ex ->
      CFGStep g bex cen ->
      cen ∈ g.nodes -> cex ∈ g.nodes ->
      ben ∈ g.nodes -> bex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets cond cen cex ->
      ExprEntryEdgeInv g (ex :: breakTargets) body ben bex ->
      ExprEntryEdgeInv g breakTargets (.While cond body) n ex
  /-- Break l: entry -> breakTargets[l] (breakOut edge). -/
  | brk (breakTargets : List CFGNode) (l : Nat) (n ex target : CFGNode)
      (hl : l < breakTargets.length) (htarget : target = breakTargets[l])
      (hkind : ∃ loopExpr, target.kind = .exprExit loopExpr)
      (hmem : target ∈ g.nodes) :
      CFGStep g n target ->
      ExprEntryEdgeInv g breakTargets (.Break l) n ex
  /-- Scope: entry -> s.entry; stores s.exit -> res.entry, res.exit -> exit. -/
  | scope (breakTargets : List CFGNode) (st : Lang .Stmt) (res : Lang .Expr)
      (n ex sen sex ren rex : CFGNode) :
      CFGStep g n sen ->
      sen.kind = .stmtEntry st -> sex.kind = .stmtExit st ->
      ren.kind = .exprEntry res -> rex.kind = .exprExit res ->
      CFGStep g sex ren -> CFGStep g rex ex ->
      sen ∈ g.nodes -> sex ∈ g.nodes ->
      ren ∈ g.nodes -> rex ∈ g.nodes ->
      StmtEntryEdgeInv g breakTargets st sen sex ->
      ExprEntryEdgeInv g breakTargets res ren rex ->
      ExprEntryEdgeInv g breakTargets (.Scope st res) n ex

inductive StmtEntryEdgeInv (g : CFG) :
    List CFGNode -> Lang .Stmt -> CFGNode -> CFGNode -> Prop where
  /-- Decl: entry -> init.entry; stores init.exit -> exit. -/
  | decl (breakTargets : List CFGNode) (ty : Ty) (init : Lang .Expr) (n ex ien iex : CFGNode) :
      CFGStep g n ien ->
      ien.kind = .exprEntry init -> iex.kind = .exprExit init ->
      CFGStep g iex ex ->
      ien ∈ g.nodes -> iex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets init ien iex ->
      StmtEntryEdgeInv g breakTargets (.Decl ty init) n ex
  /-- Assign: entry -> rhs.entry; stores rhs.exit -> exit. -/
  | assign (breakTargets : List CFGNode) (v : VarName) (rhs : Lang .Expr) (n ex ren rex : CFGNode) :
      CFGStep g n ren ->
      ren.kind = .exprEntry rhs -> rex.kind = .exprExit rhs ->
      CFGStep g rex ex ->
      ren ∈ g.nodes -> rex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets rhs ren rex ->
      StmtEntryEdgeInv g breakTargets (.Assign v rhs) n ex
  /-- Seq: entry -> s₁.entry; stores s₁.exit -> s₂.entry, s₂.exit -> exit. -/
  | seq (breakTargets : List CFGNode) (s₁ s₂ : Lang .Stmt) (n ex s₁en s₁ex s₂en s₂ex : CFGNode) :
      CFGStep g n s₁en ->
      s₁en.kind = .stmtEntry s₁ -> s₁ex.kind = .stmtExit s₁ ->
      s₂en.kind = .stmtEntry s₂ -> s₂ex.kind = .stmtExit s₂ ->
      CFGStep g s₁ex s₂en -> CFGStep g s₂ex ex ->
      s₁en ∈ g.nodes -> s₁ex ∈ g.nodes ->
      s₂en ∈ g.nodes -> s₂ex ∈ g.nodes ->
      StmtEntryEdgeInv g breakTargets s₁ s₁en s₁ex ->
      StmtEntryEdgeInv g breakTargets s₂ s₂en s₂ex ->
      StmtEntryEdgeInv g breakTargets (.Seq s₁ s₂) n ex
  /-- Do: entry -> e.entry; stores e.exit -> exit. -/
  | do_ (breakTargets : List CFGNode) (e : Lang .Expr) (n ex een eex : CFGNode) :
      CFGStep g n een ->
      een.kind = .exprEntry e -> eex.kind = .exprExit e ->
      CFGStep g eex ex ->
      een ∈ g.nodes -> eex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets e een eex ->
      StmtEntryEdgeInv g breakTargets (.Do e) n ex
end

lemma CFG_subgraph_step {g₁ g₂ n₁ n₂} (hstep : CFGStep g₁ n₁ n₂)
  (hsub : ∀ ed, ed ∈ g₁.edges -> ed ∈ g₂.edges) : CFGStep g₂ n₁ n₂ := by grind [CFGStep]

theorem CFGStep_mono {g₁ n m g₂} (h : CFGStep g₁ n m) (hsub : ∀ ed ∈ g₁.edges, ed ∈ g₂.edges) :
    CFGStep g₂ n m := by grind [CFGStep]

@[grind ->, grind .]
theorem CFGStep_dst_mem_nodes {g : CFG} {n m : CFGNode}
    (hstep : CFGStep g n m) : m ∈ g.nodes := by
  obtain ⟨e, he_mem, he_src, he_dst⟩ := hstep
  subst he_src; subst he_dst
  unfold CFG.nodes
  rw [<- List.mem_eraseDups]
  generalize g.edges = edges at he_mem ⊢
  induction edges with
  | nil => simp at he_mem
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.mem_cons]
    cases he_mem
    case head => grind
    case tail h =>
      right; right
      apply ih h

@[grind ->, grind .]
theorem CFGStep_src_mem_nodes {g : CFG} {n m : CFGNode}
    (hstep : CFGStep g n m) : n ∈ g.nodes := by
  obtain ⟨e, he_mem, he_src, he_dst⟩ := hstep
  subst he_src; subst he_dst
  unfold CFG.nodes
  rw [← List.mem_eraseDups]
  generalize g.edges = edges at he_mem ⊢
  induction edges with
  | nil => simp at he_mem
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.mem_cons]
    cases he_mem
    case head => grind
    case tail h =>
      right; right
      apply ih h

local macro "lift_cfg" : tactic => `(tactic| all_goals first
  | exact CFG_subgraph_step ‹_› ‹_›
  | exact CFGStep_dst_mem_nodes (CFG_subgraph_step ‹_› ‹_›)
  | exact CFGStep_src_mem_nodes (CFG_subgraph_step ‹_› ‹_›))

mutual
theorem ExprEntryEdgeInv.mono {g₁ bts e n ex g₂}
    (h : ExprEntryEdgeInv g₁ bts e n ex)
    (hsub : ∀ ed, ed ∈ g₁.edges -> ed ∈ g₂.edges) :
    ExprEntryEdgeInv g₂ bts e n ex := by
  cases h with
  | litTrue | litFalse | litNat | litUnit | var =>
    constructor; exact CFG_subgraph_step (by assumption) hsub
  | binop _ o e1 e2 _ _ e1en e1ex e2en e2ex _ hk1 hk2 hk3 hk4 _ _ _ _ _ _ he1 he2 =>
    refine .binop _ o e1 e2 _ _ e1en e1ex e2en e2ex
      ?_ hk1 hk2 hk3 hk4 ?_ ?_ ?_ ?_ ?_ ?_ (he1.mono hsub) (he2.mono hsub) <;> lift_cfg
  | unop _ o e _ _ aen aex _ hk1 hk2 _ _ _ he =>
    refine .unop _ o e _ _ aen aex ?_ hk1 hk2 ?_ ?_ ?_ (he.mono hsub) <;> lift_cfg
  | ife _ c e₁ e₂ _ _ cen cex e₁en e₁ex e₂en e₂ex _ hk1 hk2 hk3 hk4 hk5 hk6
      _ _ _ _ _ _ _ _ _ _ hc he1 he2 =>
    refine .ife _ c e₁ e₂ _ _ cen cex e₁en e₁ex e₂en e₂ex
      ?_ hk1 hk2 hk3 hk4 hk5 hk6 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (hc.mono hsub) (he1.mono hsub) (he2.mono hsub) <;> lift_cfg
  | whil _ c b _ _ cen cex ben bex _ hk1 hk2 hk3 hk4 _ _ _ _ _ _ _ hc hb =>
    refine .whil _ c b _ _ cen cex ben bex
      ?_ hk1 hk2 hk3 hk4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hc.mono hsub) (hb.mono hsub) <;> lift_cfg
  | brk _ l _ _ target hl ht hk _ hs =>
    exact .brk _ l _ _ target hl ht hk
      (CFGStep_dst_mem_nodes (CFG_subgraph_step hs hsub)) (CFG_subgraph_step hs hsub)
  | scope _ st res _ _ sen sex ren rex _ hk1 hk2 hk3 hk4 _ _ _ _ _ _ hs hr =>
    refine .scope _ st res _ _ sen sex ren rex
      ?_ hk1 hk2 hk3 hk4 ?_ ?_ ?_ ?_ ?_ ?_ (hs.mono hsub) (hr.mono hsub) <;> lift_cfg

theorem StmtEntryEdgeInv.mono {g1 bts st n ex g₂}
    (h : StmtEntryEdgeInv g1 bts st n ex)
    (hsub : forall ed, ed ∈ g1.edges -> ed ∈ g₂.edges) :
    StmtEntryEdgeInv g₂ bts st n ex := by
  cases h with
  | decl _ ty init _ _ ien iex _ hk1 hk2 _ _ _ he =>
    refine .decl _ ty init _ _ ien iex ?_ hk1 hk2 ?_ ?_ ?_ (he.mono hsub) <;> lift_cfg
  | assign _ v rhs _ _ ren rex _ hk1 hk2 _ _ _ he =>
    refine .assign _ v rhs _ _ ren rex ?_ hk1 hk2 ?_ ?_ ?_ (he.mono hsub) <;> lift_cfg
  | seq _ s₁ s₂ _ _ s₁en s₁ex s₂en s₂ex _ hk1 hk2 hk3 hk4 _ _ _ _ _ _ he1 he2 =>
    refine .seq _ s₁ s₂ _ _ s₁en s₁ex s₂en s₂ex
      ?_ hk1 hk2 hk3 hk4 ?_ ?_ ?_ ?_ ?_ ?_ (he1.mono hsub) (he2.mono hsub) <;> lift_cfg
  | do_ _ e _ _ een eex _ hk1 hk2 _ _ _ he =>
    refine .do_ _ e _ _ een eex ?_ hk1 hk2 ?_ ?_ ?_ (he.mono hsub) <;> lift_cfg
end

mutual
theorem buildExpr_entry_edge_inv
    (breakTargets : List CFGNode) (nextId fuel : Nat) (e : Lang .Expr)
    (hfuel : fuel >= exprSize e) :
    let r := buildExpr breakTargets nextId fuel e
    let g := CFG.mk r.entry r.exit r.edges
    ExprEntryEdgeInv g breakTargets e r.entry r.exit := by
  intros r g
  cases e with
  | Var
  | True
  | False
  | Nat
  | Unit =>
    constructor
    set e : CFGEdge := mkEdge r.entry r.exit
    exists e
    split_ands <;> try (unfold e; grind [mkEdge])
    cases fuel
    · simp [exprSize] at hfuel
    simp [g, r, buildExpr, e]
  | BinOp a₁ a₂ o =>
    cases fuel
    case zero => simp [exprSize] at hfuel
    case succ fuel =>
    simp only [exprSize] at hfuel
    set r₁ := buildExpr breakTargets (nextId + 2) fuel a₁
    set r₂ := buildExpr breakTargets r₁.nextId fuel a₂
    have hs1 : CFGStep g r.entry r₁.entry := by
      exists mkEdge r.entry r₁.entry
      grind [buildExpr, mkEdge]
    have hs2 : CFGStep g r₁.exit r₂.entry := by
      exists mkEdge r₁.exit r₂.entry
      grind [buildExpr, mkEdge]
    have hs3 : CFGStep g r₂.exit r.exit := by
      exists mkEdge r₂.exit r.exit
      grind [buildExpr, mkEdge]
    have he₁ := (buildExpr_entry_edge_inv breakTargets (nextId + 2) fuel a₁ (by omega)).mono
                  (g₂ := g) (by grind [buildExpr])
    have he₂ := (buildExpr_entry_edge_inv breakTargets r₁.nextId fuel a₂ (by omega)).mono
                  (g₂ := g) (by grind [buildExpr])
    refine .binop breakTargets o a₁ a₂ _ _ r₁.entry r₁.exit r₂.entry r₂.exit
      hs1
      ?_ ?_ ?_ ?_
      hs2 hs3
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      (CFGStep_dst_mem_nodes hs2) (CFGStep_src_mem_nodes hs3)
      he₁ he₂
    all_goals sorry
  | UnOp a o =>
    cases fuel
    case zero => simp [exprSize] at hfuel
    case succ fuel =>
    simp only [exprSize] at hfuel
    set r' := buildExpr breakTargets (nextId + 2) fuel a
    have hs1 : CFGStep g r.entry r'.entry := by
      exists mkEdge r.entry r'.entry
      grind [buildExpr, mkEdge]
    have hs2 : CFGStep g r'.exit r.exit := by
      exists mkEdge r'.exit r.exit
      grind [buildExpr, mkEdge]
    have he₁ := (buildExpr_entry_edge_inv breakTargets (nextId + 2) fuel a (by omega)).mono
                  (g₂ := g) (by grind [buildExpr])
    refine .unop breakTargets o a _ _ r'.entry r'.exit
      hs1
      ?_ ?_
      hs2
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      he₁
    all_goals sorry
  | If c e₁ e₂ =>
    cases fuel
    case zero => simp [exprSize] at hfuel
    case succ fuel =>
    simp only [exprSize] at hfuel
    sorry
  | While cond body =>
    cases fuel
    case zero => simp [exprSize] at hfuel
    case succ fuel =>
    simp only [exprSize] at hfuel
    set rc := buildExpr (r.exit :: breakTargets) (nextId + 2) fuel cond
    set rb := buildExpr (r.exit :: breakTargets) rc.nextId fuel body
    have hs1 : CFGStep g r.entry rc.entry := by
      exists mkEdge r.entry rc.entry
      grind [buildExpr, mkEdge]
    have hs2 : CFGStep g rc.exit rb.entry := by
      exists mkEdge rc.exit rb.entry .trueBranch
      grind [buildExpr, mkEdge]
    have hs3 : CFGStep g rc.exit r.exit := by
      exists mkEdge rc.exit r.exit .falseBranch
      grind [buildExpr, mkEdge]
    have hec := (buildExpr_entry_edge_inv (r.exit :: breakTargets) (nextId + 2) fuel cond
                  (by omega)).mono (g₂ := g) (by grind [buildExpr])
    have heb := (buildExpr_entry_edge_inv (r.exit :: breakTargets) rc.nextId fuel body
                  (by omega)).mono (g₂ := g) (by grind [buildExpr])
    sorry
  | Break l =>
    sorry -- out-of-bounds case has no edges; needs BreakTargetsWellFormed precondition
  | Scope s res =>
    cases fuel
    case zero => simp [exprSize] at hfuel
    case succ fuel =>
    simp only [exprSize] at hfuel
    set sr := buildStmt breakTargets (nextId + 2) fuel s
    set rr := buildExpr breakTargets sr.nextId fuel res
    have hs1 : CFGStep g r.entry sr.entry := by
      exists mkEdge r.entry sr.entry
      grind [buildExpr, mkEdge]
    have hs2 : CFGStep g sr.exit rr.entry := by
      exists mkEdge sr.exit rr.entry
      grind [buildExpr, mkEdge]
    have hs3 : CFGStep g rr.exit r.exit := by
      exists mkEdge rr.exit r.exit
      grind [buildExpr, mkEdge]
    have hes := (buildStmt_entry_edge_inv breakTargets (nextId + 2) fuel s (by omega)).mono
                  (g₂ := g) (by grind [buildExpr])
    have her := (buildExpr_entry_edge_inv breakTargets sr.nextId fuel res (by omega)).mono
                  (g₂ := g) (by grind [buildExpr])
    sorry

theorem buildStmt_entry_edge_inv
    (breakTargets : List CFGNode) (nextId fuel : Nat) (s : Lang .Stmt)
    (hfuel : fuel >= stmtSize s) :
    let r := buildStmt breakTargets nextId fuel s
    let g := CFG.mk r.entry r.exit r.edges
    StmtEntryEdgeInv g breakTargets s r.entry r.exit := by
  intros r g
  cases s with
  | Decl ty init =>
    cases fuel
    case zero => simp [stmtSize] at hfuel
    case succ fuel =>
    simp only [stmtSize] at hfuel
    set ri := buildExpr breakTargets (nextId + 2) fuel init
    have hs1 : CFGStep g r.entry ri.entry := by
      exists mkEdge r.entry ri.entry
      grind [buildStmt, mkEdge]
    have hs2 : CFGStep g ri.exit r.exit := by
      exists mkEdge ri.exit r.exit
      grind [buildStmt, mkEdge]
    have hei := (buildExpr_entry_edge_inv breakTargets (nextId + 2) fuel init (by omega)).mono
                  (g₂ := g) (by grind [buildStmt])
    refine .decl breakTargets ty init _ _ ri.entry ri.exit
      hs1
      ?_ ?_
      hs2
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      hei
    all_goals sorry
  | Assign v rhs =>
    cases fuel
    case zero => simp [stmtSize] at hfuel
    case succ fuel =>
    simp only [stmtSize] at hfuel
    set ri := buildExpr breakTargets (nextId + 2) fuel rhs
    have hs1 : CFGStep g r.entry ri.entry := by
      exists mkEdge r.entry ri.entry
      grind [buildStmt, mkEdge]
    have hs2 : CFGStep g ri.exit r.exit := by
      exists mkEdge ri.exit r.exit
      grind [buildStmt, mkEdge]
    have hei := (buildExpr_entry_edge_inv breakTargets (nextId + 2) fuel rhs (by omega)).mono
                  (g₂ := g) (by grind [buildStmt])
    refine .assign breakTargets v rhs _ _ ri.entry ri.exit
      hs1
      ?_ ?_
      hs2
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      hei
    all_goals sorry
  | Seq s₁ s₂ =>
    cases fuel
    case zero => simp [stmtSize] at hfuel
    case succ fuel =>
    simp only [stmtSize] at hfuel
    set r₁ := buildStmt breakTargets (nextId + 2) fuel s₁
    set r₂ := buildStmt breakTargets r₁.nextId fuel s₂
    have hs1 : CFGStep g r.entry r₁.entry := by
      exists mkEdge r.entry r₁.entry
      grind [buildStmt, mkEdge]
    have hs2 : CFGStep g r₁.exit r₂.entry := by
      exists mkEdge r₁.exit r₂.entry
      grind [buildStmt, mkEdge]
    have hs3 : CFGStep g r₂.exit r.exit := by
      exists mkEdge r₂.exit r.exit
      grind [buildStmt, mkEdge]
    have he₁ := (buildStmt_entry_edge_inv breakTargets (nextId + 2) fuel s₁ (by omega)).mono
                  (g₂ := g) (by grind [buildStmt])
    have he₂ := (buildStmt_entry_edge_inv breakTargets r₁.nextId fuel s₂ (by omega)).mono
                  (g₂ := g) (by grind [buildStmt])
    refine .seq breakTargets s₁ s₂ _ _ r₁.entry r₁.exit r₂.entry r₂.exit
      hs1
      ?_ ?_ ?_ ?_
      hs2 hs3
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      (CFGStep_dst_mem_nodes hs2) (CFGStep_src_mem_nodes hs3)
      he₁ he₂
    all_goals sorry
  | Do e =>
    cases fuel
    case zero => simp [stmtSize] at hfuel
    case succ fuel =>
    simp only [stmtSize] at hfuel
    set re := buildExpr breakTargets (nextId + 2) fuel e
    have hs1 : CFGStep g r.entry re.entry := by
      exists mkEdge r.entry re.entry
      grind [buildStmt, mkEdge]
    have hs2 : CFGStep g re.exit r.exit := by
      exists mkEdge re.exit r.exit
      grind [buildStmt, mkEdge]
    have hei := (buildExpr_entry_edge_inv breakTargets (nextId + 2) fuel e (by omega)).mono
                  (g₂ := g) (by grind [buildStmt])
    refine .do_ breakTargets e _ _ re.entry re.exit
      hs1
      ?_ ?_
      hs2
      (CFGStep_dst_mem_nodes hs1) (CFGStep_src_mem_nodes hs2)
      hei
    all_goals sorry
end

/-!
## Continuation-CFG invariant

`ContCFGInv g K x` asserts that when the current sub-computation finishes at
CFG node `x`, the continuation stack `K` describes exactly the CFG edges
leading back to `g.exit`.  Each constructor corresponds to a `Cont` frame and
records the CFG nodes and edges that the frame implies.
-/
inductive ContCFGInv (g : CFG) : List Cont -> CFGNode -> Prop where
  /-- Empty stack: the current exit IS the top-level exit. -/
  | halt : x = g.exit -> ContCFGInv g [] x
  /-- Left operand of BinOp done -> edge to right operand entry,
      then right exit -> parent exit.
      Also stores `ExprEntryEdgeInv` for `e₂` so that the successor
      `exprEntry` state can be constructed without a global lookup lemma. -/
  | binopLK (op : BinOp) (e₂ : Lang .Expr)
      (e₂en e₂ex pex : CFGNode) :
      e₂en.kind = .exprEntry e₂ ->
      e₂ex.kind = .exprExit e₂ ->
      CFGStep g x e₂en -> CFGStep g e₂ex pex ->
      e₂en ∈ g.nodes -> e₂ex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets e₂ e₂en e₂ex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.binopLK op e₂ :: K) x
  /-- Right operand of BinOp done -> edge to parent exit. -/
  | binopRK (op : BinOp) (v₁ : Value) (pex : CFGNode) :
      CFGStep g x pex -> ContCFGInv g K pex ->
      ContCFGInv g (.binopRK op v₁ :: K) x
  /-- Operand of UnOp done -> edge to parent exit. -/
  | unopK (op : UnOp) (pex : CFGNode) :
      CFGStep g x pex -> ContCFGInv g K pex ->
      ContCFGInv g (.unopK op :: K) x
  /-- Condition of If done -> trueBranch/falseBranch edges to branch
      entries, both branch exits -> parent exit.
      Stores `ExprEntryEdgeInv` for both branches. -/
  | ifCondK (e₁ e₂ : Lang .Expr)
      (e₁en e₁ex e₂en e₂ex pex : CFGNode) :
      e₁en.kind = .exprEntry e₁ ->
      e₁ex.kind = .exprExit e₁ ->
      e₂en.kind = .exprEntry e₂ ->
      e₂ex.kind = .exprExit e₂ ->
      CFGStep g x e₁en -> CFGStep g x e₂en ->
      CFGStep g e₁ex pex -> CFGStep g e₂ex pex ->
      e₁en ∈ g.nodes -> e₁ex ∈ g.nodes ->
      e₂en ∈ g.nodes -> e₂ex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets e₁ e₁en e₁ex ->
      ExprEntryEdgeInv g breakTargets e₂ e₂en e₂ex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.ifCondK e₁ e₂ :: K) x
  /-- Init expr of Decl done -> edge to stmt exit. -/
  | declK (ty : Ty) (sex : CFGNode) :
      CFGStep g x sex -> ContCFGInv g K sex ->
      ContCFGInv g (.declK ty :: K) x
  /-- RHS of Assign done -> edge to stmt exit. -/
  | assignK (v : VarName) (sex : CFGNode) :
      CFGStep g x sex -> ContCFGInv g K sex ->
      ContCFGInv g (.assignK v :: K) x
  /-- First statement of Seq done -> edge to s₂ entry,
      then s₂ exit -> parent exit.
      Stores `StmtEntryEdgeInv` for `s₂`. -/
  | seqK (s₂ : Lang .Stmt) (s₂en s₂ex pex : CFGNode) :
      s₂en.kind = .stmtEntry s₂ ->
      s₂ex.kind = .stmtExit s₂ ->
      CFGStep g x s₂en -> CFGStep g s₂ex pex ->
      s₂en ∈ g.nodes -> s₂ex ∈ g.nodes ->
      StmtEntryEdgeInv g breakTargets s₂ s₂en s₂ex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.seqK s₂ :: K) x
  /-- Expr of Do stmt done -> edge to stmt exit. -/
  | exprStmtK (sex : CFGNode) :
      CFGStep g x sex -> ContCFGInv g K sex ->
      ContCFGInv g (.exprStmtK :: K) x
  /-- Condition of While done (x = condExit).
      trueBranch -> bodyEntry, falseBranch -> whileExit,
      bodyExit -> condEntry (back edge).
      Stores `ExprEntryEdgeInv` for `body`. -/
  | loopK (c body : Lang .Expr) (n : Nat)
      (ben bex cen pex : CFGNode) :
      ben.kind = .exprEntry body ->
      bex.kind = .exprExit body ->
      cen.kind = .exprEntry c ->
      CFGStep g x ben -> CFGStep g x pex ->
      CFGStep g bex cen ->
      ben ∈ g.nodes -> bex ∈ g.nodes ->
      ExprEntryEdgeInv g (pex :: breakTargets) body ben bex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.loopK c body n :: K) x
  /-- Body of While done (x = bodyExit).
      back edge -> condEntry, then full loop structure from condExit.
      Stores `ExprEntryEdgeInv` for `c`. -/
  | loopContK (c body : Lang .Expr) (n : Nat)
      (cen cex ben bex pex : CFGNode) :
      cen.kind = .exprEntry c ->
      cex.kind = .exprExit c ->
      ben.kind = .exprEntry body ->
      bex.kind = .exprExit body ->
      CFGStep g x cen ->
      CFGStep g cex ben -> CFGStep g cex pex ->
      CFGStep g bex cen ->
      cen ∈ g.nodes -> cex ∈ g.nodes ->
      ExprEntryEdgeInv g (pex :: breakTargets) c cen cex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.loopContK c body n :: K) x
  /-- Statement part of Scope done -> edge to result expr entry,
      then result exit -> parent exit.
      Stores `ExprEntryEdgeInv` for the result expression. -/
  | scopeBodyK (e : Lang .Expr) (n : Nat)
      (een eex pex : CFGNode) :
      een.kind = .exprEntry e ->
      eex.kind = .exprExit e ->
      CFGStep g x een -> CFGStep g eex pex ->
      een ∈ g.nodes -> eex ∈ g.nodes ->
      ExprEntryEdgeInv g breakTargets e een eex ->
      ContCFGInv g K pex ->
      ContCFGInv g (.scopeBodyK e n :: K) x
  /-- Result expr of Scope done -> edge to parent exit. -/
  | scopeExitK (n : Nat) (pex : CFGNode) :
      CFGStep g x pex -> ContCFGInv g K pex ->
      ContCFGInv g (.scopeExitK n :: K) x

/-!
## Jump-context–CFG invariant

`JCFGInv g J breakTargets` relates the CEK jump context `J` to the list of
break-target CFG nodes threaded through the builder.  Each `J` entry's saved
continuation `K` is valid (via `ContCFGInv`) at the corresponding while-exit
node in `breakTargets`.
-/
inductive JCFGInv (g : CFG) : JStackCtx -> List CFGNode -> Prop where
  /-- Empty jump context corresponds to no break targets. -/
  | empty : JCFGInv g [] []
  /-- A loop nesting level: the saved continuation `K` is valid at the
      while-exit node `whileExit`, and the rest of `J` matches the rest
      of the break targets. -/
  | loop (n : Nat) (K : List Cont) (whileExit : CFGNode)
      (restJ : JStackCtx) (restTargets : List CFGNode) :
      (∃ loopExpr, whileExit.kind = .exprExit loopExpr) ->
      ContCFGInv g K whileExit ->
      JCFGInv g restJ restTargets ->
      JCFGInv g (⟨n, K⟩ :: restJ) (whileExit :: restTargets)

-- there are as many break targets as jump contexts
theorem JCFGInv.length_eq (h : JCFGInv g J bts) : J.length = bts.length := by
  induction h with
  | empty => rfl
  | loop => grind

theorem JCFGInv.getIdx (h : JCFGInv g J bts) :
    ∀ l, (hl : l < J.length) ->
    ContCFGInv g (J[l]'hl).2 (bts[l]'(h.length_eq ▸ hl)) := by
  induction h with
  | empty => intros l hl; cases hl
  | loop _ _ _ _ _ _ hcont _ ih =>
    intros l hl; cases l <;> grind

theorem JCFGInv.drop (h : JCFGInv g J bts) :
    ∀ l, (hl : l < J.length) ->
    JCFGInv g (J.drop (l+1)) (bts.drop (l+1)) := by
  induction h with
  | empty => intros l hl; cases hl
  | loop _ _ _ _ _ _ hcont _ ih =>
    intros l hl; cases l <;> grind

/-!
## CEK-to-CFG correspondence relation

`cfgcekRel s` relates a CEK state `σ` to a CFG node `n` when:
  1. `n` belongs to the CFG built for `s`,
  2. the CEK control component matches the node kind,
  3. the continuation stack satisfies `ContCFGInv` at the current node
     (for exit nodes) or at the corresponding exit node (for entry nodes),
  4. the jump context satisfies `JCFGInv` against the current break targets.

`ExprEntryEdgeInv`/`StmtEntryEdgeInv` are NOT stored in the relation.
Instead, they are carried inside `ContCFGInv` constructors that point to
entry nodes (e.g., `binopLK`, `ifCondK`, `seqK`, `loopK`, etc.), so that
the edge structure is available when transitioning from exit → entry states.

For entry nodes, the constructor stores the corresponding exit node `ex`
so that `ContCFGInv` can be anchored there.
-/
inductive cfgcekRel (s : Lang .Stmt) : StateRel where
  | exprEntry (e : Lang .Expr) (E : Environment) (J : JStackCtx) (K : List Cont)
      (breakTargets : List CFGNode) (n ex : CFGNode) :
      n.kind = .exprEntry e ->
      ex.kind = .exprExit e ->
      n ∈ (stmtCFG s).nodes ->
      ex ∈ (stmtCFG s).nodes ->
      ExprEntryEdgeInv (stmtCFG s) breakTargets e n ex ->
      ContCFGInv (stmtCFG s) K ex ->
      JCFGInv (stmtCFG s) J breakTargets ->
      cfgcekRel s ⟨.sourceExpr e, E, J, K⟩ n
  | exprExit (e : Lang .Expr) (v : Value) (E : Environment)
      (J : JStackCtx) (K : List Cont)
      (breakTargets : List CFGNode) (n : CFGNode) :
      n.kind = .exprExit e ->
      n ∈ (stmtCFG s).nodes ->
      ContCFGInv (stmtCFG s) K n ->
      JCFGInv (stmtCFG s) J breakTargets ->
      cfgcekRel s ⟨.value v, E, J, K⟩ n
  | stmtEntry (st : Lang .Stmt) (E : Environment) (J : JStackCtx) (K : List Cont)
      (breakTargets : List CFGNode) (n ex : CFGNode) :
      n.kind = .stmtEntry st ->
      ex.kind = .stmtExit st ->
      n ∈ (stmtCFG s).nodes ->
      ex ∈ (stmtCFG s).nodes ->
      StmtEntryEdgeInv (stmtCFG s) breakTargets st n ex ->
      ContCFGInv (stmtCFG s) K ex ->
      JCFGInv (stmtCFG s) J breakTargets ->
      cfgcekRel s ⟨.sourceStmt st, E, J, K⟩ n
  | stmtExit (st : Lang .Stmt) (E : Environment) (J : JStackCtx)
      (K : List Cont) (breakTargets : List CFGNode) (n : CFGNode) :
      n.kind = .stmtExit st ->
      n ∈ (stmtCFG s).nodes ->
      ContCFGInv (stmtCFG s) K n ->
      JCFGInv (stmtCFG s) J breakTargets ->
      cfgcekRel s ⟨.skip, E, J, K⟩ n

noncomputable def cfgcekRelReq (s : Lang .Stmt) :
    TranslationReq s (cfgcekRel s) where
  init_related := by
    exact cfgcekRel.stmtEntry s [] [] [] []
      (stmtCFG s).entry (stmtCFG s).exit
      (buildStmt_entry_kind [] 0 (stmtSize s) s)
      (buildStmt_exit_kind [] 0 (stmtSize s) s)
      (cfg_entry_in_nodes _)
      (cfg_exit_in_nodes _)
      (by grind [stmtCFG, buildStmt_entry_edge_inv])
      (ContCFGInv.halt rfl)
      JCFGInv.empty
  terminal_related := by
    intro E
    exact cfgcekRel.stmtExit s E [] [] []
      (stmtCFG s).exit
      (buildStmt_exit_kind [] 0 (stmtSize s) s)
      (cfg_exit_in_nodes _)
      (ContCFGInv.halt rfl)
      JCFGInv.empty

  step_sound := by
    intros σ σ' n hrel heval
    cases hrel with
    | exprEntry e E J K bts n ex hkind hekind hmemn hmemex heeei hcont hjinv =>
      cases heval
      case Val v =>
        exists ex
        cases v <;> simp only [liftValue] at * <;> cases heeei <;> refine ⟨?_, by assumption⟩
        all_goals
          constructor <;> assumption
      case Var v x =>
        exists ex
        cases heeei
        refine ⟨?_, by assumption⟩
        constructor <;> assumption
      case BinOp e₁ e₂ o =>
        cases heeei
        case binop e₁en e₁ex e₂en e₂ex _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exists e₁en
          refine ⟨?_, by assumption⟩
          constructor <;> try assumption
          constructor <;> assumption
      case UnOp e o =>
        cases heeei
        case unop aen aex _ _ _ _ _ _ _ =>
          exists aen
          refine ⟨?_, by assumption⟩
          constructor <;> try assumption
          constructor <;> assumption
      case If cond thn els =>
        cases heeei
        case ife cen cex thnn thnx elsn elsx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exists cen
          refine ⟨?_, by assumption⟩
          constructor <;> try assumption
          constructor <;> assumption
      case While cond body =>
        cases heeei
        case whil cen cex ben bex _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exists cen
          refine ⟨?_, by assumption⟩
          constructor <;> try assumption
          constructor <;> assumption
      case Break K' l =>
        cases heeei
        case brk trg hkind hmem hl htrg _ =>
          obtain ⟨le, hkind⟩ := hkind
          exists trg
          refine ⟨?_, by assumption⟩
          have hl' : l < J.length := hjinv.length_eq ▸ hl
          exact cfgcekRel.exprExit le (Value.Unit) (E.drop (E.length - J[l]!.1))
            (J.drop (l + 1)) (J[l]!.2) (bts.drop (l + 1)) trg
            hkind (by assumption)
            (by rw [htrg, show (J[l]! = J[l]) from by grind]; exact hjinv.getIdx l hl')
            (hjinv.drop l hl')
      case Scope st e =>
        cases heeei
        case scope sn sx rn rx _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exists sn
          refine ⟨?_, by assumption⟩
          exact cfgcekRel.stmtEntry st E J (.scopeBodyK e E.length :: K) bts sn sx
            (by assumption) (by assumption) (by assumption) (by assumption)
            (by assumption)
            (ContCFGInv.scopeBodyK e E.length rn rx ex
              (by assumption) (by assumption) (by assumption) (by assumption)
              (by assumption) (by assumption) (by assumption) hcont)
            hjinv
    | exprExit e v E J K bts n' hkind' hnodes hContInv hJInv =>
      cases heval
      case IfTrue K' s₁ s₂ =>
        cases hContInv
        case ifCondK bts' e₁en e₁ex e₂en e₂ex pex h₁step h₂step
          h₁nnode h₁xnode h₂nnode h₂xnode _ _ heeei₁ _ _ _ _ _ _ =>
        refine ⟨e₁en, ?_, by assumption⟩
        constructor <;> try assumption
        -- ⊢ ContCFGInv (stmtCFG s) K' e₁ex
        -- reasonaly sure this can't be proven
        · -- HERE
          sorry
        · sorry
      case IfFalse K' s₁ s₂ =>
        cases hContInv
        case ifCondK bts' e₁en e₁ex e₂en e₂ex pex h₁step h₂step
          h₁nnode h₁xnode h₂nnode h₂xnode _ _ _ _ _ _ _ _ _ =>
        refine ⟨e₂en, ?_, by assumption⟩
        constructor <;> try assumption
        -- ⊢ ContCFGInv (stmtCFG s) K' e₁ex
        -- reasonaly sure this can't be proven
        · sorry
        · sorry
      case VarDeclDone K' τ =>
        cases hContInv
        case declK sx hcont hstep =>
        refine ⟨sx, ?_, hstep⟩
        constructor <;> try assumption
        · sorry
        · refine CFGStep_dst_mem_nodes hstep
      case AssignDone K' x =>
        cases hContInv
        case assignK sx hcont hstep =>
        refine ⟨sx, ?_, hstep⟩
        constructor <;> try assumption
        · sorry
        · refine CFGStep_dst_mem_nodes hstep
      case BinOpL K' o rhs =>
        cases hContInv
        case binopLK bts' e₂en' _ _ _ _ _ _ _ _ _ _ =>
        refine ⟨e₂en', ?_, by assumption⟩
        constructor <;> try assumption
        constructor <;> try assumption
        sorry
      case BinOpR K' o v₁ v₂ hstep =>
        cases hContInv
        case binopRK pex hcont hstep =>
        refine ⟨pex, ?_, by assumption⟩
        constructor <;> try assumption
        · sorry
        · refine CFGStep_dst_mem_nodes hstep
      case UnOpDone K' o v hstep =>
        cases hContInv
        case unopK o pex hcont hstep =>
        refine ⟨pex, ?_, by assumption⟩
        constructor <;> try assumption
        · sorry
        · refine CFGStep_dst_mem_nodes hstep
      case LoopTrue K' b c m =>
        cases hContInv
        case loopK bts' ben bex cen pex _ _ _ _ _ _ heeei _ _ hstep =>
        exists pex
        refine ⟨?_, hstep⟩
        · constructor <;> try assumption
          · sorry
          · refine CFGStep_dst_mem_nodes (by assumption)
          · sorry
          · constructor <;> try assumption
            · sorry
            · refine CFGStep_dst_mem_nodes (by assumption)
            · sorry
          · sorry
      case LoopFalse K' b c m =>
        cases hContInv
        case loopK bts' ben bex cen pex _ _ _ _ _ _ heeei _ _ _ =>
        refine ⟨pex, ?_, by assumption⟩
        constructor <;> try assumption
        -- almost reasonable goals
        · sorry
        exact CFGStep_dst_mem_nodes (by assumption)
      case LoopCont K' J' b c m =>
        cases hContInv
        case loopContK bts' cen cex ben bex pex _ _ _ _ _ _ _ _ _ _ _ _ =>
        refine ⟨cen, ?_, by assumption⟩
        constructor <;> try assumption
        constructor <;> try assumption
        · -- almost reasonable
          exact CFGStep_dst_mem_nodes (by assumption)
        · -- similarly almost reasonable
          sorry
        · -- idfk
          sorry
        · -- idfk either
          sorry
      case ScopeExit K' b m =>
        cases hContInv
        case scopeExitK pex hcont hstep =>
        refine ⟨pex, ?_, by assumption⟩
        constructor <;> try assumption
        · sorry
        · -- almost reasonable
          exact CFGStep_dst_mem_nodes (by assumption)
      case ExprStmtDone K' =>
        cases hContInv
        case exprStmtK sx hcont hstep =>
        refine ⟨sx, ?_, by assumption⟩
        constructor <;> try assumption
        · sorry
        exact CFGStep_dst_mem_nodes (by assumption)

    | stmtEntry s' E J K bts n ex hkind hekind hmem hmemex hseei hcont hjinv =>
      sorry
    | stmtExit s' E J K bts n hkind hmem hcont hjinv =>
      -- At a statement exit node. The successor edge comes from ContCFGInv.
      cases heval
      case SeqDone K' s₂ =>
        cases hcont
        case seqK bts s₂en s₂ex pex hstep hnnode hxnode hnkind hxkind hedgeinv hcontinv hfinstep =>
        refine ⟨s₂en, ?_, hfinstep⟩
        constructor <;> try assumption
        -- ⊢ ContCFGInv (stmtCFG s) K' s₂ex
        -- reasonably sure this can't be proven
        · sorry
        · sorry
      case ScopeBody K' body m =>
        cases hcont
        case scopeBodyK bts' een eex _ _ _ _ _ _ _ _ hfinstep =>
        refine ⟨een, ?_, hfinstep⟩
        constructor <;> try assumption
        constructor <;> try assumption
        sorry

  edge_complete := by
    intros n m h
    obtain ⟨e, he, hen, hem⟩ := h
    simp only [exists_and_left]
    sorry





end TranslationTests

end AltCFGProofs
end LeanFormalisation
