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

import LeanFormalisation.LBaseCFG.alt.AltCFGDefs

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
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTarget nextId fuel expr).exit.kind = .exprExit expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

/--
Computes the kind of the entry node returned by `buildExpr`: it is always
`exprEntry expr`. Use: identifies the destination of `.back` edges in while.
-/
theorem buildExpr_entry_kind
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTarget nextId fuel expr).entry.kind = .exprEntry expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

theorem buildStmt_entry_kind
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    (buildStmt breakTarget nextId fuel stmt).entry.kind = .stmtEntry stmt := by
  cases fuel <;> cases stmt <;> simp [buildStmt]

theorem buildStmt_exit_kind
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    (buildStmt breakTarget nextId fuel stmt).exit.kind = .stmtExit stmt := by
  cases fuel <;> cases stmt <;> simp [buildStmt]

/--
Mutual fuel-induction core: any `.trueBranch`/`.falseBranch` edge produced by
either builder has source kind `exprExit _`. Use: single shared engine for the
two public branch-shape theorems immediately below.
-/
private theorem branch_src_exprExit_mutual :
    ∀ fuel,
      (∀ (breakTarget : Option CFGNode) (nextId : Nat) (stmt : Lang .Stmt)
          (ed : CFGEdge),
          ed ∈ (buildStmt breakTarget nextId fuel stmt).edges →
          ed.kind = .trueBranch ∨ ed.kind = .falseBranch →
          ∃ cond, ed.src.kind = .exprExit cond) ∧
      (∀ (breakTarget : Option CFGNode) (nextId : Nat) (expr : Lang .Expr)
          (ed : CFGEdge),
          ed ∈ (buildExpr breakTarget nextId fuel expr).edges →
          ed.kind = .trueBranch ∨ ed.kind = .falseBranch →
          ∃ cond, ed.src.kind = .exprExit cond) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTarget nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTarget nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTarget nextId stmt ed hed hkind
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
    · intro breakTarget nextId expr ed hed hkind
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
            (buildExpr_exit_kind breakTarget (nextId + 2) n cond)
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind breakTarget (nextId + 2) n cond)
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
            (buildExpr_exit_kind (some { id := nextId + 1, kind := .exprExit (.While cond body) })
              (nextId + 2) n cond)
        · subst ed
          refine ⟨cond, ?_⟩
          simpa [mkEdge] using
            (buildExpr_exit_kind (some { id := nextId + 1, kind := .exprExit (.While cond body) })
              (nextId + 2) n cond)
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₅ with h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case Break =>
        cases breakTarget with
        | none =>
          simp at hed
        | some t =>
          simp [mkEdge] at hed
          subst ed
          simp at hkind
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
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    ∀ ed ∈ (buildStmt breakTarget nextId fuel stmt).edges,
    ed.kind = .trueBranch ∨ ed.kind = .falseBranch →
    ∃ cond, ed.src.kind = .exprExit cond := by
  intro ed hed hkind
  exact (branch_src_exprExit_mutual fuel).1 breakTarget nextId stmt ed hed hkind

/--
Expression-builder specialization of `branch_src_exprExit_mutual`. Use: reusable
branch-edge invariant for later expression-local arguments.
-/
theorem buildExpr_branch_src_exprExit
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    ∀ ed ∈ (buildExpr breakTarget nextId fuel expr).edges,
    ed.kind = .trueBranch ∨ ed.kind = .falseBranch →
    ∃ cond, ed.src.kind = .exprExit cond := by
  intro ed hed hkind
  exact (branch_src_exprExit_mutual fuel).2 breakTarget nextId expr ed hed hkind

/--
Mutual fuel-induction core for back edges: every `.back` edge produced by either
builder goes from `exprExit body` to `exprEntry cond`. Use: shared engine for
`buildStmt_back_edge_shape` and `buildExpr_back_edge_shape`.
-/
private theorem back_edge_shape_mutual :
    ∀ fuel,
      (∀ (breakTarget : Option CFGNode) (nextId : Nat) (stmt : Lang .Stmt)
          (ed : CFGEdge),
          ed ∈ (buildStmt breakTarget nextId fuel stmt).edges →
          ed.kind = .back →
          ∃ c body,
            ed.src.kind = .exprExit body ∧
            ed.dst.kind = .exprEntry c) ∧
      (∀ (breakTarget : Option CFGNode) (nextId : Nat) (expr : Lang .Expr)
          (ed : CFGEdge),
          ed ∈ (buildExpr breakTarget nextId fuel expr).edges →
          ed.kind = .back →
          ∃ c body,
            ed.src.kind = .exprExit body ∧
            ed.dst.kind = .exprEntry c) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTarget nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTarget nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTarget nextId stmt ed hed hkind
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
    · intro breakTarget nextId expr ed hed hkind
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
                (some { id := nextId + 1, kind := .exprExit (.While cond body) })
                ((buildExpr (some { id := nextId + 1, kind := .exprExit (.While cond body) })
                  (nextId + 2) n cond).nextId)
                n body)
          · simpa [mkEdge] using
              (buildExpr_entry_kind
                (some { id := nextId + 1, kind := .exprExit (.While cond body) })
                (nextId + 2) n cond)
        · rcases h₅ with h | h
          · exact ihExpr _ _ _ _ h hkind
          · exact ihExpr _ _ _ _ h hkind
      case Break =>
        cases breakTarget with
        | none =>
          simp at hed
        | some t =>
          simp [mkEdge] at hed
          subst ed
          simp at hkind
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
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt) :
    ∀ ed ∈ (buildStmt breakTarget nextId fuel stmt).edges,
      ed.kind = .back →
      ∃ c body,
        ed.src.kind = .exprExit body ∧
        ed.dst.kind = .exprEntry c := by
  intro ed hed hkind
  exact (back_edge_shape_mutual fuel).1 breakTarget nextId stmt ed hed hkind

/--
Expression-builder specialization of back-edge shape. Use: reusable local fact
for expression-only analyses involving while-loop back edges.
-/
theorem buildExpr_back_edge_shape
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    ∀ ed ∈ (buildExpr breakTarget nextId fuel expr).edges,
      ed.kind = .back →
      ∃ c body,
        ed.src.kind = .exprExit body ∧
        ed.dst.kind = .exprEntry c := by
  intro ed hed hkind
  exact (back_edge_shape_mutual fuel).2 breakTarget nextId expr ed hed hkind

/--
Lifts builder-level back-edge shape to full statement CFGs. Use: canonical
stmtCFG-level formulation consumed by `stmtCFG_back_edges_are_loop_back`.
-/
theorem stmtCFG_back_edge_shape (s : Lang .Stmt) :
    ∀ e ∈ (stmtCFG s).edges,
      e.kind = .back →
      ∃ c body,
        e.src.kind = .exprExit body ∧
        e.dst.kind = .exprEntry c := by
  unfold stmtCFG
  intro e he hkind
  exact buildStmt_back_edge_shape none 0 (stmtSize s) s e he hkind

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
Specifies when a `breakTarget` is valid for proofs: either absent, or an
`exprExit` node of some loop expression. Use: invariant threaded through the
mutual break-edge proof.
-/
private def BreakTargetWellFormed : Option CFGNode → Prop
  | none => True
  | some t => ∃ loopExpr, t.kind = .exprExit loopExpr

/--
Mutual fuel-induction core for break edges under a well-formed break target:
every `.breakOut` edge points to an `exprExit _`. Use: shared engine for
`buildStmt_break_edge_target_exprExit`.
-/
private theorem break_edge_target_exprExit_mutual :
    ∀ fuel,
      (∀ (breakTarget : Option CFGNode),
          BreakTargetWellFormed breakTarget →
          ∀ (nextId : Nat) (stmt : Lang .Stmt) (ed : CFGEdge),
          ed ∈ (buildStmt breakTarget nextId fuel stmt).edges →
          ed.kind = .breakOut →
          ∃ loopExpr, ed.dst.kind = .exprExit loopExpr) ∧
      (∀ (breakTarget : Option CFGNode),
          BreakTargetWellFormed breakTarget →
          ∀ (nextId : Nat) (expr : Lang .Expr) (ed : CFGEdge),
          ed ∈ (buildExpr breakTarget nextId fuel expr).edges →
          ed.kind = .breakOut →
          ∃ loopExpr, ed.dst.kind = .exprExit loopExpr) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro breakTarget hbt nextId stmt ed hed
      simp [buildStmt] at hed
    · intro breakTarget hbt nextId expr ed hed
      simp [buildExpr] at hed
  | succ n ih =>
    rcases ih with ⟨ihStmt, ihExpr⟩
    constructor
    · intro breakTarget hbt nextId stmt ed hed hkind
      cases stmt
        <;> simp only [buildStmt, List.cons_append,
          List.nil_append, List.mem_cons, List.mem_append] at hed
      case Decl τ init =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTarget hbt _ _ _ h hkind
      case Assign x rhs =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTarget hbt _ _ _ h hkind
      case Seq s₁ s₂ =>
        rcases hed with h | h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h with h | h
          · exact ihStmt breakTarget hbt _ _ _ h hkind
          · exact ihStmt breakTarget hbt _ _ _ h hkind
      case Do e =>
        rcases hed with h | h | h
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTarget hbt _ _ _ h hkind
    · intro breakTarget hbt nextId expr ed hed hkind
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
          · exact ihExpr breakTarget hbt _ _ _ h₂ hkind
          · exact ihExpr breakTarget hbt _ _ _ h₃ hkind
      case UnOp a op =>
        rcases hed with h₁ | (h₂ | h₃)
        · cases h₁
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · exact ihExpr breakTarget hbt _ _ _ h₃ hkind
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
          · exact ihExpr breakTarget hbt _ _ _ h hkind
          · exact ihExpr breakTarget hbt _ _ _ h hkind
          · exact ihExpr breakTarget hbt _ _ _ h hkind
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
              (some { id := nextId + 1, kind := .exprExit (.While cond body) })
              (by exact ⟨.While cond body, rfl⟩)
              _ _ _ h hkind
          · exact ihExpr
              (some { id := nextId + 1, kind := .exprExit (.While cond body) })
              (by exact ⟨.While cond body, rfl⟩)
              _ _ _ h hkind
      case Break =>
        cases breakTarget with
        | none =>
          simp at hed
        | some t =>
          simp [mkEdge] at hed
          subst ed
          simpa [BreakTargetWellFormed] using hbt
      case Scope s res =>
        rcases hed with h₁ | h₂ | h₃ | h₄
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · subst ed
          simp [mkEdge] at hkind
        · rcases h₄ with h | h
          · exact ihStmt breakTarget hbt _ _ _ h hkind
          · exact ihExpr breakTarget hbt _ _ _ h hkind

/--
Statement-builder specialization of break-edge target shape, parameterized by a
well-formed break target. Use: final step to derive the stmtCFG theorem below.
-/
theorem buildStmt_break_edge_target_exprExit
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (stmt : Lang .Stmt)
    (hbt : BreakTargetWellFormed breakTarget) :
    ∀ ed ∈ (buildStmt breakTarget nextId fuel stmt).edges,
      ed.kind = .breakOut →
      ∃ loopExpr, ed.dst.kind = .exprExit loopExpr := by
  intro ed hed hkind
  exact (break_edge_target_exprExit_mutual fuel).1 breakTarget hbt nextId stmt ed hed hkind

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
  exact buildStmt_break_edge_target_exprExit none 0 (stmtSize s) s
    (by simp [BreakTargetWellFormed]) e he hkind

end Translation

section TranslationTests

set_option relaxedAutoImplicit true

/-!
## Continuation-CFG invariant

`ContCFGInv g K x` asserts that when the current sub-computation finishes at
CFG node `x`, the continuation stack `K` describes exactly the CFG edges
leading back to `g.exit`.  Each constructor corresponds to a `Cont` frame and
records the CFG nodes and edges that the frame implies.
-/
inductive ContCFGInv (g : CFG) : List Cont → CFGNode → Prop where
  /-- Empty stack: the current exit IS the top-level exit. -/
  | halt : x = g.exit → ContCFGInv g [] x
  /-- Left operand of BinOp done → edge to right operand entry,
      then right exit → parent exit. -/
  | binopLK (op : BinOp) (e₂ : Lang .Expr)
      (e₂en e₂ex pex : CFGNode) :
      e₂en.kind = .exprEntry e₂ →
      e₂ex.kind = .exprExit e₂ →
      CFGStep g x e₂en → CFGStep g e₂ex pex →
      ContCFGInv g K pex →
      ContCFGInv g (.binopLK op e₂ :: K) x
  /-- Right operand of BinOp done → edge to parent exit. -/
  | binopRK (op : BinOp) (v₁ : Value) (pex : CFGNode) :
      CFGStep g x pex → ContCFGInv g K pex →
      ContCFGInv g (.binopRK op v₁ :: K) x
  /-- Operand of UnOp done → edge to parent exit. -/
  | unopK (op : UnOp) (pex : CFGNode) :
      CFGStep g x pex → ContCFGInv g K pex →
      ContCFGInv g (.unopK op :: K) x
  /-- Condition of If done → trueBranch/falseBranch edges to branch
      entries, both branch exits → parent exit. -/
  | ifCondK (e₁ e₂ : Lang .Expr)
      (e₁en e₁ex e₂en e₂ex pex : CFGNode) :
      e₁en.kind = .exprEntry e₁ →
      e₁ex.kind = .exprExit e₁ →
      e₂en.kind = .exprEntry e₂ →
      e₂ex.kind = .exprExit e₂ →
      CFGStep g x e₁en → CFGStep g x e₂en →
      CFGStep g e₁ex pex → CFGStep g e₂ex pex →
      ContCFGInv g K pex →
      ContCFGInv g (.ifCondK e₁ e₂ :: K) x
  /-- Init expr of Decl done → edge to stmt exit. -/
  | declK (ty : Ty) (sex : CFGNode) :
      CFGStep g x sex → ContCFGInv g K sex →
      ContCFGInv g (.declK ty :: K) x
  /-- RHS of Assign done → edge to stmt exit. -/
  | assignK (v : VarName) (sex : CFGNode) :
      CFGStep g x sex → ContCFGInv g K sex →
      ContCFGInv g (.assignK v :: K) x
  /-- First statement of Seq done → edge to s₂ entry,
      then s₂ exit → parent exit. -/
  | seqK (s₂ : Lang .Stmt) (s₂en s₂ex pex : CFGNode) :
      s₂en.kind = .stmtEntry s₂ →
      s₂ex.kind = .stmtExit s₂ →
      CFGStep g x s₂en → CFGStep g s₂ex pex →
      ContCFGInv g K pex →
      ContCFGInv g (.seqK s₂ :: K) x
  /-- Expr of Do stmt done → edge to stmt exit. -/
  | exprStmtK (sex : CFGNode) :
      CFGStep g x sex → ContCFGInv g K sex →
      ContCFGInv g (.exprStmtK :: K) x
  /-- Condition of While done (x = condExit).
      trueBranch → bodyEntry, falseBranch → whileExit,
      bodyExit → condEntry (back edge). -/
  | loopK (c body : Lang .Expr) (n : Nat)
      (ben bex cen pex : CFGNode) :
      ben.kind = .exprEntry body →
      bex.kind = .exprExit body →
      cen.kind = .exprEntry c →
      CFGStep g x ben → CFGStep g x pex →
      CFGStep g bex cen →
      ContCFGInv g K pex →
      ContCFGInv g (.loopK c body n :: K) x
  /-- Body of While done (x = bodyExit).
      back edge → condEntry, then full loop structure from condExit. -/
  | loopContK (c body : Lang .Expr) (n : Nat)
      (cen cex ben bex pex : CFGNode) :
      cen.kind = .exprEntry c →
      cex.kind = .exprExit c →
      ben.kind = .exprEntry body →
      bex.kind = .exprExit body →
      CFGStep g x cen →
      CFGStep g cex ben → CFGStep g cex pex →
      CFGStep g bex cen →
      ContCFGInv g K pex →
      ContCFGInv g (.loopContK c body n :: K) x
  /-- Statement part of Scope done → edge to result expr entry,
      then result exit → parent exit. -/
  | scopeBodyK (e : Lang .Expr) (n : Nat)
      (een eex pex : CFGNode) :
      een.kind = .exprEntry e →
      eex.kind = .exprExit e →
      CFGStep g x een → CFGStep g eex pex →
      ContCFGInv g K pex →
      ContCFGInv g (.scopeBodyK e n :: K) x
  /-- Result expr of Scope done → edge to parent exit. -/
  | scopeExitK (n : Nat) (pex : CFGNode) :
      CFGStep g x pex → ContCFGInv g K pex →
      ContCFGInv g (.scopeExitK n :: K) x

/-!
## CEK-to-CFG correspondence relation (strengthened)

`cfgcekRel s` relates a CEK state `σ` to a CFG node `n` when:
  1. `n` belongs to the CFG built for `s`,
  2. the CEK control component matches the node kind, and
  3. the continuation stack satisfies `ContCFGInv` at the corresponding
     exit node — ensuring the stack shape mirrors the CFG nesting structure.

For entry nodes, the constructor stores the corresponding exit node `ex`
so that `ContCFGInv` can be anchored there.  For exit nodes, the invariant
is directly on the current node.
-/
inductive cfgcekRel (s : Lang .Stmt) : StateRel where
  | exprEntry (e : Lang .Expr) (E : Environment) (K : List Cont)
      (n ex : CFGNode) :
      n.kind = .exprEntry e →
      ex.kind = .exprExit e →
      n ∈ (stmtCFG s).nodes →
      ContCFGInv (stmtCFG s) K ex →
      cfgcekRel s (.sourceExpr e, E, K) n
  | exprExit (e : Lang .Expr) (v : Value) (E : Environment)
      (K : List Cont) (n : CFGNode) :
      n.kind = .exprExit e →
      n ∈ (stmtCFG s).nodes →
      ContCFGInv (stmtCFG s) K n →
      cfgcekRel s (.value v, E, K) n
  | stmtEntry (st : Lang .Stmt) (E : Environment) (K : List Cont)
      (n ex : CFGNode) :
      n.kind = .stmtEntry st →
      ex.kind = .stmtExit st →
      n ∈ (stmtCFG s).nodes →
      ContCFGInv (stmtCFG s) K ex →
      cfgcekRel s (.sourceStmt st, E, K) n
  | stmtExit (st : Lang .Stmt) (E : Environment)
      (K : List Cont) (n : CFGNode) :
      n.kind = .stmtExit st →
      n ∈ (stmtCFG s).nodes →
      ContCFGInv (stmtCFG s) K n →
      cfgcekRel s (.skip, E, K) n

/-!
### Proof strategy for `step_sound` and `edge_complete`

Both proofs proceed by case-splitting on the `Eval` rule (for `step_sound`)
or the CFG edge (for `edge_complete`) and the `cfgcekRel` constructor.

**`step_sound`:** Given `cfgcekRel s σ n` and `Eval σ σ'`, produce `n'` with
`cfgcekRel s σ' n'` and `CFGStep g n n'`.  The `ContCFGInv` invariant provides
the exact CFG edge for continuation-driven transitions (e.g., `BinOpL` uses
the `binopLK` constructor's stored edge `x → e₂en`), while the node kind
determines the edge for control-driven transitions (e.g., `BinOp` entry has
edge to `r₁.entry`).  Requires structural lemmas about `buildExpr`/`buildStmt`
producing specific edges from entry nodes.

**`edge_complete`:** Given `CFGStep g n m` and `cfgcekRel s σ n`, produce
`σ'` with `Eval σ σ'` and `cfgcekRel s σ' m`.  The node kind plus `ContCFGInv`
determines the CEK control and top continuation frame.  The `CEKReach`
precondition provides well-typedness for operator totality (BinOpR/UnOpDone).
-/

noncomputable def cfgcekRelReq (s : Lang .Stmt) :
    TranslationReq s (cfgcekRel s) where
  init_related := by
    exact cfgcekRel.stmtEntry s [] []
      (stmtCFG s).entry (stmtCFG s).exit
      (buildStmt_entry_kind none 0 (stmtSize s) s)
      (buildStmt_exit_kind none 0 (stmtSize s) s)
      (cfg_entry_in_nodes _)
      (ContCFGInv.halt rfl)
  terminal_related := by
    intro E
    exact cfgcekRel.stmtExit s E []
      (stmtCFG s).exit
      (buildStmt_exit_kind none 0 (stmtSize s) s)
      (cfg_exit_in_nodes _)
      (ContCFGInv.halt rfl)
  step_sound := sorry
  edge_complete := sorry

end TranslationTests

end AltCFGProofs
end LeanFormalisation
