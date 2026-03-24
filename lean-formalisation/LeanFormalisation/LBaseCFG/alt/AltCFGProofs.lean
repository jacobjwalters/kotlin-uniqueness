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

import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis

open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal

namespace LeanFormalisation
namespace AltCFGProofs

section Translation

abbrev StateRel := CEK -> CFGNode -> Prop

def CFGStep (g : CFG) (n m : CFGNode) : Prop :=
  ∃ e ∈ g.edges, e.src = n ∧ e.dst = m

abbrev CFGReach (g : CFG) := Relation.ReflTransGen (CFGStep g)
abbrev CEKReach := Relation.ReflTransGen Eval

/-!
## concrete relation candidate
-/

/--
Coarse control-kind compatibility between a CEK state and a CFG node.
-/
def KindRel (σ : CEK) (n : CFGNode) : Prop :=
  match σ.1, n.kind with
  | .sourceStmt s, .stmtEntry s' => s = s'
  | .sourceExpr e, .exprEntry e' => e = e'
  | .skip, .stmtExit _ => True
  | .value _, .exprExit _ => True
  | _, _ => False

/--
Branch-sensitive edge guard used in the concrete CEK/CFG simulation step.
-/
def EdgeEnabled (σ : CEK) (e : CFGEdge) : Prop :=
  match e.kind, σ.1 with
  | .normal, _ => True
  | .back, .value _ => True
  | .breakOut, .sourceExpr (.Break _) => True
  | .trueBranch, .value .True => True
  | .falseBranch, .value .False => True
  | _, _ => False

/--
Single synchronized step on CEK state and CFG node.
-/
def CEKCFGStep (s : Lang .Stmt) (p q : CEK × CFGNode) : Prop :=
  ∃ e ∈ (stmtCFG s).edges,
    e.src = p.2 ∧ e.dst = q.2 ∧ Eval p.1 q.1 ∧ EdgeEnabled p.1 e

/--
Concrete relation: local kind agreement plus existence of a synchronized path
from program entry to the current CEK/node pair.
-/
def stateRelConcrete (s : Lang .Stmt) : StateRel :=
  fun σ n =>
    KindRel σ n ∧
      Relation.ReflTransGen (CEKCFGStep s)
        (initState s, (stmtCFG s).entry)
        (σ, n)

/-!
## basic requirements for the semantics/cfg correspondence
-/
class TranslationReq (s : Lang .Stmt) : Prop where
  init_related : stateRelConcrete s (initState s) (stmtCFG s).entry
  terminal_related : ∀ E, stateRelConcrete s (terminalState E) (stmtCFG s).exit

  step_sound :
    ∀ {σ σ' n}, stateRelConcrete s σ n -> Eval σ σ' ->
      ∃ n', stateRelConcrete s σ' n' ∧ CFGStep (stmtCFG s) n n'

  edge_complete :
    ∀ {n m}, CFGStep (stmtCFG s) n m ->
      ∀ {σ}, stateRelConcrete s σ n ->
        ∃ σ', Eval σ σ' ∧ stateRelConcrete s σ' m

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
private theorem buildExpr_exit_kind
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTarget nextId fuel expr).exit.kind = .exprExit expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

/--
Computes the kind of the entry node returned by `buildExpr`: it is always
`exprEntry expr`. Use: identifies the destination of `.back` edges in while.
-/
private theorem buildExpr_entry_kind
    (breakTarget : Option CFGNode) (nextId fuel : Nat) (expr : Lang .Expr) :
    (buildExpr breakTarget nextId fuel expr).entry.kind = .exprEntry expr := by
  cases fuel <;> cases expr <;> simp [buildExpr]

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

/-!
## cfg translation correctness: two directions
-/

/-
  translation wrappers: these do not add proof content, they expose class fields
  under theorem names used by downstream developments.
-/

/--
Restates `TranslationReq.step_sound` as a theorem with explicit arguments. Use:
convenient entry point for proof scripts that avoid direct class-field access.
-/
theorem translation_sound_step
  (s : Lang .Stmt) [TranslationReq s]
    {σ σ' : CEK} {n : CFGNode}
  (hrel : stateRelConcrete s σ n) (hstep : Eval σ σ') :
  ∃ n', stateRelConcrete s σ' n' ∧ CFGStep (stmtCFG s) n n' := by
  exact TranslationReq.step_sound hrel hstep

/--
Restates `TranslationReq.edge_complete` as a theorem with explicit arguments.
Use: convenient entry point for completeness proofs over CFG edges.
-/
theorem translation_complete_edge
    (s : Lang .Stmt) [TranslationReq s]
    {n m : CFGNode}
    (hedge : CFGStep (stmtCFG s) n m)
    {σ : CEK} (hrel : stateRelConcrete s σ n) :
    ∃ σ', Eval σ σ' ∧ stateRelConcrete s σ' m := by
  exact TranslationReq.edge_complete hedge hrel

/--
one side correspondence between reachability and relation
-/
theorem translation_sound_reachability
      (s : Lang .Stmt) [TranslationReq s]
      {σ σ' : CEK} {n : CFGNode}
      (hrel : stateRelConcrete s σ n)
      (hreach : CEKReach σ σ') :
    ∃ n', stateRelConcrete s σ' n' ∧ CFGReach (stmtCFG s) n n' := by
  induction hreach with
  | refl => exists n
  | tail hsb hbc ih =>
    obtain ⟨mid, hbmid, hreachMid⟩ := ih
    obtain ⟨mid', hcmid', hstepMid⟩ :=
      translation_sound_step s hbmid hbc
    exact ⟨mid', hcmid', Relation.ReflTransGen.tail hreachMid hstepMid⟩

theorem translation_complete_reachability
      (s : Lang .Stmt) [TranslationReq s]
      {σ : CEK} {n m : CFGNode}
      (hrel : stateRelConcrete s σ n)
      (hpath : CFGReach (stmtCFG s) n m) :
    ∃ σ', CEKReach σ σ' ∧ stateRelConcrete s σ' m := by
  induction hpath with
  | refl =>
    exists σ
  | tail hsb hbc ih =>
    obtain ⟨mid, hbmid, hreacMid⟩ := ih
    obtain ⟨σ', hstep, hrel'⟩ :=
      translation_complete_edge s hbc hreacMid
    exact ⟨σ', Relation.ReflTransGen.tail hbmid hstep, hrel'⟩

end Translation

end AltCFGProofs
end LeanFormalisation
