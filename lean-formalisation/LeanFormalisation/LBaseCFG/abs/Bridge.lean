/-
  Bridge Lemma: connecting AbsStep to CFGStep.

  Phase 4 of the design document (JACOTODO.md §4).

  The key result is `absStep_implies_cfgStep`: every abstract step between
  two AbsControl positions corresponds to a concrete CFG edge in the graph
  built by `buildExpr`/`buildStmt`.
-/

import LeanFormalisation.LBaseCFG.abs.AbsCFG
import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Correspondence

open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal
open LeanFormalisation.AltCFGProofs

/-! ## Mapping AbsControl to CFGNodeKind -/

/-- Canonical isomorphism between `AbsControl` and `CFGNodeKind`. -/
def toNodeKind : AbsControl → CFGNodeKind
| .exprEntry e => .exprEntry e
| .exprExit e  => .exprExit e
| .stmtEntry s => .stmtEntry s
| .stmtExit s  => .stmtExit s

/-- Inverse mapping. -/
def fromNodeKind : CFGNodeKind → AbsControl
| .exprEntry e => .exprEntry e
| .exprExit e  => .exprExit e
| .stmtEntry s => .stmtEntry s
| .stmtExit s  => .stmtExit s

theorem fromNodeKind_toNodeKind (ac : AbsControl) :
    (fromNodeKind (toNodeKind ac)) = ac := by
  cases ac <;> rfl

theorem toNodeKind_fromNodeKind (nk : CFGNodeKind) :
    (toNodeKind (fromNodeKind nk)) = nk := by
  cases nk <;> rfl

/-! ## The composed state relation -/

/-- The composed relation: a CEK state is related to a CFG node when there
    exists an abstract control that mediates between them. -/
def AbsStateRel (σ : CEK) (n : CFGNode) : Prop :=
  ∃ ac, SimRel σ ac ∧ n.kind = toNodeKind ac

/-! ## Bridge: AbsStep → CFGStep (forward direction)

The forward bridge says: if `AbsStep ac₁ ac₂` holds, then for any program
whose CFG contains nodes with kinds matching `ac₁` and `ac₂`, there is a
CFG edge between them.

More precisely, for a subexpression/substatement that is built by
`buildExpr`/`buildStmt`, the resulting `BuildResult` contains the
corresponding edge.

We state per-constructor lemmas first, then combine them.
-/

-- For literals/variables: entry → exit edge
theorem buildExpr_litVar_edge (bt : List CFGNode) (nid : Nat) (e : Lang .Expr)
    (h : isLitOrVar e) :
    let r := buildExpr bt nid e
    mkEdge r.entry r.exit ∈ r.edges := by
  cases e <;> simp [isLitOrVar] at h <;> simp [buildExpr, mkEdge]

-- For BinOp: entry → left operand entry
theorem buildExpr_binop_entry_edge (bt : List CFGNode) (nid : Nat)
    (e₁ e₂ : Lang .Expr) (op : BinOp) :
    let r := buildExpr bt nid (.BinOp e₁ e₂ op)
    let r₁ := buildExpr bt (nid + 2) e₁
    mkEdge r.entry r₁.entry ∈ r.edges := by
  simp [buildExpr]

-- For BinOp: left exit → right entry
theorem buildExpr_binop_mid_edge (bt : List CFGNode) (nid : Nat)
    (e₁ e₂ : Lang .Expr) (op : BinOp) :
    let r := buildExpr bt nid (.BinOp e₁ e₂ op)
    let r₁ := buildExpr bt (nid + 2) e₁
    let r₂ := buildExpr bt r₁.nextId e₂
    mkEdge r₁.exit r₂.entry ∈ r.edges := by
  simp [buildExpr]

-- For BinOp: right exit → binop exit
theorem buildExpr_binop_exit_edge (bt : List CFGNode) (nid : Nat)
    (e₁ e₂ : Lang .Expr) (op : BinOp) :
    let r := buildExpr bt nid (.BinOp e₁ e₂ op)
    let r₁ := buildExpr bt (nid + 2) e₁
    let r₂ := buildExpr bt r₁.nextId e₂
    mkEdge r₂.exit r.exit ∈ r.edges := by
  simp [buildExpr]

-- For UnOp: entry → operand entry
theorem buildExpr_unop_entry_edge (bt : List CFGNode) (nid : Nat)
    (e : Lang .Expr) (op : UnOp) :
    let r := buildExpr bt nid (.UnOp e op)
    let ri := buildExpr bt (nid + 2) e
    mkEdge r.entry ri.entry ∈ r.edges := by
  simp [buildExpr]

-- For UnOp: operand exit → unop exit
theorem buildExpr_unop_exit_edge (bt : List CFGNode) (nid : Nat)
    (e : Lang .Expr) (op : UnOp) :
    let r := buildExpr bt nid (.UnOp e op)
    let ri := buildExpr bt (nid + 2) e
    mkEdge ri.exit r.exit ∈ r.edges := by
  simp [buildExpr]

-- For If: entry → cond entry
theorem buildExpr_if_entry_edge (bt : List CFGNode) (nid : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr bt nid (.If cond e₁ e₂)
    let rc := buildExpr bt (nid + 2) cond
    mkEdge r.entry rc.entry ∈ r.edges := by
  simp [buildExpr]

-- For If: cond exit → true branch entry (trueBranch edge)
theorem buildExpr_if_true_edge (bt : List CFGNode) (nid : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr bt nid (.If cond e₁ e₂)
    let rc := buildExpr bt (nid + 2) cond
    let rt := buildExpr bt rc.nextId e₁
    mkEdge rc.exit rt.entry .trueBranch ∈ r.edges := by
  simp [buildExpr]

-- For If: cond exit → false branch entry (falseBranch edge)
theorem buildExpr_if_false_edge (bt : List CFGNode) (nid : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr bt nid (.If cond e₁ e₂)
    let rc := buildExpr bt (nid + 2) cond
    let rt := buildExpr bt rc.nextId e₁
    let rf := buildExpr bt rt.nextId e₂
    mkEdge rc.exit rf.entry .falseBranch ∈ r.edges := by
  simp [buildExpr]

-- For If: true branch exit → if exit (join)
theorem buildExpr_if_true_join_edge (bt : List CFGNode) (nid : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr bt nid (.If cond e₁ e₂)
    let rc := buildExpr bt (nid + 2) cond
    let rt := buildExpr bt rc.nextId e₁
    mkEdge rt.exit r.exit ∈ r.edges := by
  simp [buildExpr]

-- For If: false branch exit → if exit (join)
theorem buildExpr_if_false_join_edge (bt : List CFGNode) (nid : Nat)
    (cond e₁ e₂ : Lang .Expr) :
    let r := buildExpr bt nid (.If cond e₁ e₂)
    let rc := buildExpr bt (nid + 2) cond
    let rt := buildExpr bt rc.nextId e₁
    let rf := buildExpr bt rt.nextId e₂
    mkEdge rf.exit r.exit ∈ r.edges := by
  simp [buildExpr]

-- For While: entry → cond entry
theorem buildExpr_while_entry_edge (bt : List CFGNode) (nid : Nat)
    (cond body : Lang .Expr) :
    let r := buildExpr bt nid (.While cond body)
    let rc := buildExpr bt (nid + 2) cond
    mkEdge r.entry rc.entry ∈ r.edges := by
  simp [buildExpr]

-- For While: cond exit → body entry (trueBranch)
theorem buildExpr_while_body_edge (bt : List CFGNode) (nid : Nat)
    (cond body : Lang .Expr) :
    let r := buildExpr bt nid (.While cond body)
    let rc := buildExpr bt (nid + 2) cond
    let rb := buildExpr (r.exit :: bt) rc.nextId body
    mkEdge rc.exit rb.entry .trueBranch ∈ r.edges := by
  simp [buildExpr]

-- For While: cond exit → while exit (falseBranch)
theorem buildExpr_while_false_edge (bt : List CFGNode) (nid : Nat)
    (cond body : Lang .Expr) :
    let r := buildExpr bt nid (.While cond body)
    let rc := buildExpr bt (nid + 2) cond
    mkEdge rc.exit r.exit .falseBranch ∈ r.edges := by
  simp [buildExpr]

-- For While: body exit → cond entry (back edge)
theorem buildExpr_while_back_edge (bt : List CFGNode) (nid : Nat)
    (cond body : Lang .Expr) :
    let r := buildExpr bt nid (.While cond body)
    let rc := buildExpr bt (nid + 2) cond
    let rb := buildExpr (r.exit :: bt) rc.nextId body
    mkEdge rb.exit rc.entry .back ∈ r.edges := by
  simp [buildExpr]

-- For Break: entry → break target (breakOut edge)
theorem buildExpr_break_edge (bt : List CFGNode) (nid : Nat)
    (l : Nat) (h : l < bt.length) :
    let r := buildExpr bt nid (.Break l)
    mkEdge r.entry (bt[l]) .breakOut ∈ r.edges := by
  simp [buildExpr, h]
-- For Scope: entry → stmt body entry
theorem buildExpr_scope_entry_edge (bt : List CFGNode) (nid : Nat)
    (s : Lang .Stmt) (e : Lang .Expr) :
    let r := buildExpr bt nid (.Scope s e)
    let rs := buildStmt bt (nid + 2) s
    mkEdge r.entry rs.entry ∈ r.edges := by
  simp [buildExpr]

-- For Scope: stmt exit → result expr entry
theorem buildExpr_scope_mid_edge (bt : List CFGNode) (nid : Nat)
    (s : Lang .Stmt) (e : Lang .Expr) :
    let r := buildExpr bt nid (.Scope s e)
    let rs := buildStmt bt (nid + 2) s
    let re := buildExpr bt rs.nextId e
    mkEdge rs.exit re.entry ∈ r.edges := by
  simp [buildExpr]

-- For Scope: result exit → scope exit
theorem buildExpr_scope_exit_edge (bt : List CFGNode) (nid : Nat)
    (s : Lang .Stmt) (e : Lang .Expr) :
    let r := buildExpr bt nid (.Scope s e)
    let rs := buildStmt bt (nid + 2) s
    let re := buildExpr bt rs.nextId e
    mkEdge re.exit r.exit ∈ r.edges := by
  simp [buildExpr]

-- For Decl: entry → init expr entry
theorem buildStmt_decl_entry_edge (bt : List CFGNode) (nid : Nat)
    (ty : Ty) (e : Lang .Expr) :
    let r := buildStmt bt nid (.Decl ty e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge r.entry ri.entry ∈ r.edges := by
  simp [buildStmt]

-- For Decl: init exit → decl exit
theorem buildStmt_decl_exit_edge (bt : List CFGNode) (nid : Nat)
    (ty : Ty) (e : Lang .Expr) :
    let r := buildStmt bt nid (.Decl ty e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge ri.exit r.exit ∈ r.edges := by
  simp [buildStmt]

-- For Assign: entry → rhs entry
theorem buildStmt_assign_entry_edge (bt : List CFGNode) (nid : Nat)
    (x : VarName) (e : Lang .Expr) :
    let r := buildStmt bt nid (.Assign x e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge r.entry ri.entry ∈ r.edges := by
  simp [buildStmt]

-- For Assign: rhs exit → assign exit
theorem buildStmt_assign_exit_edge (bt : List CFGNode) (nid : Nat)
    (x : VarName) (e : Lang .Expr) :
    let r := buildStmt bt nid (.Assign x e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge ri.exit r.exit ∈ r.edges := by
  simp [buildStmt]

-- For Seq: entry → first stmt entry
theorem buildStmt_seq_entry_edge (bt : List CFGNode) (nid : Nat)
    (s₁ s₂ : Lang .Stmt) :
    let r := buildStmt bt nid (.Seq s₁ s₂)
    let r₁ := buildStmt bt (nid + 2) s₁
    mkEdge r.entry r₁.entry ∈ r.edges := by
  simp [buildStmt]

-- For Seq: first exit → second entry
theorem buildStmt_seq_mid_edge (bt : List CFGNode) (nid : Nat)
    (s₁ s₂ : Lang .Stmt) :
    let r := buildStmt bt nid (.Seq s₁ s₂)
    let r₁ := buildStmt bt (nid + 2) s₁
    let r₂ := buildStmt bt r₁.nextId s₂
    mkEdge r₁.exit r₂.entry ∈ r.edges := by
  simp [buildStmt]

-- For Seq: second exit → seq exit
theorem buildStmt_seq_exit_edge (bt : List CFGNode) (nid : Nat)
    (s₁ s₂ : Lang .Stmt) :
    let r := buildStmt bt nid (.Seq s₁ s₂)
    let r₁ := buildStmt bt (nid + 2) s₁
    let r₂ := buildStmt bt r₁.nextId s₂
    mkEdge r₂.exit r.exit ∈ r.edges := by
  simp [buildStmt]

-- For Do: entry → expr entry
theorem buildStmt_do_entry_edge (bt : List CFGNode) (nid : Nat)
    (e : Lang .Expr) :
    let r := buildStmt bt nid (.Do e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge r.entry ri.entry ∈ r.edges := by
  simp [buildStmt]

-- For Do: expr exit → do exit
theorem buildStmt_do_exit_edge (bt : List CFGNode) (nid : Nat)
    (e : Lang .Expr) :
    let r := buildStmt bt nid (.Do e)
    let ri := buildExpr bt (nid + 2) e
    mkEdge ri.exit r.exit ∈ r.edges := by
  simp [buildStmt]


/-- An edge in a `BuildResult` -/
def BuildEdge (r : BuildResult) (n m : CFGNode) : Prop :=
  ∃ e ∈ r.edges, e.src = n ∧ e.dst = m

/-- Edges in a `BuildResult` lift to edges in the `CFG` built from it. -/
theorem buildEdge_of_cfgStep_stmtCFG (s : Lang .Stmt) (n m : CFGNode) :
    BuildEdge (buildStmt [] 0 s) n m → CFGStep (stmtCFG s) n m := by
  intro ⟨e, he, hsrc, hdst⟩
  exact ⟨e, he, hsrc, hdst⟩

/-- The composed step-soundness theorem:
    If the CEK machine steps and the state is related to a CFG node
    (via the abstract control), then there exists a successor CFG node
    that is related to the new state and connected by a CFG edge.

    This is the new version of `TranslationReq.step_sound`, factored
    through the abstract step relation. -/
theorem step_sound_via_abs
    (s : Lang .Stmt)
    {σ σ' : CEK} {ac₁ : AbsControl} {n : CFGNode}
    (hsim : SimRel σ ac₁)
    (hkind : n.kind = toNodeKind ac₁)
    (heval : Eval σ σ')
    (hcont : AbsContInv σ.K ac₁.target)
    (hbridge : ∀ ac₁ ac₂, AbsStep ac₁ ac₂ →
      ∀ n₁, n₁.kind = toNodeKind ac₁ →
        ∃ n₂, n₂.kind = toNodeKind ac₂ ∧ CFGStep (stmtCFG s) n₁ n₂) :
    ∃ ac₂ n' t₂, SimRel σ' ac₂ ∧ n'.kind = toNodeKind ac₂ ∧
      AbsContInv σ'.K t₂ ∧ CFGStep (stmtCFG s) n n' := by
  obtain ⟨ac₂, t₂, hstep, hsim₂, hcont₂⟩ := abs_sim heval hsim hcont
  obtain ⟨n₂, hkind₂, hedge⟩ := hbridge ac₁ ac₂ hstep n hkind
  exact ⟨ac₂, n₂, t₂, hsim₂, hkind₂, hcont₂, hedge⟩

/-- Reachability soundness: if the CEK machine reaches σ' from σ,
    and σ is related to CFG node n, then there exists a CFG node n'
    related to σ' that is CFG-reachable from n.

    This is the new version of `translation_sound_reachability`. -/
theorem reachability_sound_via_abs
    (s : Lang .Stmt)
    {σ σ' : CEK} {n : CFGNode}
    (hrel : AbsStateRel σ n)
    (hreach : CEKReach σ σ')
    -- Invariant: AbsContInv is maintained along the path
    -- Bridge: every AbsStep has a CFG edge
    (hbridge : ∀ ac₁ ac₂, AbsStep ac₁ ac₂ →
      ∀ n₁, n₁.kind = toNodeKind ac₁ →
        ∃ n₂, n₂.kind = toNodeKind ac₂ ∧ CFGStep (stmtCFG s) n₁ n₂) :
    ∃ n', AbsStateRel σ' n' ∧ CFGReach (stmtCFG s) n n' := by
  sorry -- requires threading AbsContInv through the induction; deferred

/-! ## The bridge theorem (forward direction)

The main bridge theorem: for a program `s`, every `AbsStep` between
abstract controls that appear as subexpressions of `s` corresponds to
a CFG edge in `stmtCFG s`.

This requires mutual induction over `buildExpr`/`buildStmt` to show
that every edge produced by the builder corresponds to an `AbsStep`,
and conversely every `AbsStep` for a subexpression has a matching edge.

The per-constructor edge lemmas above are the building blocks.
The full proof requires showing that subexpression edges are included
in the parent's edge list (monotonicity/containment), which is already
established in `CorrespondenceProofs.lean` as `edges_sub_*` lemmas.
-/

/-- Forward bridge: every abstract step corresponds to a CFG edge.
    Stated for a top-level statement program. -/
theorem absStep_implies_cfgEdge (s : Lang .Stmt)
    (ac₁ ac₂ : AbsControl) (hstep : AbsStep ac₁ ac₂)
    (n₁ : CFGNode) (hkind₁ : n₁.kind = toNodeKind ac₁) :
    ∃ n₂, n₂.kind = toNodeKind ac₂ ∧ CFGStep (stmtCFG s) n₁ n₂ := by
  sorry -- requires mutual induction; the per-constructor lemmas above
        -- provide the base cases, monotonicity provides containment
