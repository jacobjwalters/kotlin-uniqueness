import LeanFormalisation.LBase

namespace LeanFormalisation
namespace AltCFG

inductive CFGNodeKind where
| exprEntry (e : Lang .Expr)
| exprExit (e : Lang .Expr)
| stmtEntry (s : Lang .Stmt)
| stmtExit (s : Lang .Stmt)
deriving Repr, DecidableEq

structure CFGNode where
  id : Nat
  kind : CFGNodeKind
deriving Repr, DecidableEq

inductive EdgeKind where
| normal
| trueBranch
| falseBranch
| back
| breakOut
deriving Repr, DecidableEq

structure CFGEdge where
  src : CFGNode
  dst : CFGNode
  kind : EdgeKind
deriving Repr, DecidableEq

structure CFG where
  entry : CFGNode
  exit : CFGNode
  edges : List CFGEdge
deriving Repr

namespace Internal

def mkEdge (src dst : CFGNode) (kind : EdgeKind := .normal) : CFGEdge :=
  ⟨src, dst, kind⟩

structure BuildResult where
  entry : CFGNode
  exit : CFGNode
  edges : List CFGEdge
  nextId : Nat

mutual
  def exprSize : Lang .Expr → Nat
  | .Var _
  | .True
  | .False
  | .Nat _
  | .Unit
  | .Break _ => 1
  | .BinOp e₁ e₂ _ => 1 + exprSize e₁ + exprSize e₂
  | .UnOp e _ => 1 + exprSize e
  | .If c e₁ e₂ => 1 + exprSize c + exprSize e₁ + exprSize e₂
  | .While c body => 1 + exprSize c + exprSize body
  | .Scope s e => 1 + stmtSize s + exprSize e

  def stmtSize : Lang .Stmt → Nat
  | .Decl _ e => 1 + exprSize e
  | .Assign _ e => 1 + exprSize e
  | .Seq s₁ s₂ => 1 + stmtSize s₁ + stmtSize s₂
  | .Do e => 1 + exprSize e
end

mutual
  def buildExpr (breakTargets : List CFGNode) (nextId : Nat)
      (e : Lang .Expr) : BuildResult :=
    let entry : CFGNode := { id := nextId, kind := .exprEntry e }
    let exit : CFGNode := { id := nextId + 1, kind := .exprExit e }
    let nextId := nextId + 2
    match e with
    | .Var _
    | .True
    | .False
    | .Nat _
    | .Unit =>
        { entry := entry
        , exit := exit
        , edges := [mkEdge entry exit]
        , nextId := nextId
        }
    | .BinOp e₁ e₂ _ =>
        let r₁ := buildExpr breakTargets nextId e₁
        let r₂ := buildExpr breakTargets r₁.nextId e₂
        { entry := entry
        , exit := exit
        , edges :=
              [ mkEdge entry r₁.entry
              , mkEdge r₁.exit r₂.entry
              , mkEdge r₂.exit exit
              ] ++ r₁.edges ++ r₂.edges
        , nextId := r₂.nextId
        }
    | .UnOp arg _ =>
        let r := buildExpr breakTargets nextId arg
        { entry := entry
        , exit := exit
        , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
        , nextId := r.nextId
        }
    | .If cond e₁ e₂ =>
        let c := buildExpr breakTargets nextId cond
        let t := buildExpr breakTargets c.nextId e₁
        let f := buildExpr breakTargets t.nextId e₂
        { entry := entry
        , exit := exit
        , edges :=
            [ mkEdge entry c.entry
            , mkEdge c.exit t.entry .trueBranch
            , mkEdge c.exit f.entry .falseBranch
            , mkEdge t.exit exit
            , mkEdge f.exit exit
            ] ++ c.edges ++ t.edges ++ f.edges
        , nextId := f.nextId
        }
    | .While cond body =>
        let c := buildExpr (exit :: breakTargets) nextId cond
        let b := buildExpr (exit :: breakTargets) c.nextId body
        { entry := entry
        , exit := exit
        , edges :=
            [ mkEdge entry c.entry
            , mkEdge c.exit b.entry .trueBranch
            , mkEdge c.exit exit .falseBranch
            , mkEdge b.exit c.entry .back
            ] ++ c.edges ++ b.edges
        , nextId := b.nextId
        }
    | .Break l =>
        let edges :=
          if h : l < breakTargets.length
          then [mkEdge entry (breakTargets[l]) .breakOut]
          else []
        { entry := entry
        , exit := exit
        , edges := edges
        , nextId := nextId
        }
    | .Scope s res =>
        let sRes := buildStmt breakTargets nextId s
        let rRes := buildExpr breakTargets sRes.nextId res
        { entry := entry
        , exit := exit
        , edges :=
              [ mkEdge entry sRes.entry
              , mkEdge sRes.exit rRes.entry
              , mkEdge rRes.exit exit
              ] ++ sRes.edges ++ rRes.edges
        , nextId := rRes.nextId
        }

  def buildStmt (breakTargets : List CFGNode) (nextId : Nat)
      (s : Lang .Stmt) : BuildResult :=
    let entry : CFGNode := { id := nextId, kind := .stmtEntry s }
    let exit : CFGNode := { id := nextId + 1, kind := .stmtExit s }
    let nextId := nextId + 2
    match s with
    | .Decl _ init =>
        let r := buildExpr breakTargets nextId init
        { entry := entry
        , exit := exit
        , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
        , nextId := r.nextId
        }
    | .Assign _ rhs =>
        let r := buildExpr breakTargets nextId rhs
        { entry := entry
        , exit := exit
        , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
        , nextId := r.nextId
        }
    | .Seq s₁ s₂ =>
        let r₁ := buildStmt breakTargets nextId s₁
        let r₂ := buildStmt breakTargets r₁.nextId s₂
        { entry := entry
        , exit := exit
        , edges :=
              [ mkEdge entry r₁.entry
              , mkEdge r₁.exit r₂.entry
              , mkEdge r₂.exit exit
              ] ++ r₁.edges ++ r₂.edges
        , nextId := r₂.nextId
        }
    | .Do e =>
        let r := buildExpr breakTargets nextId e
        { entry := entry
        , exit := exit
        , edges := [mkEdge entry r.entry, mkEdge r.exit exit] ++ r.edges
        , nextId := r.nextId
        }
end

end Internal

def exprEdges (breakTargets : List CFGNode) (e : Lang .Expr) : List CFGEdge :=
  (Internal.buildExpr breakTargets 0 e).edges

def stmtEdges (breakTargets : List CFGNode) (s : Lang .Stmt) : List CFGEdge :=
  (Internal.buildStmt breakTargets 0 s).edges

def exprCFG (e : Lang .Expr) : CFG :=
  let r := Internal.buildExpr [] 0 e
  CFG.mk r.entry r.exit r.edges

def stmtCFG (s : Lang .Stmt) : CFG :=
  let r := Internal.buildStmt [] 0 s
  CFG.mk r.entry r.exit r.edges

def CFG.outEdges (g : CFG) (n : CFGNode) : List CFGEdge :=
  g.edges.filter (fun e => decide (e.src = n))

def CFG.inEdges (g : CFG) (n : CFGNode) : List CFGEdge :=
  g.edges.filter (fun e => decide (e.dst = n))

def CFG.succ (g : CFG) (n : CFGNode) : List CFGNode :=
  (g.outEdges n).map (fun e => e.dst) |>.eraseDups

def CFG.pred (g : CFG) (n : CFGNode) : List CFGNode :=
  (g.inEdges n).map (fun e => e.src) |>.eraseDups

def CFG.nodes (g : CFG) : List CFGNode :=
  (g.edges.foldr (fun ed acc => ed.src :: ed.dst :: acc) [g.entry, g.exit]).eraseDups

private theorem mem_acc_mem_eraseDupsBy_loop {α : Type} (r : α → α → Bool)
    (as acc : List α) (a : α)
    (h : a ∈ acc) : a ∈ List.eraseDupsBy.loop r as acc := by
  induction as generalizing acc with
  | nil =>
    unfold List.eraseDupsBy.loop
    exact List.mem_reverse.mpr h
  | cons x xs ih =>
    unfold List.eraseDupsBy.loop
    split
    · exact ih acc h
    · exact ih (x :: acc) (List.mem_cons_of_mem x h)

private theorem mem_of_mem_eraseDupsBy_loop {α : Type} [BEq α] [LawfulBEq α]
    (as acc : List α) (a : α)
    (h : a ∈ as) : a ∈ List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) as acc := by
  induction as generalizing acc with
  | nil => contradiction
  | cons x xs ih =>
    unfold List.eraseDupsBy.loop
    cases List.mem_cons.mp h with
    | inl heq =>
      subst heq
      split
      next htrue =>
        obtain ⟨b, hb_mem, hb_eq⟩ := List.any_eq_true.mp htrue
        exact mem_acc_mem_eraseDupsBy_loop _ xs _ a (eq_of_beq hb_eq ▸ hb_mem)
      next _ =>
        exact mem_acc_mem_eraseDupsBy_loop _ xs (a :: acc) a (List.Mem.head _)
    | inr hmem =>
      split
      · exact ih acc hmem
      · exact ih (x :: acc) hmem

theorem mem_of_mem_eraseDups {α : Type} [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  mem_of_mem_eraseDupsBy_loop l [] a h

private theorem eraseDupsBy_loop_subset {α : Type} (r : α → α → Bool)
    (as acc : List α) (a : α)
    (h : a ∈ List.eraseDupsBy.loop r as acc) : a ∈ as ∨ a ∈ acc := by
  induction as generalizing acc with
  | nil =>
    unfold List.eraseDupsBy.loop at h
    exact Or.inr (List.mem_reverse.mp h)
  | cons x xs ih =>
    unfold List.eraseDupsBy.loop at h
    split at h
    · cases ih acc h with
      | inl h => exact Or.inl (List.mem_cons_of_mem x h)
      | inr h => exact Or.inr h
    · cases ih (x :: acc) h with
      | inl h => exact Or.inl (List.mem_cons_of_mem x h)
      | inr h =>
        cases List.mem_cons.mp h with
        | inl heq => exact Or.inl (heq ▸ List.Mem.head _)
        | inr h => exact Or.inr h

theorem mem_eraseDups_of {α : Type} [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l := by
  cases eraseDupsBy_loop_subset _ l [] a h with
  | inl h => exact h
  | inr h => contradiction

private lemma mem_foldr_edges_dst (edges : List CFGEdge) (init : List CFGNode) (e : CFGEdge)
    (he : e ∈ edges) :
    e.dst ∈ edges.foldr (fun ed acc => ed.src :: ed.dst :: acc) init := by
  induction edges with
  | nil => contradiction
  | cons h t ih =>
    simp only [List.foldr_cons]
    cases List.mem_cons.mp he with
    | inl heq => subst heq; exact List.mem_cons_of_mem _ (List.Mem.head _)
    | inr hmem => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hmem))

lemma CFG.succ_subset_nodes (g : CFG) (n : CFGNode) :
    ∀ x ∈ g.succ n, x ∈ g.nodes := by
  intro x hx
  simp only [CFG.succ, CFG.outEdges] at hx
  have hx' := mem_eraseDups_of hx
  obtain ⟨e, he_mem, he_dst⟩ := List.mem_map.mp hx'
  subst he_dst
  simp only [CFG.nodes]
  exact mem_of_mem_eraseDups (mem_foldr_edges_dst g.edges _ e (List.mem_of_mem_filter he_mem))

-- Example:
-- let _ : Nat = 5;
-- do while (true) (scope { _₀ := 0 } unit)
def exampleProgram : Lang .Stmt :=
  .Seq (.Decl .nat (.Nat 5))
       (.Do (.While .True (.Scope (.Assign 0 (.Nat 0)) .Unit)))

def exampleCFG : CFG := stmtCFG exampleProgram

end AltCFG
end LeanFormalisation
