import LeanFormalisation.LBaseCFG.alt.AltCFG

namespace Utils

private lemma sum_map_update_le {A : Type} [DecidableEq A]
      (l : List A) (f : A → Nat) (n : A) (nv : Nat) (hle : f n ≤ nv) :
    (l.map f).sum ≤ (l.map (fun x => if x = n then nv else f x)).sum := by
  induction l with
  | nil => grind
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h' : h = n
    case pos => simpa [h'] using Nat.add_le_add hle ih
    case neg =>
      simpa [h'] using ih

lemma sum_map_update_lt {A : Type} [DecidableEq A]
      (l : List A) (f : A -> Nat) (n : A) (nv : Nat)
      (hin : n ∈ l) (hlt : f n < nv) :
    (l.map f).sum < (l.map (fun x => if x = n then nv else f x)).sum := by
  induction l with
  | nil => cases hin
  | cons h t ih =>
    by_cases hc : h = n
    case pos =>
      simp only [hc, List.map_cons, List.sum_cons, ↓reduceIte]
      refine Nat.add_lt_add_of_lt_of_le hlt ?_
      exact sum_map_update_le t f n nv (by grind)
    case neg =>
      grind
end Utils

open LeanFormalisation.AltCFG

abbrev fact (A : Type) := CFGNode -> A

def fact.update {A : Type} (f : fact A) (n : CFGNode) (v : A) : fact A :=
  fun m => if m = n then v else f m

def joinPredEdges [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge → A → A)
    (outF : fact A) (n : CFGNode) : A :=
  (g.inEdges n).foldl (fun acc e => acc ⊔ edgeTransfer e (outF e.src)) ⊥

class FiniteHeight (A : Type) [Max A] where
  height : A -> Nat
  maxHeight : Nat
  maxHeight_ub : ∀ a, height a ≤ maxHeight
  height_mono : ∀ a b, a ⊔ b ≠ a -> height a < height (a ⊔ b)

def factHeight {A : Type} [Max A] [fh : FiniteHeight A] (g : CFG) (f : fact A) : Nat :=
  let tot := fh.maxHeight * g.nodes.length
  let curr := (g.nodes.map (fun n => fh.height (f n))).sum
  tot - curr

open FiniteHeight in
lemma sum_height_le_max {A : Type} [Max A] [FiniteHeight A] (l : List CFGNode) (f : fact A) :
    (l.map (fun x => height (f x))).sum ≤ maxHeight A * l.length := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ maxHeight A + (List.map (fun x ↦ height (f x)) t).sum := by
        simp [maxHeight_ub]
      _ ≤ maxHeight A + maxHeight A * t.length := by
        simp [ih]
      _ ≤ maxHeight A * (t.length + 1) := by
        grind

-- NOTE: LBase.lean defines a notation `Γ₁ "("x")" "=" type` that matches
-- any `expr (expr) = expr` pattern at the top level, breaking lemma statements
-- that use `... (fun x => ...) = ...`. We use `Eq` explicitly to work around this.

private lemma map_height_update_eq {A : Type} [Max A] [FiniteHeight A]
    (nodes : List CFGNode) (outF : fact A) (node : CFGNode) (newOut : A) :
    Eq (nodes.map (fun x => FiniteHeight.height (fact.update outF node newOut x)))
       (nodes.map (fun x => if x = node then FiniteHeight.height newOut
        else FiniteHeight.height (outF x))) := by
  congr 1; ext x; simp [fact.update]; split <;> rfl

private lemma map_update_sum_lt {A : Type} [Max A] [FiniteHeight A]
    (nodes : List CFGNode) (outF : fact A) (node : CFGNode) (newOut : A)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    (nodes.map (fun x => FiniteHeight.height (outF x))).sum
    < (nodes.map (fun x => FiniteHeight.height (fact.update outF node newOut x))).sum := by
  rw [map_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.height (outF x)) node (FiniteHeight.height newOut) hn hlt

private theorem factHeight_decreases
    {A : Type} [Max A] [FiniteHeight A]
    (g : CFG) (outF : fact A) (node : CFGNode) (newOut : A)
    (hn : node ∈ g.nodes)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    factHeight g (outF.update node newOut) < factHeight g outF := by
  have h_le := sum_height_le_max g.nodes (outF.update node newOut)
  have h_lt := map_update_sum_lt g.nodes outF node newOut hn hlt
  unfold factHeight; simp only []
  omega

-- node/edgeTransfer to maintain branch sensitivity -> feed choice information
-- to the branch's environments.
def worklistForwardEdge
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : fact A) (wl : List CFGNode)
    (hwl : ∀ x ∈ wl, x ∈ g.nodes)
    : fact A :=
  match wl with
  | [] => outF
  | n :: rest =>
      let newIn :=
        if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n
      let newOut := outF n ⊔ nodeTransfer n newIn
      if newOut = outF n then
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit outF rest
          (fun x hx => hwl x (List.mem_cons_of_mem n hx))
      else
        let outF' := outF.update n newOut
        let wl' := rest ++ g.succ n
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit outF' wl'
          (fun x hx => by
            cases List.mem_append.mp hx with
            | inl h => exact hwl x (List.mem_cons_of_mem n h)
            | inr h => exact g.succ_subset_nodes n x h)
termination_by (factHeight g outF, wl.length)
decreasing_by
  · refine Prod.Lex.right (factHeight g outF) ?_
    grind
  · refine Prod.Lex.left (rest ++ g.succ n).length (n :: rest).length ?_
    exact factHeight_decreases g outF n (outF n ⊔ nodeTransfer n newIn)
      (hwl n (List.Mem.head _))
      (FiniteHeight.height_mono _ _ (by assumption))

def expectedIn {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : fact A) (n : CFGNode) : A :=
  if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n

def runDataflow
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : fact A) (wl0 : List CFGNode)
    (hwl0 : ∀ x ∈ wl0, x ∈ g.nodes) : fact A × fact A :=
  let finalOut := worklistForwardEdge g nodeTransfer edgeTransfer entryInit out0 wl0 hwl0
  let finalIn := fun n => expectedIn g edgeTransfer entryInit finalOut n
  ⟨finalIn, finalOut⟩

abbrev Domain (n : Nat) (A : Type) [Bot A] := Fin n → A

instance {n : Nat} {A : Type} [Bot A] : Bot (Domain n A) where
  bot := fun _ => ⊥

def domainJoin {n : Nat} {A : Type} [Bot A] [Max A] (ρ₁ ρ₂ : Domain n A) : Domain n A :=
  fun i => ρ₁ i ⊔ ρ₂ i

instance {n : Nat} {A : Type} [Bot A] [Max A] : Max (Domain n A) where
  max := domainJoin

private def domainBEq {n : Nat} {A : Type} [Bot A] [DecidableEq A] (ρ₁ ρ₂ : Domain n A) : Bool :=
  (List.finRange n).all (fun i => ρ₁ i = ρ₂ i)

private theorem domainBEq_iff {n : Nat} {A : Type} [Bot A] [DecidableEq A]
    (ρ₁ ρ₂ : Domain n A) : domainBEq ρ₁ ρ₂ = true ↔ ρ₁ = ρ₂ := by
  constructor
  · intro h
    funext i
    simp only [domainBEq, List.all_eq_true, List.mem_finRange,
      decide_eq_true_eq, forall_const] at h
    exact h i
  · intro h
    subst h
    simp [domainBEq, List.all_eq_true]

instance {n : Nat} {A : Type} [Bot A] [DecidableEq A] : DecidableEq (Domain n A) :=
  fun ρ₁ ρ₂ =>
    if h : domainBEq ρ₁ ρ₂ then
      isTrue ((domainBEq_iff ρ₁ ρ₂).mp h)
    else
      isFalse (fun heq => h ((domainBEq_iff ρ₁ ρ₂).mpr heq))

def getVar {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (x : VarName) : A :=
  if h : x < n then ρ ⟨x, h⟩ else ⊥

def setVar {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (x : VarName) (v : A) : Domain n A :=
  fun i => if i.val = x then v else ρ i

def pushBinding {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (v : A) : Domain n A :=
  fun i =>
    if i.val = 0 then v
    else if h : i.val - 1 < n then ρ ⟨i.val - 1, h⟩
    else ⊥

def popBindings {n : Nat} {A : Type} [Bot A] (k : Nat) (ρ : Domain n A) : Domain n A :=
  fun i =>
    if h : i.val + k < n then ρ ⟨i.val + k, h⟩
    else ⊥

instance {n : Nat} {A : Type} [Bot A] [Repr A] : Repr (Domain n A) where
  reprPrec := fun d _ =>
    let entries := (List.finRange n).map (fun i => s!"x{i.val}:{repr (d i)}")
    s!"[{String.intercalate ", " entries}]"

def domainHeight {n : Nat} {A : Type} [Bot A] [Max A] [FiniteHeight A] (ρ : Domain n A) : Nat :=
  ((List.finRange n).map (fun i => FiniteHeight.height (ρ i))).sum

private lemma height_le_of_join {A : Type} [Max A] [FiniteHeight A] (a b : A) :
    FiniteHeight.height a ≤ FiniteHeight.height (a ⊔ b) := by
  by_cases h : a ⊔ b = a
  · rw [h]
  · exact Nat.le_of_lt (FiniteHeight.height_mono a b h)

instance {A n} [Bot A] [Max A] [fh : FiniteHeight A] : FiniteHeight (Domain n A) where
  height := domainHeight
  maxHeight := n * FiniteHeight.maxHeight A
  maxHeight_ub ρ := by
    unfold domainHeight
    induction n with
    | zero => simp
    | succ n ih =>
      have := FiniteHeight.maxHeight_ub (ρ 0)
      simp only [List.finRange_succ, List.map_cons, List.map_map, List.sum_cons,
        Nat.add_one_mul, add_comm, ge_iff_le]
      exact Nat.add_le_add this (ih fun i ↦ ρ i.succ)
  height_mono ρ₁ ρ₂ h := by
    unfold domainHeight
    have ⟨i, hi₁, hi₂⟩ : ∃ i, i ∈ List.finRange n ∧ ρ₁ i ⊔ ρ₂ i ≠ ρ₁ i := by
      by_contra hall; push_neg at hall; apply h
      funext i; apply hall
      grind
    suffices hsuf : ∀ (l : List (Fin n)), i ∈ l →
        (l.map (fun j => FiniteHeight.height (ρ₁ j))).sum <
        (l.map (fun j => FiniteHeight.height ((ρ₁ ⊔ ρ₂) j))).sum from
      hsuf _ hi₁
    intro l hmem
    induction l with
    | nil => cases hmem
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      have hsum_le : ∀ (l : List (Fin n)),
         (l.map (fun j => FiniteHeight.height (ρ₁ j))).sum ≤
         (l.map (fun j => FiniteHeight.height ((ρ₁ ⊔ ρ₂) j))).sum := by
       intro l; induction l with
       | nil => simp
       | cons hd tl ih =>
         simp only [List.map_cons, List.sum_cons]
         refine Nat.add_le_add ?_ ih
         exact height_le_of_join _ _
      cases List.mem_cons.mp hmem
      case inl heq =>
        subst heq
        apply Nat.add_lt_add_of_lt_of_le
        · exact FiniteHeight.height_mono _ _ hi₂
        · exact hsum_le _
      case inr htl =>
        refine Nat.add_lt_add_of_le_of_lt ?_ (ih htl)
        exact height_le_of_join _ _

section LangSpecific

def stmtDeclDelta : Lang .Stmt -> Nat
| .Decl _ _ => 1
| .Assign _ _ => 0
| .Seq s₁ s₂ => stmtDeclDelta s₁ + stmtDeclDelta s₂
| .Do _ => 0

abbrev LangEval (n : Nat) (A : Type) [Bot A] := Domain n A -> Lang .Expr -> A

def transferScopedNode {n : Nat} {A : Type} [Max A] [Bot A]
    (eval : LangEval n A) (node : CFGNode) (ρ : Domain n A) : Domain n A :=
  match node.kind with
  | .stmtExit (.Assign x rhs) => setVar ρ x (eval ρ rhs)
  | .stmtExit (.Decl _ init) => pushBinding ρ (eval ρ init)
  | .exprExit (.Scope s _) => popBindings (stmtDeclDelta s) ρ
  | _ => ρ

def transferBranchEdge {n : Nat} {A : Type} [Max A] [Bot A]
    (refine : Lang .Expr -> Bool -> Domain n A -> Domain n A)
    (e : CFGEdge) (ρ : Domain n A) : Domain n A :=
  match e.kind, e.src.kind with
  | .trueBranch, .exprExit cond => refine cond true ρ
  | .falseBranch, .exprExit cond => refine cond false ρ
  | _, _ => ρ

end LangSpecific
