import LeanFormalisation.LBase.LBaseCFG.AltCFG
import Mathlib.Order.Notation
import Mathlib.Logic.Basic

open LeanFormalisation.AltCFG

-- note: multiple times in this document, the explicit `Eq x y` constructor is used
-- in place of the more usual `x = y` notation. This is due to notation conflicts
-- introduced by `LBase.lean`.

namespace Utils
private lemma sum_map_update_le {A : Type} [DecidableEq A]
      (l : List A) (f : A -> Nat) (n : A) (nv : Nat) (hle : f n ≤ nv) :
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

section Dataflow
/-- a fact is what is known about the abstract state at a given node.
    `A` represents the "abstract domain", dependent on the analysis
    being carried out. -/
abbrev fact (A : Type) := CFGNode -> A

/-- update the fact what is known about the current node `n` with a new
    abstract state `v`. -/
def fact.update {A : Type} (f : fact A) (n : CFGNode) (v : A) : fact A :=
  fun m => if m = n then v else f m


/-- characterization of monotonicity for a function wrt `Max` -/
def monotoneD {A : Type} [Max A] (f : A -> A) : Prop :=
  ∀ x y : A, x ⊔ y = x -> (f x) ⊔ (f y) = (f x)

/-- definition of `f ≤ g` for `fact` -/
def factLe {A : Type} [Max A] (f g : fact A) : Prop :=
  ∀ n, (f n) ⊔ (g n) = (f n)

/-- characterization of a finite lattice for types equipped with a `Max`
    operation. we require:
    - a height value for every possible abstract state;
    - a maximal height;
    - a proof that this height is, indeed, maximal
    - a proof of the monotonicity of height. -/
class FiniteHeight (A : Type) [Max A] where
  height : A -> Nat
  maxHeight : Nat
  maxHeight_ub : ∀ a, height a ≤ maxHeight
  height_mono : ∀ a b, a ⊔ b ≠ a -> height a < height (a ⊔ b)

/-- computes the height of the current fact height.
    used for proof of worklist termination. -/
def factHeight {A : Type} [Max A] [fh : FiniteHeight A] (g : CFG) (f : fact A) : Nat :=
  let tot := fh.maxHeight * g.nodes.length
  let curr := (g.nodes.map (fun n => fh.height (f n))).sum
  tot - curr

/-- for any list of nodes `l`, `∑_(n ∈ l) (h (f n)) ≤ maxHeight * |l|` -/
lemma sum_height_le_max {A : Type} [Max A] [fh : FiniteHeight A] (l : List CFGNode) (f : fact A) :
    (l.map (fun x => fh.height (f x))).sum ≤ fh.maxHeight * l.length := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ fh.maxHeight + (List.map (fun x ↦ fh.height (f x)) t).sum := by
        simp [fh.maxHeight_ub]
      _ ≤ fh.maxHeight + fh.maxHeight * t.length := by
        simp [ih]
      _ ≤ fh.maxHeight * (t.length + 1) := by
        grind

/-- update/height commutativity -/
private lemma map_height_update_eq {A : Type} [Max A] [FiniteHeight A]
    (nodes : List CFGNode) (outF : fact A) (node : CFGNode) (newOut : A) :
    Eq (nodes.map (fun x => FiniteHeight.height (fact.update outF node newOut x)))
       (nodes.map (fun x => if x = node then FiniteHeight.height newOut
        else FiniteHeight.height (outF x))) := by
  congr 1; ext x; simp [fact.update]; split <;> rfl

/-- update/height monotonicity -/
private lemma map_update_sum_lt {A : Type} [Max A] [FiniteHeight A]
    (nodes : List CFGNode) (outF : fact A) (node : CFGNode) (newOut : A)
    (hn : node ∈ nodes)
    (hlt : FiniteHeight.height (outF node) < FiniteHeight.height newOut) :
    (nodes.map (fun x => FiniteHeight.height (outF x))).sum
    < (nodes.map (fun x => FiniteHeight.height (fact.update outF node newOut x))).sum := by
  rw [map_height_update_eq]
  exact Utils.sum_map_update_lt nodes
    (fun x => FiniteHeight.height (outF x)) node (FiniteHeight.height newOut) hn hlt

/-- if you replace a node's fact with one of smaller height, the resulting
    `factHeight` is smaller -/
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

/-- computes the join of the results of applying an edge transfer function to all
    incoming edges of a given node in `g`. -/
def joinPredEdges [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (outF : fact A) (n : CFGNode) : A :=
  (g.inEdges n).foldl (fun acc e => acc ⊔ edgeTransfer e (outF e.src)) ⊥

/-- main forward worklist algorithm. -/
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

/-- computes the input fact for a given node `n`. if `n` is the entry of the
    current graph, returns the initial entry fact; otherwise, computes the
    join of all incoming fact. -/
def expectedIn {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : fact A) (n : CFGNode) : A :=
  if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n

/-- computes the full dataflow analysis, returning entry and exit metadata for
    every node -/
def runDataflow
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : fact A) (wl0 : List CFGNode)
    (hwl0 : ∀ x ∈ wl0, x ∈ g.nodes) : fact A × fact A :=
  let finalOut : fact A := worklistForwardEdge g nodeTransfer edgeTransfer entryInit out0 wl0 hwl0
  let finalIn : fact A := fun n => expectedIn g edgeTransfer entryInit finalOut n
  ⟨finalIn, finalOut⟩
end Dataflow

section Domain
/-
  we define a canonical instantiation for extending a variable-level
  abstract state `A` to a state comprised of multiple variables.
  the idea is: the user can define any abstract state `A` and abstraction
  function towards it, ensuring that this state has lattice structure.
  they then instantiate the user-facing dataflow analysis framework with it.
  under the hood, that framework lifts the user supplied pointwise abstraction
  to the multi-variable `Domain`, lifting the lattice structure and the finite
  height requirements to be able to run dataflow on it.
-/

/-- for every variable in `[0, n - 1]`, return the abstract state.
    we say that `Domain n A` is an _abstract domain of size `n` over `A`_.
-/
abbrev Domain (n : Nat) (A : Type) [Bot A] := Fin n -> A

/-- `Repr` instance for Domain. -/
instance {n : Nat} {A : Type} [Bot A] [Repr A] : Repr (Domain n A) where
  reprPrec := fun d _ =>
    let entries := (List.finRange n).map (fun i => s!"x{i.val}:{repr (d i)}")
    s!"[{String.intercalate ", " entries}]"

/-- in the lattice of `Domain n A`, the bot element is the constant function
    (λ _ => ⊥ₐ) -/
instance {n : Nat} {A : Type} [Bot A] : Bot (Domain n A) where
  bot := fun _ => ⊥

/-- the join of ρ₁, ρ₂ in `Domain n A` is the pointwise join of their elements. -/
instance {n : Nat} {A : Type} [Bot A] [Max A] : Max (Domain n A) where
  max := fun ρ₁ ρ₂ => fun i => ρ₁ i ⊔ ρ₂ i

/-- boolean equality on two domains of size n over a type `A` with decidable equality. -/
private def domainBEq {n : Nat} {A : Type} [Bot A] [DecidableEq A] (ρ₁ ρ₂ : Domain n A) : Bool :=
  (List.finRange n).all (fun i => ρ₁ i = ρ₂ i)

/-- two domains are boolean equal if and only if they're equal. -/
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

/-- decidable equality instance for `Domain` -/
instance {n : Nat} {A : Type} [Bot A] [DecidableEq A] : DecidableEq (Domain n A) :=
  fun ρ₁ ρ₂ =>
    if h : domainBEq ρ₁ ρ₂ then
      isTrue ((domainBEq_iff ρ₁ ρ₂).mp h)
    else
      isFalse (fun heq => h ((domainBEq_iff ρ₁ ρ₂).mpr heq))

/-- get abstract state of `x` in `ρ`, or `⊥` if `x` is outside of range. -/
def getVar {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (x : VarName) : A :=
  if h : x < n then ρ ⟨x, h⟩ else ⊥

/-- set abstract state of `x` in `ρ` to `v`. -/
def setVar {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (x : VarName) (v : A) : Domain n A :=
  fun i => if i.val = x then v else ρ i

/-- push new binding in Domain, shifting all others by one. -/
def pushBinding {n : Nat} {A : Type} [Bot A] (ρ : Domain n A) (v : A) : Domain n A :=
  fun i =>
    if i.val = 0 then v
    else if h : i.val - 1 < n then ρ ⟨i.val - 1, h⟩
    else ⊥

/-- pop `k` bindings from Domain. -/
def popBindings {n : Nat} {A : Type} [Bot A] (k : Nat) (ρ : Domain n A) : Domain n A :=
  fun i =>
    if h : i.val + k < n then ρ ⟨i.val + k, h⟩
    else ⊥

/-- compute height for a domain as sum of height of its elements. -/
def domainHeight {n : Nat} {A : Type} [Bot A] [Max A] [FiniteHeight A] (ρ : Domain n A) : Nat :=
  ((List.finRange n).map (fun i => FiniteHeight.height (ρ i))).sum

/-- height is monotonic wrt lub. -/
private lemma height_le_of_join {A : Type} [Max A] [FiniteHeight A] (a b : A) :
    FiniteHeight.height a ≤ FiniteHeight.height (a ⊔ b) := by
  by_cases h : a ⊔ b = a
  · grind
  · exact Nat.le_of_lt (FiniteHeight.height_mono a b h)

/-- if `A` is of finite height, then so is `Domain n A` for any `n`. -/
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
        Nat.add_one_mul, Nat.add_comm, ge_iff_le]
      exact Nat.add_le_add this (ih fun i ↦ ρ i.succ)
  height_mono ρ₁ ρ₂ h := by
    unfold domainHeight
    have ⟨i, hi₁, hi₂⟩ : ∃ i, i ∈ List.finRange n ∧ ρ₁ i ⊔ ρ₂ i ≠ ρ₁ i := by
      classical
      false_or_by_contra; apply h
      funext i
      rename_i h'
      simp only [List.mem_finRange, ne_eq, true_and, not_exists, Decidable.not_not] at h'
      apply h'
    suffices ∀ (l : List (Fin n)), i ∈ l ->
        (l.map (fun j => FiniteHeight.height (ρ₁ j))).sum <
        (l.map (fun j => FiniteHeight.height ((ρ₁ ⊔ ρ₂) j))).sum from this _ hi₁
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

end Domain

section LBaseSpec
/-- compute the shift depth needed to account for a statement. -/
private def stmtDeclDelta : Lang .Stmt -> Nat
| .Decl _ _ => 1
| .Assign _ _ => 0
| .Seq s₁ s₂ => stmtDeclDelta s₁ + stmtDeclDelta s₂
| .Do _ => 0

/-- a LangEval is a function that takes an abstract domain and
    an expression and computes the output fact for it. -/
abbrev LangEval (n : Nat) (A : Type) [Bot A] := Domain n A -> Lang .Expr -> A

/-- a LangRefine performs a similar function but on edges instead. -/
abbrev LangRefine (n : Nat) (A : Type) [Bot A] := Lang .Expr -> Bool -> Domain n A -> Domain n A

/-- update the current domain according to the eval function based on the
    statement being treated. -/
def transferScopedNode {n : Nat} {A : Type} [Max A] [Bot A]
    (eval : LangEval n A) (node : CFGNode) (ρ : Domain n A) : Domain n A :=
  match node.kind with
  | .stmtExit (.Assign x rhs) => setVar ρ x (eval ρ rhs)
  | .stmtExit (.Decl _ init) => pushBinding ρ (eval ρ init)
  | .exprExit (.Scope s _) => popBindings (stmtDeclDelta s) ρ
  | _ => ρ

/-- carry branch information into the domain. -/
def transferBranchEdge {n : Nat} {A : Type} [Max A] [Bot A]
    (refine : LangRefine n A) (e : CFGEdge) (ρ : Domain n A) : Domain n A :=
  match e.kind, e.src.kind with
  | .trueBranch, .exprExit cond => refine cond true ρ
  | .falseBranch, .exprExit cond => refine cond false ρ
  | _, _ => ρ
end LBaseSpec

class LatticeLike
    (A : Type) [Max A] [Bot A] [FiniteHeight A]
    (nodeTransfer : CFGNode -> A -> A)
    (edgeTransfer : CFGEdge -> A -> A) where
  -- regular lattice structure
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a

  -- edge and node monotoncity
  node_mono : ∀ n, monotoneD (nodeTransfer n)
  edge_mono : ∀ e, monotoneD (edgeTransfer e)
