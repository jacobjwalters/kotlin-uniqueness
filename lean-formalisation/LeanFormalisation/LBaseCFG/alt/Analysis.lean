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

-- node/edgeTransfer to maintain branch sensitivity -> feed choice information
-- to the branch's environments.
def worklistForwardEdge
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    : fact A × fact A :=
  match wl with
  | [] => (inF, outF)
  | n :: rest =>
      let newIn :=
        if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n
      let newOut := outF n ⊔ nodeTransfer n newIn
      if newOut = outF n then
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF rest
      else
        let inF' := inF.update n newIn
        let outF' := outF.update n newOut
        let wl' := rest ++ g.succ n
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF' outF' wl'
termination_by (factHeight g outF, wl.length)
decreasing_by
  · refine Prod.Lex.right (factHeight g outF) ?_
    grind
  · refine Prod.Lex.left (rest ++ g.succ n).length (n :: rest).length ?_
    simp [factHeight]

    -- [[ FOR CLAUDE ]]
    -- hi!!
    -- prove the theorem from here, or argue why it can't be proven in its current
    -- form, provide the fixes needed to prove it, and prove it.

    -- i suspect some sort of combination of `grind`, the lemmas in `Utils` as well
    -- as the global property on maxheight will be needed to prove this, but you
    -- do you.
    sorry

abbrev Domain (A : Type) [Max A] [Bot A] := List A

instance {A : Type} [Max A] [Bot A] : Bot (Domain A) where
  bot := []

def domainJoin {A : Type} [Max A] [Bot A] : Domain A -> Domain A -> Domain A
| [], ys => ys
| xs, [] => xs
| x :: xs, y :: ys => (x ⊔ y) :: domainJoin xs ys

instance {A : Type} [Max A] [Bot A] : Max (Domain A) where
  max := domainJoin

def getVar {A : Type} [Max A] [Bot A] (ρ : Domain A) (x : VarName) : A :=
  ρ.getD x ⊥

def setVar {A : Type} [Max A] [Bot A] : Domain A -> VarName -> A -> Domain A
| [], 0, s => [s]
| [], x + 1, s => ⊥ :: setVar [] x s
| _ :: tl, 0, s => s :: tl
| hd :: tl, x + 1, s => hd :: setVar tl x s

def pushBinding {A : Type} [Max A] [Bot A] (ρ : Domain A) (v : A) : Domain A :=
  v :: ρ

def popBindings {A : Type} [Max A] [Bot A] (k : Nat) (ρ : Domain A) : Domain A :=
  ρ.drop k

instance {A : Type} [Max A] [Bot A] [Repr A] : Repr (Domain A) where
  reprPrec := fun d _ =>
    let rec go (i : Nat) : Domain A -> List String
      | [] => []
      | v :: tl => s!"x{i}:{repr v}" :: go (i + 1) tl
    s!"[{String.intercalate ", " (go 0 d)}]"

section LangSpecific

def stmtDeclDelta : Lang .Stmt -> Nat
| .Decl _ _ => 1
| .Assign _ _ => 0
| .Seq s₁ s₂ => stmtDeclDelta s₁ + stmtDeclDelta s₂
| .Do _ => 0

abbrev LangEval (A : Type) [Max A] [Bot A] := Domain A -> Lang .Expr -> A

def transferScopedNode {A : Type} [Max A] [Bot A]
    (eval : LangEval A) (n : CFGNode) (ρ : Domain A) : Domain A :=
  match n.kind with
  | .stmtExit (.Assign x rhs) => setVar ρ x (eval ρ rhs)
  | .stmtExit (.Decl _ init) => pushBinding ρ (eval ρ init)
  | .exprExit (.Scope s _) => popBindings (stmtDeclDelta s) ρ
  | _ => ρ

def transferBranchEdge {A : Type} [Max A] [Bot A]
    (refine : Lang .Expr -> Bool -> Domain A -> Domain A)
    (e : CFGEdge) (ρ : Domain A) : Domain A :=
  match e.kind, e.src.kind with
  | .trueBranch, .exprExit cond => refine cond true ρ
  | .falseBranch, .exprExit cond => refine cond false ρ
  | _, _ => ρ

end LangSpecific
