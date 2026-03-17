import LeanFormalisation.LBaseCFG.alt.AltCFG

open LeanFormalisation.AltCFG

abbrev fact (A : Type) := CFGNode -> A

def fact.update {A : Type} (f : fact A) (n : CFGNode) (v : A) : fact A :=
  fun m => if m = n then v else f m

def joinPredEdges [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge → A → A)
    (outF : fact A) (n : CFGNode) : A :=
  (g.inEdges n).foldl (fun acc e => acc ⊔ edgeTransfer e (outF e.src)) ⊥

-- node/edgeTransfer to maintain branch sensitivity -> feed choice information
-- to the branch's environments.
partial def worklistForwardEdge
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    : fact A × fact A :=
  match wl with
  | [] => (inF, outF)
  | n :: rest =>
      let newIn :=
        if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n
      let newOut := nodeTransfer n newIn
      if newOut = outF n then
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF rest
      else
        let inF' := inF.update n newIn
        let outF' := outF.update n newOut
        let wl' := rest ++ g.succ n
        worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF' outF' wl'

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
