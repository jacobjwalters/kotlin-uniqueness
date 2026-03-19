import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis

open LeanFormalisation.AltCFG

def expectedIn {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : fact A) (n : CFGNode) : A :=
  if n = g.entry then entryInit else joinPredEdges g edgeTransfer outF n

def IsForwardFixpoint {A : Type} [Bot A] [Max A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) : Prop :=
  (∀ n, inF n = expectedIn g edgeTransfer entryInit outF n) ∧
  (∀ n, outF n = nodeTransfer n (inF n))

def IsForwardPostFixpoint {A : Type} [Bot A] [Max A]
      (g : CFG)
      (nodeTransfer : CFGNode -> A -> A)
      (edgeTransfer : CFGEdge -> A -> A)
      (entryInit : A)
      (outF : fact A) : Prop :=
   ∀ n, (nodeTransfer n (expectedIn g edgeTransfer entryInit outF n)) ⊔ (outF n) = (outF n)

def monotoneD {A : Type} [Max A] (f : A -> A) : Prop :=
  ∀ x y, x ⊔ y = x -> (f x) ⊔ (f y) = (f x)

def factLe {A : Type} [Max A] (f g : fact A) : Prop :=
  ∀ n, (f n) ⊔ (g n) = (f n)

class WorklistReq {A : Type} [Bot A] [Max A] [FiniteHeight A]
    (g : CFG)
    (nodeTransfer : CFGNode -> A -> A)
    (edgeTransfer : CFGEdge -> A -> A) : Prop where
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a
  node_mono : ∀ n, monotoneD (nodeTransfer n)
  edge_mono : ∀ e, monotoneD (edgeTransfer e)

theorem worklist_sound_postfixpoint
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (in0 out0 : fact A) (wl0 : List CFGNode)
    [WorklistReq g nodeTransfer edgeTransfer] :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit in0 out0 wl0
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res.2 := by
  intros n
  sorry

theorem worklist_sound_fixpoint
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (in0 out0 : fact A) (wl0 : List CFGNode)
    [WorklistReq g nodeTransfer edgeTransfer] :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit in0 out0 wl0
    IsForwardFixpoint g nodeTransfer edgeTransfer entryInit res.1 res.2 := by
  sorry

theorem worklist_complete_least_postfixpoint
    [DecidableEq CFGNode]
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (in0 out0 : fact A) (wl0 : List CFGNode)
    [WorklistReq g nodeTransfer edgeTransfer]
    (Hinit : ∀ n, (out0 n) ⊔ (in0 n) = (out0 n))
    (post : fact A) (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit post) :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit in0 out0 wl0
    factLe res.2 post := by
  sorry

theorem worklist_complete_fixpoint_stability
    [DecidableEq CFGNode]
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    [WorklistReq g nodeTransfer edgeTransfer]
    (hfp : IsForwardFixpoint g nodeTransfer edgeTransfer entryInit inF outF) :
    worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF wl = (inF, outF) := by
  sorry
