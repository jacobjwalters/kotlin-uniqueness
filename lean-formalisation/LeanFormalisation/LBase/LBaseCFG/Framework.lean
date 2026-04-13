import LeanFormalisation.LBase.LBaseCFG.AltCFG
import LeanFormalisation.LBase.LBaseCFG.Analysis
import LeanFormalisation.LBase.LBaseCFG.AnalysisProofs
import LeanFormalisation.LBase.LBaseCFG.Correspondence

open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFGProofs

/-- An analysis `Framework` is a structure comprised of
    - a lattice-like abstract domain `A`,
    - transfer functions describing the update to the domain based on the
      CFG state
    - an abstraction function to turn a concrete state to an element of the
      abstract domain

    Additionally, we guarantee regular lattice properties on `A`, and
    monotonicity with respect to it of the transfer functions.
-/
class Framework
    (A : Type) [Bot A] [Max A] [FiniteHeight A]
    (edgeTransfer : CFGEdge -> A -> A)
    (nodeTransfer : CFGNode -> A -> A)
    (s : Lang .Stmt) (R : StateRel)
    (abs : CEK -> A -> Prop)
    extends LatticeLike A nodeTransfer edgeTransfer where

  abs_mono : ∀ {σ : CEK} {a b : A}, a ⊔ b = b -> abs σ a -> abs σ b
  abs_preserves_init : ∀ {a : A}, abs (initState s) a ->
    abs (initState s) (nodeTransfer (stmtCFG s).entry a)

  step_sound : ∀ {σ σ' : CEK} {n n' : CFGNode} {entryInit : A},
    R σ n -> R σ' n' -> Eval σ σ' -> CFGReach (stmtCFG s) n n' ->
    ∀ (f : fact A), IsForwardPostFixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit f ->
    abs σ (f n) -> abs σ' (f n')

/-- for all reachable CEK states σ, there exists a state n such that -/
theorem dataflow_soundness_exists {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (entryInit : A) (out0 : fact A)
    (wl0 : List CFGNode) (hwl0 : ∀ x ∈ wl0, x ∈ (stmtCFG s).nodes)
    (h_inv0 : ∀ m, m ∉ wl0 ->
        nodeTransfer m (expectedIn (stmtCFG s) edgeTransfer entryInit out0 m) ⊔ out0 m = out0 m)
    (hinit_sound : abs (initState s) entryInit)
    (σ : CEK) (hreach : CEKReach (initState s) σ) :
    let res := worklistForwardEdge (stmtCFG s) nodeTransfer edgeTransfer entryInit out0 wl0 hwl0
    ∃ n, R σ n ∧ abs σ (res n) := by
  intro res
  have h_postfix : IsForwardPostFixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit res :=
    worklist_sound_postfixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit out0 wl0 hwl0 h_inv0
  induction hreach with
  | refl =>
    refine ⟨(stmtCFG s).entry, tr.init_related, ?_⟩
    refine fr.abs_mono ?_ (fr.abs_preserves_init hinit_sound)
    simpa [expectedIn] using h_postfix (stmtCFG s).entry
  | tail σ_mid h_eval ih =>
    obtain ⟨n, hstep, habs⟩ := ih
    obtain ⟨n', hstep', habs'⟩ := tr.step_sound hstep h_eval
    refine ⟨n', hstep', ?_⟩
    apply fr.step_sound hstep hstep' h_eval habs' res h_postfix
    grind

theorem dataflow_soundness {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (entryInit : A) (out0 : fact A)
    (wl0 : List CFGNode) (hwl0 : ∀ x ∈ wl0, x ∈ (stmtCFG s).nodes)
    (h_inv0 : ∀ m, m ∉ wl0 ->
        nodeTransfer m (expectedIn (stmtCFG s) edgeTransfer entryInit out0 m) ⊔ out0 m = out0 m)
    (hinit_sound : abs (initState s) entryInit)
    (σ : CEK) (n : CFGNode) (hreach : CEKReach (initState s) σ) (hrel : R σ n) :
    let res := worklistForwardEdge (stmtCFG s) nodeTransfer edgeTransfer entryInit out0 wl0 hwl0
    abs σ (res n) := by
  intro res
  have h_postfix : IsForwardPostFixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit res :=
    worklist_sound_postfixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit out0 wl0 hwl0 h_inv0
  induction hreach generalizing n with
  | refl =>
    unfold IsForwardPostFixpoint at h_postfix
    have : n = (stmtCFG s).entry := tr.init_uniq hrel
    apply fr.abs_mono (h_postfix n)
    simp only [this, expectedIn, ↓reduceIte]
    apply fr.abs_preserves_init
    assumption
  | tail hreach h_eval ih =>
    rename_i σ_mid σ'
    have ⟨nmid, hr_mid, hreach_mid⟩ := tr.step_complete h_eval hrel
    specialize ih nmid hr_mid
    grind [fr.step_sound]
