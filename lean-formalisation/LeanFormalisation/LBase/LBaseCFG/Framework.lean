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
    (s : Lang .Stmt) (R : StateRel) [TranslationReq s R]
    (abs : CEK -> A -> Prop)
    extends LatticeLike A nodeTransfer edgeTransfer where
  entryInit : A
  init_sound : abs (initState s) entryInit
  abs_mono : ∀ {σ : CEK} {a b : A}, a ⊔ b = b -> abs σ a -> abs σ b
  abs_preserves_init : ∀ {a : A}, abs (initState s) a ->
    abs (initState s) (nodeTransfer (stmtCFG s).entry a)
  step_sound : ∀ {σ σ' : CEK} {n n' : NodeOf (stmtCFG s)},
    R σ n -> R σ' n' -> Eval σ σ' -> CFGReach (stmtCFG s) n n' ->
    ∀ (f : GFact (stmtCFG s) A),
      IsForwardPostFixpointOf (stmtCFG s) nodeTransfer edgeTransfer entryInit f ->
    abs σ (f n) -> abs σ' (f n')

/-- for all reachable CEK states σ, there exists a state n such that -/
theorem worklistForwardEdgeOf_soundness_exists {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (σ : CEK) (hreach : CEKReach (initState s) σ) :
    let res := worklistForwardEdgeOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
    ∃ n : NodeOf (stmtCFG s), R σ n ∧ abs σ (res n) := by
  intro res
  have h_postfix : IsForwardPostFixpointOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit res :=
    worklistForwardEdgeOf_sound_postfixpoint (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
      (fun _ => ⊥) ((stmtCFG s).nodes_mem) (by grind only [CFG.nodes_mem, usr List.mem_pmap_of_mem])
  induction hreach with
  | refl =>
    let nen : NodeOf (stmtCFG s) := ⟨(stmtCFG s).entry, (stmtCFG s).entry_in_nodes⟩
    let nex : NodeOf (stmtCFG s) := ⟨(stmtCFG s).exit, (stmtCFG s).exit_in_nodes⟩
    refine ⟨nen, tr.init_related, ?_⟩
    refine fr.abs_mono ?_ (fr.abs_preserves_init fr.init_sound)
    simpa [expectedInOf, nen] using h_postfix nen
  | tail σ_mid h_eval ih =>
    obtain ⟨n, hstep, habs⟩ := ih
    obtain ⟨n', hstep', habs'⟩ := tr.step_sound hstep h_eval
    refine ⟨n', hstep', ?_⟩
    apply fr.step_sound hstep hstep' h_eval habs' res h_postfix
    grind

/-- for all reachable CEK states σ, there exists a state n such that -/
theorem dataflow_soundness_exists {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (σ : CEK) (hreach : CEKReach (initState s) σ) :
    let data := runDataflowOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
    ∃ n : NodeOf (stmtCFG s), R σ n ∧ abs σ (data.2 n) := by
  intro data
  exact worklistForwardEdgeOf_soundness_exists σ hreach

lemma IsForwardFixpointOf.to_postfixpoint {A : Type} [Bot A] [Max A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (outF : GFact g A) [ll : LatticeLike A nodeTransfer edgeTransfer]
    (entryInit : A)
    (hfix : IsForwardFixpointOf g nodeTransfer edgeTransfer entryInit outF) :
    IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit outF := by
  intro n
  rw [hfix n]
  simp [ll.join_idem]

theorem worklistForwardEdgeOf_soundness {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (σ : CEK) (n : NodeOf (stmtCFG s))
    (hreach : CEKReach (initState s) σ) (hrel : R σ n) :
    let res := worklistForwardEdgeOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
    abs σ (res n) := by
  intro res
  have h_postfix :
      IsForwardPostFixpointOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit res := by
    have := (worklistForwardEdgeOf_sound_fixpoint (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
      (fun _ => ⊥) ((stmtCFG s).nodes_mem) (by grind only [CFG.nodes_mem, usr List.mem_pmap_of_mem])
        (by grind [fr.join_comm, fr.bot_le]))
    exact this.to_postfixpoint
  induction hreach generalizing n with
  | refl =>
    unfold IsForwardPostFixpointOf at h_postfix
    have : n = (stmtCFG s).entry := tr.init_uniq hrel
    apply fr.abs_mono (h_postfix n)
    simp only [this, expectedInOf, ↓reduceIte]
    apply fr.abs_preserves_init
    exact fr.init_sound
  | tail hreach h_eval ih =>
    rename_i σ_mid σ'
    have ⟨nmid, hr_mid, hreach_mid⟩ := tr.step_complete h_eval hrel
    specialize ih nmid hr_mid
    grind [fr.step_sound]

theorem dataflow_soundness {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (σ : CEK) (n : NodeOf (stmtCFG s))
    (hreach : CEKReach (initState s) σ) (hrel : R σ n) :
    let data := runDataflowOf (stmtCFG s) nodeTransfer edgeTransfer fr.entryInit
    abs σ (data.2 n) := by
  intro data
  exact worklistForwardEdgeOf_soundness σ n hreach hrel
