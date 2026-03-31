import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis
import LeanFormalisation.LBaseCFG.alt.AnalysisProofs
import LeanFormalisation.LBaseCFG.alt.Correspondence

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
    (A : Type) [Bot A] [Max A]
    (edgeTransfer : CFGEdge -> A -> A)
    (nodeTransfer : CFGNode -> A -> A)
    (s : Lang .Stmt) (R : StateRel)
    (abs : CEK -> A -> Prop)
    extends LatticeLike A nodeTransfer edgeTransfer where

  abs_mono : ∀ {σ : CEK} {a b : A}, a ⊔ b = b → abs σ a → abs σ b
  abs_preserves_init : ∀ {a : A}, abs (initState s) a →
    abs (initState s) (nodeTransfer (stmtCFG s).entry a)
  step_sound : ∀ {σ σ' : CEK} {n n' : CFGNode} {entryInit : A},
    R σ n → R σ' n' → Eval σ σ' → CFGReach (stmtCFG s) n n' →
    ∀ (f : fact A), IsForwardPostFixpoint (stmtCFG s) nodeTransfer edgeTransfer entryInit f →
    abs σ (f n) → abs σ' (f n')

theorem dataflow_soundness {s : Lang .Stmt}
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    {edgeTransfer : CFGEdge -> A -> A} {nodeTransfer : CFGNode -> A -> A}
    {abs : CEK -> A -> Prop} {R : StateRel} [tr : TranslationReq s R]
    [fr : Framework A edgeTransfer nodeTransfer s R abs]
    (entryInit : A) (out0 : fact A)
    (wl0 : List CFGNode) (hwl0 : ∀ x ∈ wl0, x ∈ (stmtCFG s).nodes)
    (h_inv0 : ∀ m, m ∉ wl0 →
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
  | tail σ_mid h_eval ih =>
    -- From reachability, obtain a CFG node related to the intermediate state
    obtain ⟨n_mid, hrel_mid, _⟩ :=
      translation_sound_reachability s R tr.init_related σ_mid
    -- From step soundness of the translation, obtain the successor node
    obtain ⟨n', hrel', hcfgreach⟩ := tr.step_sound hrel_mid h_eval
    -- By functionality of R, n' = n
    have heq : n' = n := tr.rel_uniq hrel' hrel
    subst heq
    -- Apply the framework's step soundness
    exact fr.step_sound hrel_mid hrel h_eval hcfgreach res h_postfix (ih n_mid hrel_mid)
