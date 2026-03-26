/-
  Concrete CEK/CFG relation definitions and the abstract `TranslationReq` class.

  These definitions are kept separate from the structural CFG proofs so that
  `TranslationReq` can be instantiated independently — e.g. to test concrete
  definitions without depending on the proof obligations in `AltCFGProofs`.
-/

import LeanFormalisation.LBaseCFG.alt.AltCFG

open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal

namespace LeanFormalisation
namespace AltCFGProofs

section Translation

abbrev StateRel := CEK -> CFGNode -> Prop

def CFGStep (g : CFG) (n m : CFGNode) : Prop :=
  ∃ e ∈ g.edges, e.src = n ∧ e.dst = m

abbrev CFGReach (g : CFG) := Relation.ReflTransGen (CFGStep g)
abbrev CEKReach := Relation.ReflTransGen Eval

/-!
## basic requirements for the semantics/cfg correspondence
-/
/--
Abstract translation-correctness obligations for a statement `s` and a
user-supplied CEK/CFG relation `R : StateRel`.
-/
class TranslationReq (s : Lang .Stmt) (R : StateRel) : Prop where
  init_related : R (initState s) (stmtCFG s).entry
  terminal_related : ∀ E, R (terminalState E) (stmtCFG s).exit

  step_sound :
    ∀ {σ σ' n}, R σ n -> Eval σ σ' ->
      ∃ n', R σ' n' ∧ CFGStep (stmtCFG s) n n'

  edge_complete :
    ∀ {n m}, CFGStep (stmtCFG s) n m ->
      ∃ σ σ', CEKReach (initState s) σ ∧ R σ n ∧ Eval σ σ' ∧ R σ' m

/-!
## cfg translation correctness: two directions
-/

/--
one side correspondence between reachability and relation
-/
theorem translation_sound_reachability
      (s : Lang .Stmt) (R : StateRel) [tr : TranslationReq s R]
      {σ σ' : CEK} {n : CFGNode}
      (hrel : R σ n)
      (hreach : CEKReach σ σ') :
    ∃ n', R σ' n' ∧ CFGReach (stmtCFG s) n n' := by
  induction hreach with
  | refl => exists n
  | tail hsb hbc ih =>
    obtain ⟨mid, hbmid, hreachMid⟩ := ih
    obtain ⟨mid', hcmid', hstepMid⟩ :=
      tr.step_sound hbmid hbc
    exact ⟨mid', hcmid', Relation.ReflTransGen.tail hreachMid hstepMid⟩

-- theorem translation_complete_reachability
--       (s : Lang .Stmt) (R : StateRel) [tr : TranslationReq s R]
--       {σ : CEK} {n m : CFGNode}
--       (hrel : R σ n) (hcorr : CEKReach (initState s) σ)
--       (hpath : CFGReach (stmtCFG s) n m) :
--     ∃ σ', CEKReach σ σ' ∧ R σ' m := by
--   induction hpath with
--   | refl =>
--     exists σ
--   | tail hsb hbc ih => case tail b c =>
--     obtain ⟨mid, hbmid, hreacMid⟩ := ih
--     obtain ⟨σ', hstep, hrel'⟩ : ∃ σ', Eval mid σ' ∧ R σ' c := by
--       exact tr.edge_complete hbc hreacMid
--         (Relation.ReflTransGen.trans hcorr hbmid)
--     exact ⟨σ', Relation.ReflTransGen.tail hbmid hstep, hrel'⟩

end Translation

end AltCFGProofs
end LeanFormalisation
