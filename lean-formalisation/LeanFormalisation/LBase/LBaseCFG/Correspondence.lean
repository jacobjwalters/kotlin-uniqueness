/-
  Concrete CEK/CFG relation definitions and the abstract `TranslationReq` class.

  These definitions are kept separate from the structural CFG proofs so that
  `TranslationReq` can be instantiated independently — e.g. to test concrete
  definitions without depending on the proof obligations in `AltCFGProofs`.
-/

import LeanFormalisation.LBase.LBaseCFG.AltCFG
import Mathlib.Logic.Relation

open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal

namespace LeanFormalisation
namespace AltCFGProofs

section Translation

abbrev StateRel {g : CFG} := CEK -> NodeOf g -> Prop

def CFGStep (g : CFG) (n m : NodeOf g) : Prop :=
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
  init_related : R (initState s) ⟨(stmtCFG s).entry, (stmtCFG s).entry_in_nodes⟩
  terminal_related : ∀ E, R (terminalState E []) ⟨(stmtCFG s).exit, (stmtCFG s).exit_in_nodes⟩

  init_uniq : ∀ {n}, R (initState s) n -> n = (stmtCFG s).entry

  step_sound :
    ∀ {σ σ' n}, R σ n -> Eval σ σ' ->
      ∃ n', R σ' n' ∧ CFGReach (stmtCFG s) n n'

  step_complete :
    ∀ {σ σ' n'}, Eval σ σ' -> R σ' n' ->
      ∃ n, R σ n /\ CFGReach (stmtCFG s) n n'

/-!
## cfg translation correctness: two directions
-/

/--
one side correspondence between reachability and relation
-/
theorem translation_sound_reachability
      (s : Lang .Stmt) (R : StateRel) [tr : TranslationReq s R]
      {σ σ' : CEK} {n : NodeOf (stmtCFG s)}
      (hrel : R σ n)
      (hreach : CEKReach σ σ') :
    ∃ n', R σ' n' ∧ CFGReach (stmtCFG s) n n' := by
  induction hreach with
  | refl => exists n
  | tail hsb hbc ih =>
    obtain ⟨mid, hbmid, hreachMid⟩ := ih
    obtain ⟨mid', hcmid', hstepMid⟩ :=
      tr.step_sound hbmid hbc
    exact ⟨mid', hcmid', Relation.ReflTransGen.trans hreachMid hstepMid⟩

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
