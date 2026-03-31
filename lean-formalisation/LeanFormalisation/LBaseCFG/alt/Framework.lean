import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis

open LeanFormalisation.AltCFG

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
    (abs : CEK -> A -> Prop) where

  -- regular lattice structure
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a

  -- monotonicity of the transfer
  node_mono : ∀ n, monotoneD (nodeTransfer n)
  edge_mono : ∀ e, monotoneD (edgeTransfer e)
