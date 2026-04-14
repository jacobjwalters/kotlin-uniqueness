import Mathlib.Tactic.Basic


lemma p_index_r (Γ₁ Γ₂ : List α) (i : Nat) :
  i < Γ₁.length →
  (Γ₂ ++ Γ₁)[i + Γ₂.length]? = Γ₁[i]? := by
    intro hlt
    induction Γ₂ with
    | nil => simp
    | cons _ _ => grind

lemma List.eq_take_drop (Γ : List α) (n : Nat) :
  Γ = Γ.take n ++ Γ.drop n := by
    induction Γ generalizing n
    { grind }
    by_cases ∃ k, n = k + 1
    { grind }
    simp at *
