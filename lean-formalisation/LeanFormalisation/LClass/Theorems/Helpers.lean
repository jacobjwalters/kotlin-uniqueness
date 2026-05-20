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

lemma suffix_eq (Γ₁ Γ₂ Γ₃ : List α) :
  Γ₃ = Γ₁ ++ Γ₂ →
  n ≤ Γ₂.length →
  (Γ₂.drop (Γ₂.length - n)) = (Γ₃.drop (Γ₃.length - n)) := by
    intro eq le
    rw [eq, List.drop_append]
    rw [List.drop_eq_nil_iff (l := Γ₁).mpr]
    { grind }
    grind
