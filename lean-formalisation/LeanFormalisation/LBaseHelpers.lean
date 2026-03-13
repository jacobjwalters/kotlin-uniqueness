import LeanFormalisation.LBase

lemma neg_index_eq (Γ₁ Γ₂ : Γ) (i : Nat) :
  i < Γ₁.length →
  Γ₁[Γ₁.length - 1 - i]? = (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? := by
    intro hlt
    unhygienic induction Γ₂
    { simp }
    grind

lemma neg_index_l (Γ₁ Γ₂ : Γ) (i : Nat) :
  i < Γ₂.length + Γ₁.length → Γ₁.length ≤ i →
  (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? = Γ₂[Γ₂.length - 1 - (i - Γ₁.length)]? := by
    intro hlt
    unhygienic induction Γ₂ <;> grind

lemma neg_index_r (Γ₁ Γ₂ : Γ) (i : Nat) :
  i < Γ₁.length →
  (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? = Γ₁[Γ₁.length - 1 - i]? := by
    intro hlt
    unhygienic induction Γ₂
    { simp }
    grind
