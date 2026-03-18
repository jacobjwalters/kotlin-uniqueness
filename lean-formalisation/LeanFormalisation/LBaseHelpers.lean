import LeanFormalisation.LBase

lemma neg_index_eq (Γ₁ Γ₂ : Ctx) (i : Nat) :
  i < Γ₁.length →
  Γ₁[Γ₁.length - 1 - i]? = (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? := by
    intro hlt
    induction Γ₂ with
    | nil => simp
    | cons _ _ => grind

lemma neg_index_l (Γ₁ Γ₂ : Ctx) (i : Nat) :
  i < Γ₂.length + Γ₁.length → Γ₁.length ≤ i →
  (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? = Γ₂[Γ₂.length - 1 - (i - Γ₁.length)]? := by
    intro hlt
    induction Γ₂ with
    | nil => grind
    | cons _ _ => grind

lemma neg_index_r (Γ₁ Γ₂ : Ctx) (i : Nat) :
  i < Γ₁.length →
  (Γ₂ ++ Γ₁)[Γ₂.length + Γ₁.length - 1 - i]? = Γ₁[Γ₁.length - 1 - i]? := by
    intro hlt
    induction Γ₂ with
    | nil => simp
    | cons _ _ => grind
