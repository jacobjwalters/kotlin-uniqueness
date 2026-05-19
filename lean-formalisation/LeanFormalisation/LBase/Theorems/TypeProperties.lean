import Batteries.Tactic.Init

import LeanFormalisation.LBase.LBaseDefs
import LeanFormalisation.LBase.Theorems.Helpers

theorem typ_permutation (Γ₁ Γ₂ : Ctx) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  Typ tg Δ₁ Γ₁ e Γ₃ → Typ tg Δ₁ Γ₂ e Γ₃ := by
    intro hg
    have leq : Γ₁.length = Γ₂.length := by
      by_cases h1: Γ₂.length < Γ₁.length
      { have hi := hg Γ₁[Γ₁.length - 1] (Γ₁.length - 1)
        clear hg
        grind }
      by_cases h2: Γ₁.length < Γ₂.length
      { have hi := hg Γ₂[Γ₂.length - 1] (Γ₂.length - 1)
        clear hg
        grind }
      grind
    have : Γ₁ = Γ₂ := by
      ext
      clear e
      rename_i idx el
      have hi := hg el idx
      by_cases hid: idx < Γ₁.length
      { clear hg
        grind }
      grind
    rw [this]
    grind


lemma stmt_mono (Γ₁ : Ctx) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  Typ tg Δ₁ Γ₁ s Γ₂ → ∃ Γ₃ : TypR tg, Γ₃.extR Γ₁ = Γ₂ := by
    intro hs
    unhygienic induction hs <;> try grind
    all_goals try
    { eapply Exists.intro
      rw [TypR.extR] }
    { eapply Exists.intro
      rw [TypR.extR]
      rotate_left
      { exact [type] }
      grind }
    { eapply Exists.intro
      rw [TypR.extR]
      rotate_left
      { exact [] }
      grind }
    { have ⟨g, hg⟩:= a_ih
      unhygienic cases g
      have ⟨g1, hg1⟩:= a_ih_1
      unhygienic cases g1
      simp only [TypR.extR] at *
      exists TypR.Stmt (Γ₁_3 ++ Γ₁_2)
      grind }
    eapply Exists.intro
    rw [TypR.extR]
    rotate_left
    { exact [] }
    grind


lemma stmt_decl (type : Ty) : Typ .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

theorem lang_extension (tg : Tag) (e : Lang tg) (res : TypR tg)
    (Γ₁ Γ₂ : Ctx) :
    Typ tg Δ₁ Γ₁ e res →
    Typ tg (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) (e)
      (res.extR Γ₂) := by
    intro h
    unhygienic induction h generalizing Γ₂ <;>try solve_by_elim
    { rw [TypR.extR]
      apply Typ.VarAccess
      grind }
    { apply Typ.WhileExpr
      { solve_by_elim }
      { -- map distributes over cons: map f (n :: Δ) = f n :: map f Δ
        -- and f n = n + len = (Γ₁ ++ Γ₂).length
        have h := a_ih_1 Γ₂
        simp only [List.map_cons, List.length_append,
          TypR.extR] at h ⊢
        exact h } }
    { exact Typ.BreakExpr _ _
        (by rw [List.length_map]; exact a) }
    { solve_by_elim [Typ.ScopeExpr] }
    { rw [TypR.extR]
      apply Typ.VarAssign _ _ _ (a_ih Γ₂)
      grind }
    solve_by_elim [Typ.Seq]

theorem typ_ext (e : Lang .Expr) (type : Ty) (Γ₁ Γ₂ : Ctx) :
    Typ .Expr Δ₁ Γ₁ e (.Expr type) →
    Typ .Expr (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) e
      (.Expr type) := by
    intro h
    have lm := lang_extension _ _ _ _ Γ₂ h
    rw [TypR.extR] at lm
    apply lm

lemma lift_value_type (v : Value) (type : Ty) :
  Typ .Expr Γ Δ (liftValue v) (.Expr type) → value_type v type := by
    intro ht
    cases v <;> cases ht <;> grind [value_type]
