import Batteries.Tactic.Init

import LeanFormalisation.LClass.LClassDefs
import LeanFormalisation.LClass.Theorems.Helpers

variable (cCnt : Nat) (defs : Defs cCnt)

theorem lang_det
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) (S : Store cCnt defs) :
  Typ cCnt defs tg cCur mCur Δ₁ Γ₁ s Γ₂ →
  Typ cCnt defs tg cCur mCur Δ₁ Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    unhygienic induction h1 <;> try grind
    all_goals try
    { cases h2
      grind }
    stop sorry

theorem typ_permutation
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ Γ₂ : Ctx) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  Typ cCnt defs tg cCur mCur Δ₁ Γ₁ e Γ₃ → Typ cCnt defs tg cCur mCur Δ₁ Γ₂ e Γ₃ := by
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


lemma stmt_mono
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  Typ cCnt defs tg cCur mCur Δ₁ Γ₁ s Γ₂ → ∃ Γ₃ : TypR tg, Γ₃.extR Γ₁ = Γ₂ := by
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


lemma stmt_decl
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (type : Ty) :
  Typ cCnt defs .Stmt cCur mCur Δ₁ Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

theorem lang_extension
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (tg : Tag) (e : Lang tg) (res : TypR tg)
  (Γ₁ Γ₂ : Ctx) :
    Typ cCnt defs tg cCur mCur Δ₁ Γ₁ e res →
    Typ cCnt defs tg cCur mCur (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) (e)
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
    { exact Typ.BreakExpr cCur_1 mCur_1 .unit _
        (by rw [List.length_map]; exact a) }
    { solve_by_elim [Typ.ScopeExpr] }
    { rw [TypR.extR]
      apply Typ.VarAssign _ _ _ _ _ (a_ih Γ₂)
      grind }
    solve_by_elim [Typ.Seq]

theorem typ_ext
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (e : Lang .Expr) (type : Ty) (Γ₁ Γ₂ : Ctx) :
    Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ e (.Expr type) →
    Typ cCnt defs .Expr cCur mCur (Δ₁.map (fun x => x + Γ₂.length)) (Γ₁ ++ Γ₂) e
      (.Expr type) := by
    intro h
    have lm := lang_extension cCnt defs _ _ _ _ _ _ Γ₂ h
    rw [TypR.extR] at lm
    apply lm


lemma lift_value_type
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (v : Value) (type : Ty) :
  Typ cCnt defs .Expr cCur mCur Γ Δ e (.Expr type) →
  liftValue v e → ValueTyp cCnt defs v type S := by
    intro ht
    cases v <;> cases ht <;> grind [ValueTyp, liftValue]
