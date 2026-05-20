import Batteries.Tactic.Init

import LeanFormalisation.LClass.LClassDefs
import LeanFormalisation.LClass.Theorems.Helpers

variable (cCnt : Nat) (defs : Defs cCnt)

theorem typ_permutation
  (Γ₁ Γ₂ : Ctx) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  Typ cCnt defs tg Δ₁ Γ₁ e Γ₃ → Typ cCnt defs tg Δ₁ Γ₂ e Γ₃ := by
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
  (Γ₁ : Ctx) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  Typ cCnt defs tg Δ₁ Γ₁ s Γ₂ → ∃ Γ₃ : TypR tg, Γ₃.extR Γ₁ = Γ₂ := by
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
  (type : Ty) :
  Typ cCnt defs .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

lemma loop_jump_ext (Δ : JCtx cCnt defs) :
  LoopJump cCnt defs Δ l ↔
  (l < Δ.length ∧ ∀ i ≤ l, ∃ res, Δ[i]! = .Loop res):= by
    constructor
    { intro hl
      induction hl
      { simp }
      constructor
      { grind }
      intro i hi
      by_cases h0 : i = 0
      { rw [h0]
        simp }
      rename_i a_ih
      rcases a_ih.2 (i - 1) (by grind)
      grind }
    intro hall
    induction l generalizing Δ
    { cases Δ
      { grind }
      have := hall.2 0 (by simp)
      grind [LoopJump] }
    cases Δ
    { grind }
    rcases hall.2 0 (by simp) with ⟨res, hres⟩
    simp at hres
    simp only [hres]
    apply LoopJump.Loop
    simp only [Nat.add_one_sub_one]
    rename_i a_ih _ _
    apply a_ih
    constructor
    { grind }
    intro i hi
    rcases hall.2 (i + 1) (by omega)
    grind

/-- `MethodJump Δ l cls m` implies position `l` of `Δ` is in range and
contains exactly the `Method cls m` frame. -/
lemma method_jump_lookup (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls)) :
    MethodJump cCnt defs Δ l cls m →
    l < Δ.length ∧ Δ[l]! = .Method cls m := by
  intro hj
  induction hj <;> grind

lemma method_jump_delta_ext (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls)) :
  MethodJump cCnt defs Δ l cls m → MethodJump cCnt defs (Δ ++ Δ₁) l cls m := by
    intro hl
    induction hl <;> grind [MethodJump]

/-- `MethodJump` is preserved when every `Loop n` frame in `Δ` is replaced by
`Loop (n + k)` for some constant `k`. Used in `lang_extension`. -/
lemma method_jump_loop_map (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls)) (k : Nat) :
    MethodJump cCnt defs Δ l cls m →
    MethodJump cCnt defs
      (Δ.map (fun x => match x with | .Loop n => .Loop (n + k) | val => val))
      l cls m := by
  intro hj
  induction hj <;> grind [MethodJump]

theorem lang_extension
  (tg : Tag) (e : Lang tg) (res : TypR tg)
  (Γ₁ Γ₂ : Ctx) :
    Typ cCnt defs tg Δ₁ Γ₁ e res →
    Typ cCnt defs tg (Δ₁.map
        (fun x => match x with
          | .Loop n => .Loop (n + Γ₂.length)
          | val => val))
      (Γ₁ ++ Γ₂) e
      (res.extR Γ₂) := by
    intro h
    unhygienic induction h generalizing Γ₂ <;> try solve_by_elim
    { rw [TypR.extR]
      apply Typ.VarAccess
      grind }
    { apply Typ.FieldAccess <;> solve_by_elim }
    { apply Typ.Call <;> solve_by_elim }
    { apply Typ.Return <;> try solve_by_elim
      apply method_jump_loop_map
      solve_by_elim }
    { apply Typ.WhileExpr
      { solve_by_elim }
      { -- map distributes over cons: map f (n :: Δ) = f n :: map f Δ
        -- and f n = n + len = (Γ₁ ++ Γ₂).length
        have h := a_ih_1 Γ₂
        simp only [List.map_cons, List.length_append,
          TypR.extR] at h ⊢
        exact h } }
    { apply Typ.BreakExpr
      induction a <;> solve_by_elim }
    { solve_by_elim [Typ.ScopeExpr] }
    { rw [TypR.extR]
      apply Typ.VarAssign _ _ _ (a_ih Γ₂)
      grind }
    solve_by_elim [Typ.Seq]

theorem typ_ext
  (e : Lang .Expr) (type : Ty) (Γ₁ Γ₂ : Ctx) :
    Typ cCnt defs .Expr Δ₁ Γ₁ e (.Expr type) →
    Typ cCnt defs .Expr (Δ₁.map
        (fun x => match x with
          | .Loop n => .Loop (n + Γ₂.length)
          | val => val)) (Γ₁ ++ Γ₂) e
      (.Expr type) := by
    intro h
    have lm := lang_extension cCnt defs _ _ _ _ Γ₂ h
    rw [TypR.extR] at lm
    apply lm


lemma lift_value_type
  (v : Value) (type : Ty) :
  Typ cCnt defs .Expr Γ Δ e (.Expr type) →
  liftValue v e → ValueTyp cCnt defs v type S := by
    intro ht
    cases v <;> cases ht <;> grind [ValueTyp, liftValue]

lemma value_typ_ext (ty : Ty) :
  ValueTyp cCnt defs v ty S → a ∉ S → ValueTyp cCnt defs v ty (S.insert a s) := by
    intro hv ha
    unhygienic induction hv <;> try grind [ValueTyp]
    apply ValueTyp.Cls
    { rw [Finmap.lookup_insert_of_ne]
      { exact a_2 }
      intro heq
      have st := (Finmap.mem_iff (a := a_1) (s := S_1)).mpr (by
        eapply Exists.intro
        solve_by_elim)
      grind }
    { grind }
    grind

lemma loop_jump_delta_ext :
  LoopJump cCnt defs Δ l → LoopJump cCnt defs (Δ ++ Δ₁) l := by
    intro hl
    induction hl <;> grind [LoopJump]


theorem lang_extension_delta
  (tg : Tag) (e : Lang tg) (res : TypR tg)
  (Γ₁ : Ctx) :
    Typ cCnt defs tg Δ₁ Γ₁ e res →
    Typ cCnt defs tg (Δ₁ ++ Δ₂) Γ₁ e res := by
    intro h
    unhygienic induction h generalizing Δ₂ <;> try solve_by_elim
    { apply Typ.FieldAccess <;> solve_by_elim }
    { apply Typ.Call <;> solve_by_elim }
    { apply Typ.Return <;> try solve_by_elim
      apply method_jump_delta_ext
      solve_by_elim }
    apply Typ.BreakExpr
    induction a <;> solve_by_elim
