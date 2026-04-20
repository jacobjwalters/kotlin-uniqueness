import Batteries.Tactic.Init
import Mathlib.Data.Nat.Basic

import LeanFormalisation.LClass.LClassDefs
import LeanFormalisation.LClass.Theorems.Helpers

variable (cCnt : Nat) (defs : Defs cCnt)

lemma coh_len (E : Environment) (Γ : Ctx) (S : Store cCnt defs) :
  Coh cCnt defs E S Γ → E.length = Γ.length := by
    intro h
    induction h <;> grind

lemma coh_get (E : Environment) (Γ : Ctx) (S : Store cCnt defs) (idx : Nat) :
  Coh cCnt defs E S Γ → idx < E.length →
  ValueTyp cCnt defs E[idx]! Γ[idx]! S := by
    intro h
    induction h generalizing idx <;> grind

lemma coh_set (E : Environment) (Γ : Ctx) (S : Store cCnt defs) (idx : Nat) (v : Value) :
  Coh cCnt defs E S Γ → idx < E.length →
  ValueTyp cCnt defs v Γ[idx]! S →
  Coh cCnt defs (E.set idx v) S Γ := by
    intro h
    induction h generalizing idx
    { grind }
    by_cases h0 : ∃ idx₁, idx = idx₁ + 1
    { grind [Coh] }
    simp only [Nat.exists_eq_add_one, not_lt, Nat.le_zero_eq] at h0
    rw [h0, List.set_cons_zero]
    grind [Coh]


lemma coh_mono (E : Environment) (Γ : Ctx) (S : Store cCnt defs) :
  Coh cCnt defs E S Γ → Coh cCnt defs (E.drop n) S (Γ.drop n) := by
    intro h
    induction h generalizing n
    { grind [Coh] }
    have cons_append (α : Type) (li : List α) (x : α) :
      [x] ++ li = x :: li := by grind
    have (α : Type) (li : List α) (x : α) : n > 0 → ([x] ++ li).drop n = li.drop (n - 1) := by
      rw [List.drop_append]
      intro hn
      rw [List.drop_cons]
      { grind [List.take] }
      grind
    by_cases n = 0
    { grind [Coh] }
    rw [←cons_append, this]
    { grind [Coh] }
    grind

lemma drop_suffix_prepend {α : Type} (Γ₁ Γ₂ : List α) (n : Nat)
    (hn : n ≤ Γ₂.length) :
    List.drop (List.length (Γ₁ ++ Γ₂) - n) (Γ₁ ++ Γ₂) =
    List.drop (List.length Γ₂ - n) Γ₂ := by
  rw [List.drop_append]
  have h1 : List.drop (List.length (Γ₁ ++ Γ₂) - n) Γ₁ = [] := by
    rw [List.drop_eq_nil_iff]; simp; omega
  rw [h1, List.nil_append]
  congr 1; simp; omega

lemma jcoh_ext (J : JStackCtx cCnt defs) (Γ Γ₁ : Ctx) :
    JCoh cCnt defs J Γ Δ → JCoh cCnt defs J (Γ₁ ++ Γ) Δ := by
    intro h
    unhygienic induction h generalizing Γ₁
    { exact JCoh.JCohEmp }
    rename_i Γ₂
    have hdrop := drop_suffix_prepend Γ₁ Γ₂ n a
    apply JCoh.JCohLoop
    { simp; omega }
    { rw [hdrop]; assumption }
    { rw [hdrop]; assumption }

lemma jcoh_sub (J : JStackCtx cCnt defs) (Γ : Ctx) :
    JCoh cCnt defs J Γ Δ → ctx_limit n Δ →
    JCoh cCnt defs J (Γ.drop (Γ.length - n)) Δ := by
    intro h hc
    unhygienic induction h generalizing n
    { exact JCoh.JCohEmp }
    apply JCoh.JCohLoop
    { grind [ctx_limit] }
    { simp at *
      grind [ctx_limit] }
    stop sorry
    /- JCoh should not be related to a specific method. -/

lemma jcoh_drop (J : JStackCtx cCnt defs) (Γ : Ctx) (l : Nat) :
    JCoh cCnt defs J Γ Δ →
    JCoh cCnt defs (J.drop (l + 1))
      (Γ.drop (Γ.length - J[l]!.1)) (Δ.drop (l + 1)) := by
    intro hj
    unhygienic induction l generalizing J Δ Γ
    { cases hj
      { grind [JCoh] }
      grind }
    unhygienic cases hj
    { grind [JCoh] }
    simp only [List.drop_succ_cons]
    apply a
    have : Γ = Γ.take (Γ.length - n_1) ++ (Γ.drop (Γ.length - n_1)) := by
      clear a a_2
      exact List.eq_take_drop Γ _
    rw [this]
    apply jcoh_ext
    apply a_2

lemma jcoh_ctx :
  JCoh cCnt defs J Γ Δ → ctx_limit Γ.length Δ := by
    intro hj
    induction hj
    { grind [ctx_limit] }
    rw [ctx_limit]
    grind
