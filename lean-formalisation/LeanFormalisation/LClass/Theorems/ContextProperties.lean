import Batteries.Tactic.Init
import Mathlib.Data.Nat.Basic

import LeanFormalisation.LClass.LClassDefs
import LeanFormalisation.LClass.Theorems.TypeProperties

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

lemma map_fresh_addr {val : Type} (m : Map val) : ∃ n : Addr, n ∉ m := by
  -- Treat the keys as Finset Nat (Addr = Nat definitionally) to access Nat instances
  let ks : Finset Nat := m.keys
  use ks.sup id + 1
  intro h
  have hk : ks.sup id + 1 ∈ ks := Finmap.mem_keys.mpr h
  have hle := Finset.le_sup (f := id) hk
  simp only [id_eq] at hle
  omega

lemma entries_insert_ne (S : Store cCnt defs) (a : Addr) (s : Object cCnt defs)
    (obj : Σ _ : Addr, Object cCnt defs) :
    obj ∈ (S.insert a s).entries → obj.1 ≠ a → obj ∈ S.entries := by
  intro hobj hne
  have hmem := Finmap.mem_lookup_iff.mpr hobj
  rw [Finmap.lookup_insert_of_ne S hne] at hmem
  simpa [Sigma.eta] using Finmap.mem_lookup_iff.mp hmem

lemma coh_ext (E : Environment) (Γ : Ctx) (S : Store cCnt defs) :
  Coh cCnt defs E S Γ →
  a ∉ S →
  Coh cCnt defs E (S.insert a s) Γ := by
    intro hc ha
    induction hc <;> grind [Coh, value_typ_ext]

lemma store_ext (S : Store cCnt defs) (s : Object cCnt defs) :
  S_ok cCnt defs S →
  a ∉ S →
  (∀ i, ValueTyp cCnt defs (s.values i) (defs.fieldsTy s.cls i) S) →
  S_ok cCnt defs (S.insert a s) := by
    intro hs ha hv
    rw [S_ok] at *
    intro obj hobj
    have mem := Finmap.mem_lookup_iff.mpr hobj
    by_cases heq : a = obj.fst
    { apply ValueTyp.Cls
      { rw [heq, Finmap.lookup_insert] }
      { intro i
        apply value_typ_ext
        { apply hv i }
        exact ha }
      rw [heq, Finmap.lookup_insert] at mem
      grind }
    rw [Finmap.lookup_insert_of_ne] at mem
    { simp only [Option.mem_def] at mem
      apply ValueTyp.Cls
      { rw [Finmap.lookup_insert_of_ne]
        { exact mem }
        grind }
      { intro i
        apply value_typ_ext
        { unhygienic cases hs obj (by
            apply Finmap.mem_lookup_iff.mp
            grind)
          have eq := Fin.eq_of_val_eq a_4
          subst eq
          rw [mem] at a_2
          simp at a_2
          have eq1 : vls = obj.2.values := by grind
          subst eq1
          grind }
        grind }
      { grind } }
    grind

lemma coh_iff (E : Environment) (Γ : Ctx) (S : Store cCnt defs) :
  Coh cCnt defs E S Γ ↔
  (E.length = Γ.length ∧ ∀ i < E.length, ValueTyp cCnt defs E[i]! Γ[i]! S) := by
    constructor
    { intro hc
      induction hc <;> grind }
    intro hc
    induction E generalizing Γ
    { have gemp : Γ = [] := by grind
      rw [gemp]
      exact Coh.CohEmp }
    have : ∃ g G', Γ = g :: G' := by cases Γ <;> grind
    rcases this with ⟨g, G', hg⟩
    rw [hg]
    rename_i tail_ih
    apply Coh.CohBind
    { apply tail_ih
      constructor
      { grind }
      intro i hi
      have lm := hc.2 (i + 1) (by simp; omega)
      grind }
    rw [hg] at hc
    have lmc := hc.2 0 (by simp)
    grind

lemma cont_type_ext (tg : Tag) (res : ContTypeRes tg) :
  ContType cCnt defs tg Δ Γ S K res →
  a ∉ S →
  ContType cCnt defs tg Δ Γ (S.insert a s) K res := by
    intro hc ha
    unhygienic induction hc
    all_goals try solve_by_elim
    { apply ContType.FieldK <;> solve_by_elim }
    { apply ContType.IfCondK <;> solve_by_elim }
    { apply ContType.LoopContK Γ₁ e c cnts <;> try solve_by_elim
      { intros
        apply a_ih <;> try solve_by_elim }
      { intros
        apply a_ih_1 <;> try solve_by_elim } }
    { apply ContType.BreakRestoreK Γ₁ cnts (Δ := Δ_1) (Δ₁ := Δ₁) <;> grind }
    { apply ContType.ScopeExitK _ _ _ cnts <;> try solve_by_elim
      { grind }
      { grind } }
    { apply ContType.ReturnRestoreK (cnts := cnts) <;> try solve_by_elim
      apply coh_ext <;> try solve_by_elim
      { intros
        apply a_ih <;> solve_by_elim }
      { intros
        apply a_ih_1 <;> solve_by_elim } }
    { apply ContType.CallRestoreK (cnts := cnts) <;> try solve_by_elim
      apply coh_ext <;> solve_by_elim
      { intros
        apply a_ih <;> solve_by_elim }
      { intros
        apply a_ih_1 <;> solve_by_elim } }
    { apply ContType.ArgK <;> try solve_by_elim
      intros
      apply value_typ_ext <;> grind }
    { apply ContType.NewK <;> try solve_by_elim
      intros
      apply value_typ_ext <;> grind }
    { apply ContType.ScopeBodyK (cnts := cnts) <;> try solve_by_elim
      { intros
        apply a_ih <;> solve_by_elim }
      { intros
        apply a_ih_1 <;> solve_by_elim } }


lemma cont_gen_method (type : Ty) :
  (∃ E₁ J₁, K = Cont.returnRestoreK E₁ J₁ :: K') →
  ContType cCnt defs Tag.Expr Δ₁ Γ₁ S K (ContTypeRes.Expr type) →
  ContType cCnt defs Tag.Expr Δ₂ Γ₂ S K (ContTypeRes.Expr type) := by
    intro hj hc
    rcases hj with ⟨E, J, hj⟩
    subst hj
    unhygienic cases hc
    apply ContType.ReturnRestoreK <;> solve_by_elim

lemma cont_gen_loop (Γ₁ Γ₂ : Ctx) :
  (K = Cont.breakRestoreK n1 J₁ :: K') →
  n1 ≤ Γ₁.length → n1 ≤ Γ₂.length →
  (Γ₁.drop (Γ₁.length - n1)) = Γ₂.drop (Γ₂.length - n1) →
  ContType cCnt defs Tag.Expr Δ₁ Γ₁ S K (ContTypeRes.Expr Ty.unit) →
  ContType cCnt defs Tag.Expr Δ₂ Γ₂ S K (ContTypeRes.Expr Ty.unit) := by
    intro hj eq1 eq2 eq hc
    subst hj
    unhygienic cases hc
    apply ContType.BreakRestoreK <;> try solve_by_elim
    { grind }
    { unhygienic intros
      apply cont_gen_method <;> try solve_by_elim }
    grind
