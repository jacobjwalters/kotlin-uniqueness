import Mathlib.Tactic.Basic

abbrev VarName := Nat

inductive τ
| Nat
| Bool
deriving Repr

inductive BinOp
| Sub
| Add
| NatEq
| BoolEq
deriving Repr

inductive UnOp
| IsZero
deriving Repr

inductive Expr
| Var (x : VarName)
| True
| False
| Nat (n : Nat)
| BinOp (arg₁ : Expr) (arg₂ : Expr) (op : BinOp)
| UnOp (arg : Expr) (op : UnOp)
deriving Repr

inductive Stmt
| Decl (x : VarName) (type : τ) (e : Expr)
| Assign (x : VarName) (e : Expr)
| Seq (s₁ : Stmt) (s₂ : Stmt)
| If (e : Expr) (s₁ : Stmt) (s₂ : Stmt)
deriving Repr

notation:100 s₁:100 ";" s₂:101 => Stmt.Seq s₁ s₂
notation x "::=" exp => Stmt.Assign x exp

abbrev Γ := List (VarName × τ)
notation Γ₁ "("x")" "=" type => List.find? (fun ⟨name, _⟩ => name = x) Γ₁ = Option.some ⟨x, type⟩

section Types

inductive ExprType : Γ → Expr → τ → Prop
| TrueConst : ExprType Γ₁ .True .Bool
| FalseConst : ExprType Γ₁ .False .Bool
| NatConst (n : Nat) : ExprType Γ₁ (.Nat n) .Nat
| VarAccess (x : VarName) (type : τ) :
  (Γ₁(x) = type) →
  ExprType Γ₁ (.Var x) type
| IsZero (arg : Expr) :
  ExprType Γ₁ arg .Nat →
  ExprType Γ₁ (.UnOp arg .IsZero) .Bool
| Sub (arg₁ arg₂ : Expr) :
  ExprType Γ₁ arg₁ .Nat →
  ExprType Γ₁ arg₂ .Nat →
  ExprType Γ₁ (.BinOp arg₁ arg₂ .Sub) .Nat
| Add (arg₁ arg₂ : Expr) :
  ExprType Γ₁ arg₁ .Nat →
  ExprType Γ₁ arg₂ .Nat →
  ExprType Γ₁ (.BinOp arg₁ arg₂ .Add) .Nat
| NatEq (arg₁ arg₂ : Expr) :
  ExprType Γ₁ arg₁ .Nat →
  ExprType Γ₁ arg₂ .Nat →
  ExprType Γ₁ (.BinOp arg₁ arg₂ .NatEq) .Bool
| BoolEq (arg₁ arg₂ : Expr) :
  ExprType Γ₁ arg₁ .Bool →
  ExprType Γ₁ arg₂ .Bool →
  ExprType Γ₁ (.BinOp arg₁ arg₂ .BoolEq) .Bool


inductive StmtType : Γ → Stmt → Γ → Prop
| VarDecl (e : Expr) (type : τ) (x : VarName) : ExprType Γ₁ e type →
  StmtType Γ₁ (.Decl x type e) (⟨x, type⟩ :: Γ₁)
| VarAssign (x : VarName) (e : Expr) (type : τ) : ExprType Γ₁ e type → (Γ₁(x) = type) →
  StmtType Γ₁ (.Assign x e) Γ₁
| Seq (s₁ s₂ : Stmt) : StmtType Γ₁ s₁ Γ₂ → StmtType Γ₂ s₂ Γ₃ →
  StmtType Γ₁ (s₁; s₂) Γ₃
| If (e : Expr) (s₁ s₂ : Stmt) : ExprType Γ₁ e .Bool → StmtType Γ₁ s₁ Γ₂ → StmtType Γ₁ s₂ Γ₃ →
  StmtType Γ₁ (.If e s₁ s₂) Γ₁

end Types

section Properties

theorem StmtDet (Γ₁ Γ₂ Γ₃ : Γ) (s : Stmt) :
  StmtType Γ₁ s Γ₂ → StmtType Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    induction s generalizing Γ₁ Γ₂ Γ₃ <;> grind [StmtType, Stmt, ExprType, Expr]

theorem ExprExtension (Γ₁ Γ₂ : Γ) (e : Expr) (type : τ) :
  ExprType Γ₁ e type → ExprType (Γ₁ ++ Γ₂) e type := by
    intro hg
    unhygienic induction e generalizing type <;> try grind [Expr, ExprType]

theorem ExprPermutation (Γ₁ Γ₂ : Γ) (e : Expr) (type : τ) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  ExprType Γ₁ e type → ExprType Γ₂ e type := by
    intro hg
    induction e generalizing type <;> try grind [Expr, ExprType]

lemma StmtMono (Γ₁ Γ₂ : Γ) (s : Stmt) :
  StmtType Γ₁ s Γ₂ → ∃ Γ₃, Γ₂ = Γ₃ ++ Γ₁ := by
    intro hs
    unhygienic induction s generalizing Γ₁ Γ₂
    { unhygienic cases hs
      exists [⟨x, type⟩] }
    { unhygienic cases hs
      exists [] }
    { unhygienic cases hs
      rcases s₁_ih Γ₁ Γ₂_1 a with ⟨g1, hg1⟩
      rcases s₂_ih Γ₂_1 Γ₂ a_1 with ⟨g2, hg2⟩
      exists g2 ++ g1
      grind }
    unhygienic cases hs
    exists []

lemma StmtDecl (type : τ) : StmtType Γ₁ (Stmt.Decl x type e) Γ₂ → Γ₂ = ⟨x, type⟩ :: Γ₁ := by
  grind [StmtType]

theorem StmtExtension (Γ₁ Γ₂ Γ₃ : Γ) (s : Stmt) :
  StmtType Γ₁ s (Γ₂ ++ Γ₁) → StmtType (Γ₁ ++ Γ₃) s (Γ₂ ++ Γ₁ ++ Γ₃) := by
    intro hs
    unhygienic induction s generalizing Γ₁ Γ₂ Γ₃
    { have obt := StmtDecl type hs
      have : Γ₂ = [⟨x, type⟩] := by
        induction Γ₁
        { grind }
        rw [List.append_eq_cons_iff] at obt
        unhygienic cases obt
        { grind }
        rcases h with ⟨as, has1, has2⟩
        rw [eq_comm, List.append_left_eq_self] at has2
        grind
      rw [List.append_assoc]
      have : ExprType (Γ₁ ++ Γ₃) e type := by
        rw [obt] at hs
        cases hs
        clear obt this
        induction e generalizing type <;> grind [Stmt, StmtType, ExprType, BinOp, UnOp]
      grind [StmtType] }
    { by_cases hemp : Γ₂ = []
      { simp only [hemp] at *
        unhygienic cases hs
        apply StmtType.VarAssign
        { apply ExprExtension
          apply a }
        grind }
      have : Γ₂ ++ Γ₁ ≠ Γ₁ := by
        intro eq
        have : (Γ₂ ++ Γ₁).length > Γ₁.length := by
          simp
          grind
        grind
      grind [StmtType] }
    { unhygienic cases hs
      rcases StmtMono _ _ _ a with ⟨g, hg⟩
      apply StmtType.Seq
      { apply s₁_ih
        rw [hg] at a
        apply a }
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      rw [hg] at hg1
      have : Γ₂ = g1 ++ g := by
        rw [←List.append_assoc] at hg1
        apply List.append_cancel_right
        apply hg1
      grind }
    by_cases hemp : Γ₂ = []
    { simp only [hemp] at *
      unhygienic cases hs
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      rcases StmtMono _ _ _ a_2 with ⟨g2, hg2⟩
      apply StmtType.If (Γ₂ := g1 ++ Γ₁ ++ Γ₃) (Γ₃ := g2 ++ Γ₁ ++ Γ₃)
      { apply ExprExtension
        apply a }
      { apply s₁_ih
        rw [hg1] at a_1
        exact a_1 }
      apply s₂_ih
      rw [hg2] at a_2
      exact a_2 }
    have : Γ₂ ++ Γ₁ ≠ Γ₁ := by
      intro eq
      have : (Γ₂ ++ Γ₁).length > Γ₁.length := by
        simp
        grind
      grind
    grind [StmtType]

theorem StmtPermutation (Γ₁ Γ₂ Δ : Γ) (s : Stmt) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  StmtType Γ₁ s (Δ ++ Γ₁) → StmtType Γ₂ s (Δ ++ Γ₂) := by
    intro heq hs
    unhygienic induction s generalizing Γ₁ Γ₂ Δ
    { have := StmtDecl type hs
      have : Δ = [⟨x, type⟩] := by
        clear heq hs
        induction Γ₁
        { grind }
        rw [List.append_eq_cons_iff] at this
        unhygienic cases this
        { grind }
        rcases h with ⟨as, has1, has2⟩
        rw [eq_comm, List.append_left_eq_self] at has2
        grind
      grind [ExprPermutation, StmtType] }
    { by_cases hemp : Δ = []
      { simp only [hemp] at *
        unhygienic cases hs
        apply StmtType.VarAssign
        { apply ExprPermutation
          { apply heq }
          apply a }
        grind }
      have : Δ ++ Γ₁ ≠ Γ₁ := by
        intro eq
        have : (Δ ++ Γ₁).length > Γ₁.length := by
          simp
          grind
        grind
      grind [StmtType] }
    { unhygienic cases hs
      rcases StmtMono _ _ _ a with ⟨g, hg⟩
      apply StmtType.Seq
      { apply s₁_ih Γ₁ Γ₂ g
        { grind }
        rw [hg] at a
        apply a }
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      rw [hg] at hg1
      have : Δ = g1 ++ g := by
        rw [←List.append_assoc] at hg1
        apply List.append_cancel_right
        apply hg1
      rw [this, List.append_assoc]
      apply s₂_ih (g ++ Γ₁) (g ++ Γ₂)
      { intro tp x
        constructor <;> intro h <;>
        { clear s₁_ih s₂_ih
          simp [List.find?_append] at *
          grind } }
      grind }
    by_cases hemp : Δ = []
    { simp only [hemp] at *
      unhygienic cases hs
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      rcases StmtMono _ _ _ a_2 with ⟨g2, hg2⟩
      apply StmtType.If (Γ₂ := g1 ++ Γ₂) (Γ₃ := g2 ++ Γ₂)
      { apply ExprPermutation _ _ e .Bool heq
        grind }
      { apply s₁_ih Γ₁ Γ₂ g1
        { grind }
        rw [hg1] at a_1
        exact a_1 }
      apply s₂_ih Γ₁ Γ₂ g2
      { grind }
      rw [hg2] at a_2
      exact a_2 }
    have : Δ ++ Γ₁ ≠ Γ₁ := by
      intro eq
      have : (Δ ++ Γ₁).length > Γ₁.length := by
        simp
        grind
      grind
    grind [StmtType]

end Properties
