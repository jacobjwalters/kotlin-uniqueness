import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat

inductive τ
| Nat
| Bool
deriving Repr

inductive Value
| True
| False
| Nat (n : Nat)
deriving Inhabited, Repr

structure BinOp where
  run : Value → Value → Value
  arg1 : τ
  arg2 : τ
  out : τ
instance : Repr BinOp where
  reprPrec op _ := f!"
    BinOp(
      run := <function>,
      arg1 := {repr op.arg1},
      arg2 := {repr op.arg2},
      out := {repr op.out})"

structure UnOp where
  run : Value → Value
  arg : τ
  out : τ
instance : Repr UnOp where
  reprPrec op _ := f!"
    UnOp(
      run := <function>,
      arg := {repr op.arg},
      out := {repr op.out})"

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
| While (c : Expr) (body : Stmt)
--| Break
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
| UnOp (arg : Expr) (type : τ) (out : τ) (run : Value → Value)  :
  ExprType Γ₁ arg type →
  ExprType Γ₁ (.UnOp arg ⟨run, type, out⟩) out
| BinOp (arg₁ arg₂ : Expr) (type₁ : τ) (type₂ : τ) (out : τ) (run : Value → Value → Value) :
  ExprType Γ₁ arg₁ type₁ →
  ExprType Γ₁ arg₂ type₂ →
  ExprType Γ₁ (.BinOp arg₁ arg₂ ⟨run, type₁, type₂, out⟩) out


inductive StmtType : Γ → Stmt → Γ → Prop
| VarDecl (e : Expr) (type : τ) (x : VarName) : ExprType Γ₁ e type →
  StmtType Γ₁ (.Decl x type e) (⟨x, type⟩ :: Γ₁)
| VarAssign (x : VarName) (e : Expr) (type : τ) : ExprType Γ₁ e type → (Γ₁(x) = type) →
  StmtType Γ₁ (.Assign x e) Γ₁
| Seq (s₁ s₂ : Stmt) : StmtType Γ₁ s₁ Γ₂ → StmtType Γ₂ s₂ Γ₃ →
  StmtType Γ₁ (s₁; s₂) Γ₃
| If (e : Expr) (s₁ s₂ : Stmt) : ExprType Γ₁ e .Bool → StmtType Γ₁ s₁ Γ₂ → StmtType Γ₁ s₂ Γ₃ →
  StmtType Γ₁ (.If e s₁ s₂) Γ₁
| While (c : Expr) (s : Stmt) : ExprType Γ₁ c .Bool → StmtType Γ₁ s Γ₂ →
  StmtType Γ₁ (.While c s) Γ₁
/-| Break :
  StmtType Γ₁ .Break Γ₂
-/

end Types

section TypeProperties

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
    { unhygienic cases hs
      exists [] }
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
    { by_cases hemp : Γ₂ = []
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
      grind [StmtType] }
    by_cases hemp : Γ₂ = []
    { simp only [hemp] at *
      unhygienic cases hs
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      apply StmtType.While (Γ₂ := g1 ++ Γ₁ ++ Γ₃)
      { apply ExprExtension
        apply a }
      apply body_ih
      rw [hg1] at a_1
      exact a_1 }
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
    { by_cases hemp : Δ = []
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
      grind [StmtType] }
    by_cases hemp : Δ = []
    { simp only [hemp] at *
      unhygienic cases hs
      rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
      apply StmtType.While (Γ₂ := g1 ++ Γ₂)
      { apply ExprPermutation _ _ c .Bool heq
        grind }
      apply body_ih Γ₁ Γ₂ g1
      { grind }
      rw [hg1] at a_1
      exact a_1 }
    have : Δ ++ Γ₁ ≠ Γ₁ := by
      intro eq
      have : (Δ ++ Γ₁).length > Γ₁.length := by
        simp
        grind
      grind
    grind [StmtType]

end TypeProperties

def liftValue : Value → Expr
| .True => .True
| .False => .False
| .Nat (n : Nat) => .Nat n

def ValueType : Value → τ → Prop
| .True, .Bool => True
| .False, .Bool => True
| .Nat _, .Nat => True
| _, _ => False

inductive Control
| sourceExpr (e : Expr)
| sourceStmt (s : Stmt)
| value (v : Value)
| skip

abbrev Map (val : Type) := Finmap (fun _ : VarName ↦ val)

abbrev Environment := List (Map Value)

inductive Cont
| ifCondK (s₁ s₂ : Stmt)
| jumpK (l : Nat)
| declK (x : VarName) (type : τ)
| assignK (x : VarName)
| seqK (s : Stmt)
| binopLK (op : BinOp) (e₂ : Expr)
| binopRK (op : BinOp) (v : Value)
| unopK (op : UnOp)
| loopK (c : Expr) (s : Stmt)

abbrev CEK := Control × Environment × List Cont

notation E "("x")!" => Option.get! (Finmap.lookup x (List.getD E 0 ∅ : Map Value) : Option Value)

def popK (K : List Cont) (l : Nat) : List Cont :=
  match K with
  | .jumpK l₁ :: li => if l = l₁ then li else popK li l
  | _ :: li => popK li l
  | [] => panic! "popK from an empty List"

def insert_first (key : VarName) (value : Value) : Environment → Environment
| fst :: li => (Finmap.insert key value fst) :: li
| [] => panic! "Insertion into empty environment"

def modify_first (key : VarName) (value : Value) : Environment → Environment
| fst :: li => (Finmap.insert key value (Finmap.erase key fst)) :: li
| [] => panic! "Insertion into empty environment"


inductive Eval : CEK → CEK → Prop
-- # Expr
| Val (v : Value) :
  Eval
    ⟨.sourceExpr (liftValue v), E, K⟩
    ⟨.value v, E, K⟩
| Var (v : Value) (x : VarName) :
  Eval
    ⟨.sourceExpr (.Var x), E, K⟩
    ⟨.value (E(x)!), E, K⟩
| If (e : Expr) (s₁ s₂ : Stmt) :
  Eval
    ⟨.sourceStmt (.If e s₁ s₂), E, K⟩
    ⟨.sourceExpr e, E, (.ifCondK s₁ s₂) :: K⟩
| VarDecl (x : VarName) (type : τ) (e : Expr) :
  Eval
    ⟨.sourceStmt (.Decl x type e), E, K⟩
    ⟨.sourceExpr e, E, (.declK x type) :: K⟩
| Assign (x : VarName) (e : Expr) :
  Eval
    ⟨.sourceStmt (.Assign x e), E, K⟩
    ⟨.sourceExpr e, E, (.assignK x) :: K⟩
| Seq (s₁ s₂ : Stmt) :
  Eval
    ⟨.sourceStmt (.Seq s₁ s₂), E, K⟩
    ⟨.sourceStmt s₁, E, (.seqK s₂) :: K⟩
| BinOp (e₁ e₂ : Expr) (op : BinOp) :
  Eval
    ⟨.sourceExpr (.BinOp e₁ e₂ op), E, K⟩
    ⟨.sourceExpr e₁, E, (.binopLK op e₂) :: K⟩
| UnOp (e : Expr) (op : UnOp) :
  Eval
    ⟨.sourceExpr (.UnOp e op), E, K⟩
    ⟨.sourceExpr e, E, (.unopK op) :: K⟩
| While (c : Expr) (body : Stmt) :
  Eval
    ⟨.sourceStmt (.While c body), E, K⟩
    ⟨.sourceExpr c, ∅ :: E, (.loopK c body) :: (.jumpK E.length) :: K⟩
/-| Break  :
  Eval
    ⟨.sourceStmt (.Break), E, K⟩
    ⟨.skip, E.drop 1, popK K (E.length - 1)⟩
-/
-- # Cont
| IfTrue (s₁ s₂ : Stmt) :
  Eval
    ⟨.value .True, E, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceStmt s₁, ∅ :: E, (.jumpK E.length) :: K⟩
| IfFalse (s₁ s₂ : Stmt) :
  Eval
    ⟨.value .False, E, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceStmt s₂, ∅ :: E, (.jumpK E.length) :: K⟩
| ScopeDone (l : Nat) :
  Eval
    ⟨.skip, E, .jumpK l :: K⟩
    ⟨.skip, E.drop (E.length - l), K⟩
| VarDeclDone (x : VarName) (type : τ) (v : Value) :
  Eval
    ⟨.value v, E, .declK x type :: K⟩
    ⟨.skip, insert_first x v E, K⟩
| AssignDone (x : VarName) (v : Value) :
  Eval
    ⟨.value v, E, .assignK x :: K⟩
    ⟨.skip, modify_first x v E, K⟩
| SeqDone (s₂ : Stmt) :
  Eval
    ⟨.skip, E, .seqK s₂ :: K⟩
    ⟨.sourceStmt s₂, E, K⟩
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Expr) :
  Eval
    ⟨.value v₁, E, .binopLK op e₂ :: K⟩
    ⟨.sourceExpr e₂, E, .binopRK op v₁ :: K⟩
| BinOpR (op : BinOp) (v₁ : Value) (v₂ : Value) :
  Eval
    ⟨.value v₂, E, .binopRK op v₁ :: K⟩
    ⟨.value (op.run v₁ v₂), E, K⟩
| UnOpDone (op : UnOp) (v : Value) :
  Eval
    ⟨.value v, E, .unopK op :: K⟩
    ⟨.value (op.run v), E, K⟩
| LoopTrue (body : Stmt) (c : Expr) :
  Eval
    ⟨.value .True, E, .loopK c body :: K⟩
    ⟨.sourceStmt body, E, .loopK c body :: K⟩
| LoopFalse (body : Stmt) (c : Expr) :
  Eval
    ⟨.value .False, E, .loopK c body :: K⟩
    ⟨.skip, E, K⟩
| LoopCont (body : Stmt) (c : Expr) :
  Eval
    ⟨.skip, E, .loopK c body :: K⟩
    ⟨.sourceExpr c, ∅ :: E.drop 1, .loopK c body :: K⟩

def init_state (s : Stmt) : CEK := ⟨.sourceStmt s, [], []⟩

def terminal_state (E : Environment) : CEK := ⟨.skip, E, []⟩

-- # Statement Continuations

def List.gcat (inp : List Γ) : Γ := inp.foldl (· ++ ·) []

inductive ContStmtType : List Γ → List Cont → Prop
| HaltK (Γ₁ : List Γ) :
  ContStmtType Γ₁ []
| JumpK (Γ₁ : List Γ) (l : Nat) :
  ContStmtType (Γ₁.drop (Γ₁.length - l)) K →
  ContStmtType Γ₁ (.jumpK l :: K)
| SeqK (Γ₁ : List Γ) (Γ₂ : List Γ) (s : Stmt) :
  StmtType Γ₁.gcat s Γ₂.gcat →
  ContStmtType Γ₂ K →
  ContStmtType Γ₁ (.seqK s :: K)
| LoopBodyK (Γ₁ : List Γ) (Γ₂ : List Γ) (body : Stmt) (c : Expr) :
  ExprType Γ₁.gcat c .Bool →
  StmtType Γ₁.gcat body Γ₂.gcat →
  ContStmtType Γ₁ K →
  ContStmtType Γ₁ (.loopK c body :: K)

-- # Expression Continuations

inductive ContExprType : List Γ → List Cont → τ → Prop
-- check with the loop framing
| IfCondK (s₁ : Stmt) (s₂ : Stmt) (Γ₁ Γ₂ Γ₃ : List Γ) :
  StmtType Γ₁.gcat s₁ Γ₂.gcat →
  StmtType Γ₁.gcat s₂ Γ₃.gcat →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.ifCondK s₁ s₂ :: K) .Bool
| DeclK (x : VarName) (type : τ) (Γ₁ : Γ) (Γ₂ : List Γ) :
  ContStmtType ((⟨x, type⟩ :: Γ₁) :: Γ₂) K →
  ContExprType (Γ₁ :: Γ₂) (.declK x type :: K) type
| AssignK (x : VarName) (type : τ) (Γ₁ : List Γ) :
  (Γ₁.gcat(x) = type) →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.assignK x :: K) type
| BinOpLK (Γ₁ : List Γ) (op : BinOp) (e₂ : Expr) :
  ExprType Γ₁.gcat e₂ op.arg2 →
  ContExprType Γ₁ K op.out →
  ContExprType Γ₁ (.binopLK op e₂ :: K) op.arg1
| BinOpRK (Γ₁ : List Γ) (op : BinOp) (v₁ : Value) :
  ValueType v₁ op.arg1 →
  ContExprType Γ₁ K op.out →
  ContExprType Γ₁ (.binopRK op v₁ :: K) op.arg2
| UnOpK (Γ₁ : List Γ) (op : UnOp) :
  ContExprType Γ₁ K op.out →
  ContExprType Γ₁ (.unopK op :: K) op.arg
| LoopCondK (Γ₁ : List Γ) (Γ₂ : List Γ) (body : Stmt) (c : Expr) :
  ExprType Γ₁.gcat c .Bool →
  StmtType Γ₁.gcat body Γ₂.gcat →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.loopK c body :: K) .Bool
