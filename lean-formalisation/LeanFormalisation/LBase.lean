import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat

inductive τ
| Nat
| Bool
| Unit
deriving Repr


inductive Value
| True
| False
| Nat (n : Nat)
| Unit
deriving Inhabited, Repr

inductive BinOp
| Add
| Sub
| NatEq
| BoolEq

structure BinOpArgs where
  arg₁ : τ
  arg₂ : τ
  out : τ

inductive UnOp
| IsZero

structure UnOpArgs where
  arg : τ
  out : τ

def BinOp.args : BinOp → BinOpArgs
| .Add => ⟨.Nat, .Nat, .Nat⟩
| .Sub => ⟨.Nat, .Nat, .Nat⟩
| .NatEq => ⟨.Nat, .Nat, .Bool⟩
| .BoolEq => ⟨.Bool, .Bool, .Bool⟩

def BinOp.run : BinOp → Value → Value → Value
| .Add => fun x y =>
  match x, y with
  | .Nat n, .Nat m => .Nat (n + m)
  | _, _ => panic! "Not implemented"
| .Sub => fun x y =>
  match x, y with
  | .Nat n, .Nat m => .Nat (n - m)
  | _, _ => panic! "Not implemented"
| .NatEq => fun x y =>
  match x, y with
  | .Nat n, .Nat m => if n = m then .True else .False
  | _, _ => panic! "Not implemented"
| .BoolEq => fun x y =>
  match x, y with
  | .True, .True => .True
  | .False, .False => .True
  | _, _ => panic! "Not implemented"

def UnOp.args : UnOp → UnOpArgs
| .IsZero => ⟨.Nat, .Bool⟩

def UnOp.run : UnOp → Value → Value
| .IsZero => fun x =>
  match x with
  | .Nat 0 => .True
  | .Nat _ => .False
  | _ => panic! "Not implemented"

mutual
inductive Expr
| Var (x : VarName)
| True
| False
| Nat (n : Nat)
| Unit
| BinOp (arg₁ : Expr) (arg₂ : Expr) (op : BinOp)
| UnOp (arg : Expr) (op : UnOp)
| If (cond : Expr) (e₁ : Expr) (e₂ : Expr)
| While (cond : Expr) (body : Expr)
| Break
| Scope (s : Stmt) (res : Expr)

inductive Stmt
| Decl (type : τ) (e : Expr)
| Assign (x : VarName) (e : Expr)
| Seq (s₁ : Stmt) (s₂ : Stmt)
| Do (e : Expr)
end

notation:100 s₁:100 ";" s₂:101 => Stmt.Seq s₁ s₂
notation x "::=" exp => Stmt.Assign x exp
#check List.get
abbrev Γ := List τ
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[List.length Γ₁ - 1 - x]? = Option.some type

section Types
mutual
inductive ExprType : Γ → Expr → τ → Prop
| TrueConst :
  ExprType Γ₁ .True .Bool
| FalseConst :
  ExprType Γ₁ .False .Bool
| NatConst (n : Nat) :
  ExprType Γ₁ (.Nat n) .Nat
| UnitConst :
  ExprType Γ₁ (.Unit) .Unit
| VarAccess (x : VarName) (type : τ) :
  (Γ₁(x) = type) →
  ExprType Γ₁ (.Var x) type
| UnOp (arg : Expr) (op : UnOp) :
  ExprType Γ₁ arg op.args.1 →
  ExprType Γ₁ (.UnOp arg op) op.args.2
| BinOp (arg₁ arg₂ : Expr) (op : BinOp) :
  ExprType Γ₁ arg₁ op.args.1 →
  ExprType Γ₁ arg₂ op.args.2 →
  ExprType Γ₁ (.BinOp arg₁ arg₂ op) op.args.3
| IfExpr (cond : Expr) (e₁ : Expr) (e₂ : Expr) (type : τ) :
  ExprType Γ₁ cond .Bool →
  ExprType Γ₁ e₁ type →
  ExprType Γ₁ e₂ type →
  ExprType Γ₁ (.If cond e₁ e₂) type
| WhileExpr (cond : Expr) (body : Expr) :
  ExprType Γ₁ cond .Bool →
  ExprType Γ₁ body .Unit →
  ExprType Γ₁ (.While cond body) .Unit
| BreakExpr (type : τ) :
  ExprType Γ₁ .Break .Unit
| ScopeExpr (s : Stmt) (e : Expr) (type : τ) :
  StmtType Γ₁ s Γ₂ →
  ExprType Γ₂ e type →
  ExprType Γ₁ (.Scope s e) type

inductive StmtType : Γ → Stmt → Γ → Prop
| VarDecl (e : Expr) (type : τ) :
  ExprType Γ₁ e type →
  StmtType Γ₁ (.Decl type e) (type :: Γ₁)
| VarAssign (x : VarName) (e : Expr) (type : τ) :
  ExprType Γ₁ e type → (Γ₁(x) = type) →
  StmtType Γ₁ (.Assign x e) Γ₁
| Seq (s₁ s₂ : Stmt) :
  StmtType Γ₁ s₁ Γ₂ →
  StmtType Γ₂ s₂ Γ₃ →
  StmtType Γ₁ (s₁; s₂) Γ₃
| Do (e : Expr) (type : τ) :
  ExprType Γ₁ e type →
  StmtType Γ₁ (.Do e) Γ₁

end

end Types

section TypeProperties

theorem StmtDet (Γ₁ Γ₂ Γ₃ : Γ) (s : Stmt) :
  StmtType Γ₁ s Γ₂ → StmtType Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    unhygienic cases h1 <;> unhygienic cases h2
    any_goals rfl
    sorry

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

theorem ExprExtension (Γ₁ Γ₂ : Γ) (e : Expr) (type : τ) :
  ExprType Γ₁ e type → ExprType (Γ₂ ++ Γ₁) e type := by
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
      exists [type] }
    { unhygienic cases hs
      exists [] }
    { unhygienic cases hs
      rcases s₁_ih Γ₁ Γ₂_1 a with ⟨g1, hg1⟩
      rcases s₂_ih Γ₂_1 Γ₂ a_1 with ⟨g2, hg2⟩
      exists g2 ++ g1
      grind }
    { unhygienic cases hs
      exists [] }
    { unhygienic cases hs
      exists [] }
    unhygienic cases hs
    exists []


lemma StmtDecl (type : τ) : StmtType Γ₁ (Stmt.Decl type e) Γ₂ → Γ₂ = type :: Γ₁ := by
  grind [StmtType]

theorem StmtExtension (Γ₁ Γ₂ Γ₃ : Γ) (s : Stmt) :
  StmtType Γ₁ s (Γ₂ ++ Γ₁) → StmtType (Γ₃ ++ Γ₁) s (Γ₂ ++ Γ₃ ++ Γ₁) := by
    intro hs
    unhygienic induction s generalizing Γ₁ Γ₂ Γ₃
    stop sorry

theorem StmtPermutation (Γ₁ Γ₂ Δ : Γ) (s : Stmt) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  StmtType Γ₁ s (Δ ++ Γ₁) → StmtType Γ₂ s (Δ ++ Γ₂) := by
    intro heq hs
    have leq : Γ₂.length = Γ₁.length := by
      by_cases lt : Γ₂.length < Γ₁.length
      { let tp := Γ₁[0]
        have hx := heq tp (Γ₁.length - 1)
        simp at hx
        clear heq
        grind }
      by_cases gt : Γ₂.length > Γ₁.length
      { let tp := Γ₂[0]
        have hx := heq tp (Γ₂.length - 1)
        simp at hx
        clear heq
        grind }
      grind
    unhygienic induction s generalizing Γ₁ Γ₂ Δ
    { have := StmtDecl type hs
      have : Δ = [type] := by
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
      { apply s₁_ih Γ₁ Γ₂ g <;> try assumption
        grind }
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
          by_cases hx : x < Γ₂.length
          { grind [neg_index_r] }
          constructor
          { grind }
          grind } }
      { grind }
      grind }
    { by_cases hemp : Δ = []
      { simp only [hemp] at *
        unhygienic cases hs
        rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
        rcases StmtMono _ _ _ a_2 with ⟨g2, hg2⟩
        apply StmtType.If (Γ₂ := g1 ++ Γ₂) (Γ₃ := g2 ++ Γ₂)
        { apply ExprPermutation _ _ e .Bool heq
          grind }
        { apply s₁_ih Γ₁ Γ₂ g1 <;> try assumption
          grind }
        apply s₂_ih Γ₁ Γ₂ g2 <;> try assumption
        grind }
      have : Δ ++ Γ₁ ≠ Γ₁ := by
        intro eq
        have : (Δ ++ Γ₁).length > Γ₁.length := by
          simp
          grind
        grind
      grind [StmtType] }
    { by_cases hemp : Δ = []
      { simp only [hemp] at *
        unhygienic cases hs
        rcases StmtMono _ _ _ a_1 with ⟨g1, hg1⟩
        apply StmtType.While (Γ₂ := g1 ++ Γ₂)
        { apply ExprPermutation _ _ c .Bool heq
          grind }
        apply body_ih Γ₁ Γ₂ g1 <;> try assumption
        grind }
      have : Δ ++ Γ₁ ≠ Γ₁ := by
        intro eq
        have : (Δ ++ Γ₁).length > Γ₁.length := by
          simp
          grind
        grind
      grind [StmtType] }
    by_cases hemp : Δ = []
    { grind [StmtType] }
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
| VarDecl (type : τ) (e : Expr) :
  Eval
    ⟨.sourceStmt (.Decl type e), E, K⟩
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
| Break  :
  Eval
    ⟨.sourceStmt (.Break), E, K⟩
    ⟨.skip, E.drop 1, popK K (E.length - 1)⟩
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
| DeclK (type : τ) (Γ₁ : Γ) (Γ₂ : List Γ) :
  ContStmtType ((type:: Γ₁) :: Γ₂) K →
  ContExprType (Γ₁ :: Γ₂) (.declK x type :: K) type
| AssignK (x : VarName) (type : τ) (Γ₁ : List Γ) :
  (Γ₁.gcat(x) = type) →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.assignK x :: K) type
| BinOpLK (Γ₁ : List Γ) (op : BinOp) (e₂ : Expr) :
  ExprType Γ₁.gcat e₂ op.args.2 →
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.binopLK op e₂ :: K) op.args.1
| BinOpRK (Γ₁ : List Γ) (op : BinOp) (v₁ : Value) :
  ValueType v₁ op.args.1 →
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.binopRK op v₁ :: K) op.args.2
| UnOpK (Γ₁ : List Γ) (op : UnOp) :
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.unopK op :: K) op.args.1
| LoopCondK (Γ₁ : List Γ) (Γ₂ : List Γ) (body : Stmt) (c : Expr) :
  ExprType Γ₁.gcat c .Bool →
  StmtType Γ₁.gcat body Γ₂.gcat →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.loopK c body :: K) .Bool
