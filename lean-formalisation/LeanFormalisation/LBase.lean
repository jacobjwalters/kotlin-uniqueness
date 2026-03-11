import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat

inductive τ
| Nat
| Bool
| Unit
deriving Repr, Inhabited


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

inductive Tag
| Expr
| Stmt

inductive Lang : Tag → Type
-- # Expr
| Var (x : VarName) : Lang .Expr
| True : Lang .Expr
| False : Lang .Expr
| Nat (n : Nat) : Lang .Expr
| Unit : Lang .Expr
| BinOp (arg₁ : Lang .Expr) (arg₂ : Lang .Expr) (op : BinOp) : Lang .Expr
| UnOp (arg : Lang .Expr) (op : UnOp) : Lang .Expr
| If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) : Lang .Expr
| While (cond : Lang .Expr) (body : Lang .Expr) : Lang .Expr
| Break : Lang .Expr
| Scope (s : Lang .Stmt) (res : Lang .Expr) : Lang .Expr
-- # Stmt
| Decl (type : τ) (e : Lang .Expr) : Lang .Stmt
| Assign (x : VarName) (e : Lang .Expr) : Lang .Stmt
| Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) : Lang .Stmt
| Do (e : Lang .Expr) : Lang .Stmt

notation:100 s₁:100 ";" s₂:101 => Lang.Seq s₁ s₂
notation x "::=" exp => Lang.Assign x exp
#check List.get
abbrev Γ := List τ
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[List.length Γ₁ - 1 - x]? = Option.some type

section Types

inductive TypR : Tag → Type
| Stmt (Γ₁ : Γ) : TypR .Stmt
| Expr (type : τ) : TypR .Expr

inductive ExprType : Γ → Lang .Expr → τ → Prop

inductive Typ : (tg : Tag) → Γ → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst :
  Typ .Expr Γ₁ .True (.Expr .Bool)
| FalseConst :
  Typ .Expr Γ₁ .False (.Expr .Bool)
| NatConst (n : Nat) :
  Typ .Expr Γ₁ (.Nat n) (.Expr .Nat)
| UnitConst :
  Typ .Expr Γ₁ .Unit (.Expr .Unit)
| VarAccess (x : VarName) (type : τ) :
  (Γ₁(x) = type) →
  Typ .Expr Γ₁ (.Var x) (.Expr type)
| UnOp (arg : Lang .Expr) (op : UnOp) :
  Typ .Expr Γ₁ arg (.Expr op.args.1) →
  Typ .Expr Γ₁ (.UnOp arg op) (.Expr op.args.2)
| BinOp (arg₁ arg₂ : Lang .Expr) (op : BinOp) :
  Typ .Expr Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr Γ₁ arg₂ (.Expr op.args.2) →
  Typ .Expr Γ₁ (.BinOp arg₁ arg₂ op) (.Expr op.args.3)
| IfExpr (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : τ) :
  Typ .Expr Γ₁ cond (.Expr .Bool) →
  Typ .Expr Γ₁ e₁ (.Expr type) →
  Typ .Expr Γ₁ e₂ (.Expr type) →
  Typ .Expr Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr Γ₁ cond (.Expr .Bool) →
  Typ .Expr Γ₁ body (.Expr .Unit) →
  Typ .Expr Γ₁ (.While cond body) (.Expr .Unit)
| BreakExpr (type : τ) :
  Typ .Expr Γ₁ .Break (.Expr .Unit)
| ScopeExpr (s : Lang .Stmt) (e : Lang .Expr) (type : τ) :
  Typ .Stmt Γ₁ s (.Stmt Γ₂) →
  Typ .Expr Γ₂ e (.Expr type) →
  Typ .Expr Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl (e : Lang .Expr) (type : τ) :
  Typ .Expr Γ₁ e (.Expr type) →
  Typ .Stmt Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign (x : VarName) (e : Lang .Expr) (type : τ) :
  Typ .Expr Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt Γ₂ s₂ Γ₃ →
  Typ .Stmt Γ₁ (s₁; s₂) Γ₃
| Do (e : Lang .Expr) (type : τ) :
  Typ .Expr Γ₁ e (.Expr type) →
  Typ .Stmt Γ₁ (.Do e) (.Stmt Γ₁)

end Types

section TypeProperties

theorem StmtDet (Γ₁ : Γ) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) :
  Typ tg Γ₁ s Γ₂ → Typ tg Γ₁ s Γ₃ → tg = .Stmt → Γ₂ = Γ₃ := by
    intro h1 h2 eq
    unhygienic induction h1 <;> try grind
    { cases h2
      rfl }
    { cases h2
      rfl }
    { unhygienic cases h2
      grind }
    cases h2
    rfl


theorem ExprDet (Γ₁ : Γ) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) :
  Typ tg Γ₁ s Γ₂ → Typ tg Γ₁ s Γ₃ → tg = .Expr → Γ₂ = Γ₃ := by
    intro h1 h2 eq
    unhygienic induction h1 <;> try grind
    all_goals
    { cases h2
      grind [StmtDet] }

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
/-
theorem ExprExtension (Γ₁ Γ₂ : Γ) (e : Expr) (type : τ) :
  Type Γ₁ e type → ExprType (Γ₂ ++ Γ₁) e type := by
    intro hg
    unhygienic induction e generalizing type <;> try grind [Expr, ExprType]
-/
theorem TypPermutation (Γ₁ Γ₂ : Γ) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
  (∀ tp x, (Γ₁(x) = tp) ↔ Γ₂(x) = tp) →
  Typ tg Γ₁ e Γ₃ → Typ tg Γ₂ e Γ₃ := by
    intro hg
    have leq : Γ₁.length = Γ₂.length := by
      by_cases h1: Γ₂.length < Γ₁.length
      { have hi := hg Γ₁[0] (Γ₁.length - 1)
        clear hg
        grind }
      by_cases h2: Γ₁.length < Γ₂.length
      { have hi := hg Γ₂[0] (Γ₂.length - 1)
        clear hg
        grind }
      grind
    have : Γ₁ = Γ₂ := by
      ext
      clear e
      rename_i idx el
      have hi := hg el (Γ₁.length - idx - 1)
      by_cases hid: idx < Γ₁.length
      { clear hg
        grind }
      grind
    rw [this]
    grind

--check to see if it is possible to make this work
/-
lemma StmtMono (Γ₁ : Γ) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  tg = .Stmt → Typ tg Γ₁ s Γ₂ → ∃ Γ₃, Γ₂ = TypR.Stmt (Γ₃ ++ Γ₁) := by
    intro heq hs
    unhygienic induction s generalizing Γ₁ Γ₂ <;> try grind
    { unhygienic cases hs
      exists [type] }
    { unhygienic cases hs
      exists [] }
    { unhygienic cases hs
      rcases s₁_ih Γ₁ Γ₂_1 (by rfl) a with ⟨g1, hg1⟩
      rcases s₂_ih Γ₂_1 Γ₂ (by rfl) a_1 with ⟨g2, hg2⟩
      exists g2 ++ g1
      grind }
    unhygienic cases hs
    exists []
-/

lemma StmtDecl (type : τ) : Typ .Stmt Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl
/-
theorem StmtExtension (Γ₁ Γ₂ Γ₃ : Γ) (s : Stmt) :
  StmtType Γ₁ s (Γ₂ ++ Γ₁) → StmtType (Γ₃ ++ Γ₁) s (Γ₂ ++ Γ₃ ++ Γ₁) := by
    intro hs
    unhygienic induction s generalizing Γ₁ Γ₂ Γ₃
    stop sorry
-/
end TypeProperties

def liftValue : Value → Lang .Expr
| .True => .True
| .False => .False
| .Nat (n : Nat) => .Nat n
| .Unit => .Unit

def ValueType : Value → τ → Prop
| .True, .Bool => True
| .False, .Bool => True
| .Nat _, .Nat => True
| .Unit, .Unit => True
| _, _ => False

inductive Control
| sourceExpr (e : Lang .Expr)
| sourceStmt (s : Lang .Stmt)
| value (v : Value)
| skip

abbrev Map (val : Type) := Finmap (fun _ : VarName ↦ val)

abbrev Environment := List Value

inductive Cont
| ifCondK (e₁ e₂ : Lang .Expr)
| declK (type : τ)
| assignK (x : VarName)
| seqK (s : Lang .Stmt)
| binopLK (op : BinOp) (e₂ : Lang .Expr)
| binopRK (op : BinOp) (v : Value)
| unopK (op : UnOp)
| loopK (c : Lang .Expr) (body : Lang .Expr) (n : Nat)
| loopContK (c : Lang .Expr) (body : Lang .Expr) (n : Nat)
| scopeBodyK (e : Lang .Expr) (n : Nat)
| scopeExitK (n : Nat)
| exprStmtK

abbrev CEK := Control × Environment × List Cont

notation E "("x")!" => Option.get! (Finmap.lookup x (List.getD E 0 ∅ : Map Value) : Option Value)

def popLoopK (K : List Cont) : List Cont × Nat :=
  match K with
  | .loopK _ _ n :: li => ⟨li, n⟩
  | .loopContK _ _ n :: li => ⟨li, n⟩
  | _ :: li => popLoopK li
  | [] => panic! "popK from an empty List"

inductive Eval : CEK → CEK → Prop
-- # Expr
| Val (v : Value) :
  Eval
    ⟨.sourceExpr (liftValue v), E, K⟩
    ⟨.value v, E, K⟩
| Var (v : Value) (x : VarName) :
  Eval
    ⟨.sourceExpr (.Var x), E, K⟩
    ⟨.value (E[x]!), E, K⟩
| VarDecl (type : τ) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Decl type e), E, K⟩
    ⟨.sourceExpr e, E, (.declK type) :: K⟩
| Assign (x : VarName) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Assign x e), E, K⟩
    ⟨.sourceExpr e, E, (.assignK x) :: K⟩
| Seq (s₁ s₂ : Lang .Stmt) :
  Eval
    ⟨.sourceStmt (.Seq s₁ s₂), E, K⟩
    ⟨.sourceStmt s₁, E, (.seqK s₂) :: K⟩
| ExprStmt (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Do e), E, K⟩
    ⟨.sourceExpr e, E, .exprStmtK :: K⟩
| BinOp (e₁ e₂ : Lang .Expr) (op : BinOp) :
  Eval
    ⟨.sourceExpr (.BinOp e₁ e₂ op), E, K⟩
    ⟨.sourceExpr e₁, E, (.binopLK op e₂) :: K⟩
| UnOp (e : Lang .Expr) (op : UnOp) :
  Eval
    ⟨.sourceExpr (.UnOp e op), E, K⟩
    ⟨.sourceExpr e, E, (.unopK op) :: K⟩
| If (e : Lang .Expr) (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.If e s₁ s₂), E, K⟩
    ⟨.sourceExpr e, E, (.ifCondK s₁ s₂) :: K⟩
| While (c : Lang .Expr) (body : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.While c body), E, K⟩
    ⟨.sourceExpr c, E, (.loopK c body E.length) :: K⟩
| Break  :
  Eval
    ⟨.sourceExpr .Break, E, K⟩
    ⟨.skip, E.take (popLoopK K).2, (popLoopK K).1⟩
| Scope (s : Lang .Stmt) (e : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.Scope s e), E, K⟩
    ⟨.sourceStmt s, E, .scopeBodyK e E.length :: K⟩
-- # Cont
| IfTrue (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .True, E, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr e₁, E, K⟩
| IfFalse (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .False, E, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr e₁, E, K⟩
| VarDeclDone (type : τ) (v : Value) :
  Eval
    ⟨.value v, E, .declK type :: K⟩
    ⟨.skip, v :: E, K⟩
| AssignDone (x : VarName) (v : Value) :
  Eval
    ⟨.value v, E, .assignK x :: K⟩
    ⟨.skip, E.set x v, K⟩
| SeqDone (s₂ : Lang .Stmt) :
  Eval
    ⟨.skip, E, .seqK s₂ :: K⟩
    ⟨.sourceStmt s₂, E, K⟩
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr) :
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
| LoopTrue (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .True, E, .loopK c body n :: K⟩
    ⟨.sourceExpr body, E, .loopK c body n :: K⟩
| LoopFalse (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .False, E, .loopK c body n :: K⟩
    ⟨.value .Unit, E, K⟩
| LoopCont (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .Unit, E, .loopContK c body n :: K⟩
    ⟨.sourceExpr c, E, .loopK c body n :: K⟩
| ScopeBody (body : Lang .Expr) (n : Nat) :
  Eval
    ⟨.skip, E, .scopeBodyK body n :: K⟩
    ⟨.sourceExpr body, E, .scopeExitK n :: K⟩
| ScopeExit (body : Lang .Expr) (n : Nat) (v : Value) :
  Eval
    ⟨.value V, E, .scopeExitK n :: K⟩
    ⟨.value V, E.take n, K⟩


def init_state (s : Lang .Stmt) : CEK := ⟨.sourceStmt s, [], []⟩

def terminal_state (E : Environment) : CEK := ⟨.skip, E, []⟩


-- # Expression Continuations
mutual
inductive ContExprType : Γ → List Cont → τ → Prop
| IfCondK (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ Γ₂ Γ₃ : Γ) (type : τ) :
  Typ .Expr Γ₁ s₁ (.Expr type) →
  Typ .Expr Γ₁ s₂ (.Expr type) →
  ContExprType Γ₁ K type →
  ContExprType Γ₁ (.ifCondK s₁ s₂ :: K) .Bool
| DeclK (type : τ) (Γ₁ : Γ) :
  ContStmtType (type :: Γ₁) K →
  ContExprType Γ₁ (.declK type :: K) type
| AssignK (x : VarName) (type : τ) (Γ₁ : Γ) :
  (Γ₁[x]! = type) →
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.assignK x :: K) type
| BinOpLK (Γ₁ : Γ) (op : BinOp) (e₂ : Lang .Expr) :
  ExprType Γ₁ e₂ op.args.2 →
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.binopLK op e₂ :: K) op.args.1
| BinOpRK (Γ₁ : Γ) (op : BinOp) (v₁ : Value) :
  ValueType v₁ op.args.1 →
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.binopRK op v₁ :: K) op.args.2
| UnOpK (Γ₁ : Γ) (op : UnOp) :
  ContExprType Γ₁ K op.args.out →
  ContExprType Γ₁ (.unopK op :: K) op.args.1
| LoopK (Γ₁ : Γ) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContExprType (Γ₁.take n) K .Unit →
  ContExprType Γ₁ (.loopK c body n :: K) .Bool
| LoopContK (Γ₁ : Γ) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContExprType (Γ₁.take n) K .Unit →
  ContExprType Γ₁ (.loopContK c body n :: K) .Bool
| ScopeExitK (Γ₁ : Γ) (n : Nat) (type : τ) :
  ContExprType (Γ₁.take n) K type →
  ContExprType Γ₁ (.scopeExitK n :: K) type
| ExprStmtK (Γ₁ : Γ) (type : τ) :
  ContStmtType Γ₁ K →
  ContExprType Γ₁ (.exprStmtK :: K) type


-- # Statement Continuations

inductive ContStmtType : Γ → List Cont → Prop
| HaltK (Γ₁ : Γ) :
  ContStmtType Γ₁ []
| SeqK (Γ₁ : Γ) (Γ₂ : Γ) (s : Lang .Stmt) :
  Typ .Stmt Γ₁ s (.Stmt Γ₂) →
  ContStmtType Γ₂ K →
  ContStmtType Γ₁ (.seqK s :: K)
| ScopeBodyK (Γ₁ : Γ) (body : Lang .Stmt) (e : Lang .Expr) (type : τ) (n : Nat) :
  Typ .Expr Γ₁ e (.Expr type) →
  ContExprType (Γ₁.take n) K type →
  ContStmtType Γ₁ (.scopeBodyK c n :: K)

end
