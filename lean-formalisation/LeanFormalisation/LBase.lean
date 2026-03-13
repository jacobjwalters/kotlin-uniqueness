import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat
-- TODO: use
-- https://leanprover-community.github.io/contribute/style.html
-- https://leanprover-community.github.io/contribute/naming.html

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

-- TODO: Convert to small step semantics
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

-- TODO: Convert to small step semantics
def UnOp.run : UnOp → Value → Value
| .IsZero => fun x =>
  match x with
  | .Nat 0 => .True
  | .Nat _ => .False
  | _ => panic! "Not implemented"

-- TODO: I am not very happy with this tag system, because it means that some statements
-- (e.g. StmtMono) have confusing formulations for the stmt vs expression case.
-- Don't change anything yet, but please suggest some possibilities for other ways we
-- could do this.
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
abbrev Γ := List τ
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[List.length Γ₁ - 1 - x]? = Option.some type

-- TODO: Remove st
def langShift {tg : Tag} (l st : Nat) : Lang tg → Lang tg
-- # Expr
| .Var (x : VarName) =>
  .Var (x + l)
| .True =>
  .True
| .False =>
  .False
| .Nat (n : Nat) =>
  .Nat n
| .Unit =>
  .Unit
| .BinOp (arg₁ : Lang .Expr) (arg₂ : Lang .Expr) (op : BinOp) =>
  .BinOp (langShift l st arg₁) (langShift l st arg₂) op
| .UnOp (arg : Lang .Expr) (op : UnOp) =>
  .UnOp (langShift l st arg) op
| .If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) =>
  .If (langShift l st cond) (langShift l st e₁) (langShift l st e₂)
| .While (cond : Lang .Expr) (body : Lang .Expr) =>
  .While (langShift l st cond) (langShift l st body)
| .Break =>
  .Break
| .Scope (s : Lang .Stmt) (res : Lang .Expr) =>
  .Scope (langShift l st s) (langShift l st res)
-- # Stmt
| .Decl (type : τ) (e : Lang .Expr) =>
  .Decl type (langShift l st e)
| .Assign (x : VarName) (e : Lang .Expr) =>
  .Assign (x + l) (langShift l st e)
| .Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) =>
  .Seq (langShift l st s₁) (langShift l st s₂)
| .Do (e : Lang .Expr) =>
  .Do (langShift l st e)

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

theorem LangDet (Γ₁ : Γ) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) :
  Typ tg Γ₁ s Γ₂ → Typ tg Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    unhygienic induction h1 <;> try grind
    all_goals
    { cases h2
      grind }

-- TODO: split helper lemmas into separate file
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

def TypR.extL (Γ₁ : Γ) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Γ) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

lemma StmtMono (Γ₁ : Γ) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
  Typ tg Γ₁ s Γ₂ → ∃ Γ₃ : TypR tg, Γ₃.extR Γ₁ = Γ₂ := by
    intro hs
    unhygienic induction hs <;> try grind
    all_goals try
    { eapply Exists.intro
      rw [TypR.extR] }
    { eapply Exists.intro
      rw [TypR.extR]
      have : ?VarDecl.h.Γ₂ = [type] := by rfl
      grind }
    { eapply Exists.intro
      rw [TypR.extR]
      have : ?VarAssign.h.Γ₂ = [] := by rfl
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
    have : ?Do.h.Γ₂ = [] := by rfl
    grind


lemma StmtDecl (type : τ) : Typ .Stmt Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

theorem LangExtension (tg : Tag) (e : Lang tg) (res : TypR tg) (Γ₁ Γ₂ : Γ) :
  Typ tg Γ₁ e res → Typ tg (Γ₁ ++ Γ₂) (langShift Γ₂.length 0 e) (res.extR Γ₂) := by
    intro h
    unhygienic induction h generalizing Γ₂ <;>try solve_by_elim
    { rw [langShift, TypR.extR]
      apply Typ.VarAccess
      grind }
    { rw [langShift]
      solve_by_elim [Typ.ScopeExpr] }
    { rw [langShift, TypR.extR]
      apply Typ.VarAssign _ _ _ (a_ih Γ₂)
      grind }
    rw [langShift]
    solve_by_elim [Typ.Seq]


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

-- TODO: change to small step semantics
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

inductive ContTypeRes : Tag → Type
| Expr (type : τ) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

-- # Expression Continuations
inductive ContType : (tg : Tag) → Γ → List Cont → ContTypeRes tg → Prop
| IfCondK (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ Γ₂ Γ₃ : Γ) (type : τ) :
  Typ .Expr Γ₁ s₁ (.Expr type) →
  Typ .Expr Γ₁ s₂ (.Expr type) →
  ContType .Expr Γ₁ K (.Expr type) →
  ContType .Expr Γ₁ (.ifCondK s₁ s₂ :: K) (.Expr .Bool)
| DeclK (type : τ) (Γ₁ : Γ) :
  ContType .Stmt (type :: Γ₁) K .Stmt →
  ContType .Expr Γ₁ (.declK type :: K) (.Expr type)
| AssignK (x : VarName) (type : τ) (Γ₁ : Γ) :
  (Γ₁[x]! = type) →
  ContType .Stmt Γ₁ K .Stmt →
  ContType .Expr Γ₁ (.assignK x :: K) (.Expr type)
| BinOpLK (Γ₁ : Γ) (op : BinOp) (e₂ : Lang .Expr) :
  ExprType Γ₁ e₂ op.args.2 →
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK (Γ₁ : Γ) (op : BinOp) (v₁ : Value) :
  ValueType v₁ op.args.1 →
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK (Γ₁ : Γ) (op : UnOp) :
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.unopK op :: K) (.Expr op.args.1)
| LoopK (Γ₁ : Γ) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContType .Expr (Γ₁.take n) K (.Expr .Unit) →
  ContType .Expr Γ₁ (.loopK c body n :: K) (.Expr .Bool)
| LoopContK (Γ₁ : Γ) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContType .Expr (Γ₁.take n) K (.Expr .Unit) →
  ContType .Expr Γ₁ (.loopContK c body n :: K) (.Expr .Bool)
| ScopeExitK (Γ₁ : Γ) (n : Nat) (type : τ) :
  ContType .Expr (Γ₁.take n) K (.Expr type) →
  ContType .Expr Γ₁ (.scopeExitK n :: K) (.Expr type)
| ExprStmtK (Γ₁ : Γ) (type : τ) :
  ContType .Stmt Γ₁ K .Stmt →
  ContType .Expr Γ₁ (.exprStmtK :: K) (.Expr type)
-- # Statement Continuations
| HaltK (Γ₁ : Γ) :
  ContType .Stmt Γ₁ [] .Stmt
| SeqK (Γ₁ : Γ) (Γ₂ : Γ) (s : Lang .Stmt) :
  Typ .Stmt Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt Γ₂ K .Stmt →
  ContType .Stmt Γ₁ (.seqK s :: K) .Stmt
| ScopeBodyK (Γ₁ : Γ) (body : Lang .Stmt) (e : Lang .Expr) (type : τ) (n : Nat) :
  Typ .Expr Γ₁ e (.Expr type) →
  ContType .Expr (Γ₁.take n) K (.Expr type) →
  ContType .Stmt Γ₁ (.scopeBodyK c n :: K) .Stmt
