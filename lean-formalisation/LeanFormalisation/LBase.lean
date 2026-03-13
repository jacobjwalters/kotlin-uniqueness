import Mathlib.Data.Finmap
import Mathlib.Tactic.Basic

abbrev VarName := Nat
inductive Ty
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
  arg₁ : Ty
  arg₂ : Ty
  out : Ty

inductive UnOp
| IsZero

structure UnOpArgs where
  arg : Ty
  out : Ty

def BinOp.args : BinOp → BinOpArgs
| .Add => ⟨.Nat, .Nat, .Nat⟩
| .Sub => ⟨.Nat, .Nat, .Nat⟩
| .NatEq => ⟨.Nat, .Nat, .Bool⟩
| .BoolEq => ⟨.Bool, .Bool, .Bool⟩

inductive BinOp.step : BinOp → Value → Value → Value → Prop
| add (n m : Nat) : BinOp.step .Add (.Nat n) (.Nat m) (.Nat (n + m))
| sub (n m : Nat) : BinOp.step .Sub (.Nat n) (.Nat m) (.Nat (n - m))
| natEqTrue (n : Nat) : BinOp.step .NatEq (.Nat n) (.Nat n) .True
| natEqFalse (n m : Nat) : n ≠ m → BinOp.step .NatEq (.Nat n) (.Nat m) .False
| boolEqTT : BinOp.step .BoolEq .True .True .True
| boolEqFF : BinOp.step .BoolEq .False .False .True
| boolEqTF : BinOp.step .BoolEq .True .False .False
| boolEqFT : BinOp.step .BoolEq .False .True .False

def UnOp.args : UnOp → UnOpArgs
| .IsZero => ⟨.Nat, .Bool⟩

inductive UnOp.step : UnOp → Value → Value → Prop
| isZeroTrue : UnOp.step .IsZero (.Nat 0) .True
| isZeroFalse (n : Nat) : n ≠ 0 → UnOp.step .IsZero (.Nat n) .False

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
| Decl (type : Ty) (e : Lang .Expr) : Lang .Stmt
| Assign (x : VarName) (e : Lang .Expr) : Lang .Stmt
| Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) : Lang .Stmt
| Do (e : Lang .Expr) : Lang .Stmt

notation:100 s₁:100 ";" s₂:101 => Lang.Seq s₁ s₂
notation x "::=" exp => Lang.Assign x exp
abbrev Ctx := List Ty
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[List.length Γ₁ - 1 - x]? = Option.some type

def langShift {tg : Tag} (l : Nat) : Lang tg → Lang tg
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
  .BinOp (langShift l arg₁) (langShift l arg₂) op
| .UnOp (arg : Lang .Expr) (op : UnOp) =>
  .UnOp (langShift l arg) op
| .If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) =>
  .If (langShift l cond) (langShift l e₁) (langShift l e₂)
| .While (cond : Lang .Expr) (body : Lang .Expr) =>
  .While (langShift l cond) (langShift l body)
| .Break =>
  .Break
| .Scope (s : Lang .Stmt) (res : Lang .Expr) =>
  .Scope (langShift l s) (langShift l res)
-- # Stmt
| .Decl (type : Ty) (e : Lang .Expr) =>
  .Decl type (langShift l e)
| .Assign (x : VarName) (e : Lang .Expr) =>
  .Assign (x + l) (langShift l e)
| .Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) =>
  .Seq (langShift l s₁) (langShift l s₂)
| .Do (e : Lang .Expr) =>
  .Do (langShift l e)

section Types

inductive TypR : Tag → Type
| Stmt (Γ₁ : Ctx) : TypR .Stmt
| Expr (type : Ty) : TypR .Expr

inductive ExprType : Ctx → Lang .Expr → Ty → Prop

inductive Typ : (tg : Tag) → Ctx → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst :
  Typ .Expr Γ₁ .True (.Expr .Bool)
| FalseConst :
  Typ .Expr Γ₁ .False (.Expr .Bool)
| NatConst (n : Nat) :
  Typ .Expr Γ₁ (.Nat n) (.Expr .Nat)
| UnitConst :
  Typ .Expr Γ₁ .Unit (.Expr .Unit)
| VarAccess (x : VarName) (type : Ty) :
  (Γ₁(x) = type) →
  Typ .Expr Γ₁ (.Var x) (.Expr type)
| UnOp (arg : Lang .Expr) (op : UnOp) :
  Typ .Expr Γ₁ arg (.Expr op.args.1) →
  Typ .Expr Γ₁ (.UnOp arg op) (.Expr op.args.2)
| BinOp (arg₁ arg₂ : Lang .Expr) (op : BinOp) :
  Typ .Expr Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr Γ₁ arg₂ (.Expr op.args.2) →
  Typ .Expr Γ₁ (.BinOp arg₁ arg₂ op) (.Expr op.args.3)
| IfExpr (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : Ty) :
  Typ .Expr Γ₁ cond (.Expr .Bool) →
  Typ .Expr Γ₁ e₁ (.Expr type) →
  Typ .Expr Γ₁ e₂ (.Expr type) →
  Typ .Expr Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr Γ₁ cond (.Expr .Bool) →
  Typ .Expr Γ₁ body (.Expr .Unit) →
  Typ .Expr Γ₁ (.While cond body) (.Expr .Unit)
| BreakExpr (type : Ty) :
  Typ .Expr Γ₁ .Break (.Expr .Unit)
| ScopeExpr (s : Lang .Stmt) (e : Lang .Expr) (type : Ty) :
  Typ .Stmt Γ₁ s (.Stmt Γ₂) →
  Typ .Expr Γ₂ e (.Expr type) →
  Typ .Expr Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl (e : Lang .Expr) (type : Ty) :
  Typ .Expr Γ₁ e (.Expr type) →
  Typ .Stmt Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign (x : VarName) (e : Lang .Expr) (type : Ty) :
  Typ .Expr Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt Γ₂ s₂ Γ₃ →
  Typ .Stmt Γ₁ (s₁; s₂) Γ₃
| Do (e : Lang .Expr) (type : Ty) :
  Typ .Expr Γ₁ e (.Expr type) →
  Typ .Stmt Γ₁ (.Do e) (.Stmt Γ₁)

end Types

section TypeProperties

theorem lang_det (Γ₁ : Ctx) (tg : Tag) (Γ₂ Γ₃ : TypR tg) (s : Lang tg) :
  Typ tg Γ₁ s Γ₂ → Typ tg Γ₁ s Γ₃ → Γ₂ = Γ₃ := by
    intro h1 h2
    unhygienic induction h1 <;> try grind
    all_goals
    { cases h2
      grind }


theorem typ_permutation (Γ₁ Γ₂ : Ctx) (tg : Tag) (Γ₃ : TypR tg) (e : Lang tg) :
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

def TypR.extL (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

lemma stmt_mono (Γ₁ : Ctx) (tg : Tag) (Γ₂ : TypR tg) (s : Lang tg) :
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


lemma stmt_decl (type : Ty) : Typ .Stmt Γ₁ (.Decl type e) (.Stmt Γ₂) → Γ₂ = type :: Γ₁ := by
  intro h
  cases h
  rfl

theorem lang_extension (tg : Tag) (e : Lang tg) (res : TypR tg) (Γ₁ Γ₂ : Ctx) :
  Typ tg Γ₁ e res → Typ tg (Γ₁ ++ Γ₂) (langShift Γ₂.length e) (res.extR Γ₂) := by
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

def value_type : Value → Ty → Prop
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
| declK (type : Ty)
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

inductive PopLoopK : List Cont → List Cont → Nat → Prop
| loopK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopK c body n :: rest) rest n
| loopContK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopContK c body n :: rest) rest n
| skip (k : Cont) (rest result : List Cont) (n : Nat) :
  PopLoopK rest result n →
  PopLoopK (k :: rest) result n

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
| VarDecl (type : Ty) (e : Lang .Expr) :
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
| Break (K' : List Cont) (n : Nat) :
  PopLoopK K K' n →
  Eval
    ⟨.sourceExpr .Break, E, K⟩
    ⟨.skip, E.take n, K'⟩
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
| VarDeclDone (type : Ty) (v : Value) :
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
| BinOpR (op : BinOp) (v₁ v₂ result : Value) :
  op.step v₁ v₂ result →
  Eval
    ⟨.value v₂, E, .binopRK op v₁ :: K⟩
    ⟨.value result, E, K⟩
| UnOpDone (op : UnOp) (v result : Value) :
  op.step v result →
  Eval
    ⟨.value v, E, .unopK op :: K⟩
    ⟨.value result, E, K⟩
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


def initState (s : Lang .Stmt) : CEK := ⟨.sourceStmt s, [], []⟩

def terminalState (E : Environment) : CEK := ⟨.skip, E, []⟩

inductive ContTypeRes : Tag → Type
| Expr (type : Ty) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

-- # Expression Continuations
inductive ContType : (tg : Tag) → Ctx → List Cont → ContTypeRes tg → Prop
| IfCondK (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ Γ₂ Γ₃ : Ctx) (type : Ty) :
  Typ .Expr Γ₁ s₁ (.Expr type) →
  Typ .Expr Γ₁ s₂ (.Expr type) →
  ContType .Expr Γ₁ K (.Expr type) →
  ContType .Expr Γ₁ (.ifCondK s₁ s₂ :: K) (.Expr .Bool)
| DeclK (type : Ty) (Γ₁ : Ctx) :
  ContType .Stmt (type :: Γ₁) K .Stmt →
  ContType .Expr Γ₁ (.declK type :: K) (.Expr type)
| AssignK (x : VarName) (type : Ty) (Γ₁ : Ctx) :
  (Γ₁[x]! = type) →
  ContType .Stmt Γ₁ K .Stmt →
  ContType .Expr Γ₁ (.assignK x :: K) (.Expr type)
| BinOpLK (Γ₁ : Ctx) (op : BinOp) (e₂ : Lang .Expr) :
  ExprType Γ₁ e₂ op.args.2 →
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK (Γ₁ : Ctx) (op : BinOp) (v₁ : Value) :
  value_type v₁ op.args.1 →
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK (Γ₁ : Ctx) (op : UnOp) :
  ContType .Expr Γ₁ K (.Expr op.args.out) →
  ContType .Expr Γ₁ (.unopK op :: K) (.Expr op.args.1)
| LoopK (Γ₁ : Ctx) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContType .Expr (Γ₁.take n) K (.Expr .Unit) →
  ContType .Expr Γ₁ (.loopK c body n :: K) (.Expr .Bool)
| LoopContK (Γ₁ : Ctx) (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Typ .Expr Γ₁ c (.Expr .Bool) →
  Typ .Expr Γ₁ e (.Expr .Unit) →
  ContType .Expr (Γ₁.take n) K (.Expr .Unit) →
  ContType .Expr Γ₁ (.loopContK c body n :: K) (.Expr .Bool)
| ScopeExitK (Γ₁ : Ctx) (n : Nat) (type : Ty) :
  ContType .Expr (Γ₁.take n) K (.Expr type) →
  ContType .Expr Γ₁ (.scopeExitK n :: K) (.Expr type)
| ExprStmtK (Γ₁ : Ctx) (type : Ty) :
  ContType .Stmt Γ₁ K .Stmt →
  ContType .Expr Γ₁ (.exprStmtK :: K) (.Expr type)
-- # Statement Continuations
| HaltK (Γ₁ : Ctx) :
  ContType .Stmt Γ₁ [] .Stmt
| SeqK (Γ₁ : Ctx) (Γ₂ : Ctx) (s : Lang .Stmt) :
  Typ .Stmt Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt Γ₂ K .Stmt →
  ContType .Stmt Γ₁ (.seqK s :: K) .Stmt
| ScopeBodyK (Γ₁ : Ctx) (body : Lang .Stmt) (e : Lang .Expr) (type : Ty) (n : Nat) :
  Typ .Expr Γ₁ e (.Expr type) →
  ContType .Expr (Γ₁.take n) K (.Expr type) →
  ContType .Stmt Γ₁ (.scopeBodyK c n :: K) .Stmt
