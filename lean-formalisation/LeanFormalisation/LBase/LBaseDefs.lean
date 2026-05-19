
abbrev VarName := Nat
inductive Ty
| nat
| bool
| unit
deriving Repr, Inhabited, DecidableEq --! qtz: added DecidableEq


inductive Value
| True
| False
| Nat (n : Nat)
| Unit
deriving Inhabited, Repr, DecidableEq --! qtz: added DecidableEq

inductive BinOp
| Add
| Sub
| NatEq
| BoolEq
deriving Repr, DecidableEq --! qtz: added this line

structure BinOpArgs where
  arg₁ : Ty
  arg₂ : Ty
  out : Ty

inductive UnOp
| IsZero
deriving Repr, DecidableEq --! qtz: added this line

structure UnOpArgs where
  arg : Ty
  out : Ty

def BinOp.args : BinOp → BinOpArgs
| .Add => ⟨.nat, .nat, .nat⟩
| .Sub => ⟨.nat, .nat, .nat⟩
| .NatEq => ⟨.nat, .nat, .bool⟩
| .BoolEq => ⟨.bool, .bool, .bool⟩

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
| .IsZero => ⟨.nat, .bool⟩

inductive UnOp.step : UnOp → Value → Value → Prop
| isZeroTrue : UnOp.step .IsZero (.Nat 0) .True
| isZeroFalse (n : Nat) : n ≠ 0 → UnOp.step .IsZero (.Nat n) .False

inductive Tag
| Expr
| Stmt
deriving Repr, DecidableEq --! qtz: added this line

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
| Break (l : Nat) : Lang .Expr
| Scope (s : Lang .Stmt) (res : Lang .Expr) : Lang .Expr
-- # Stmt
| Decl (type : Ty) (e : Lang .Expr) : Lang .Stmt
| Assign (x : VarName) (e : Lang .Expr) : Lang .Stmt
| Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) : Lang .Stmt
| Do (e : Lang .Expr) : Lang .Stmt
deriving Repr, DecidableEq --! qtz: added this line

notation:100 s₁:100 ";" s₂:101 => Lang.Seq s₁ s₂
notation x "::=" exp => Lang.Assign x exp
abbrev Ctx := List Ty
abbrev JCtx := List Nat
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[x]? = Option.some type

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
| .Break l =>
  .Break l
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

inductive Typ : (tg : Tag) → JCtx → Ctx → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst :
  Typ .Expr Δ₁ Γ₁ .True (.Expr .bool)
| FalseConst :
  Typ .Expr Δ₁ Γ₁ .False (.Expr .bool)
| NatConst (n : Nat) :
  Typ .Expr Δ₁ Γ₁ (.Nat n) (.Expr .nat)
| UnitConst :
  Typ .Expr Δ₁ Γ₁ .Unit (.Expr .unit)
| VarAccess (x : VarName) (type : Ty) :
  (Γ₁(x) = type) →
  Typ .Expr Δ₁ Γ₁ (.Var x) (.Expr type)
| UnOp (arg : Lang .Expr) (op : UnOp) :
  Typ .Expr Δ₁ Γ₁ arg (.Expr op.args.1) →
  Typ .Expr Δ₁ Γ₁ (.UnOp arg op) (.Expr op.args.2)
| BinOp (arg₁ arg₂ : Lang .Expr) (op : BinOp) :
  Typ .Expr Δ₁ Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr Δ₁ Γ₁ arg₂ (.Expr op.args.2) →
  Typ .Expr Δ₁ Γ₁ (.BinOp arg₁ arg₂ op) (.Expr op.args.3)
| IfExpr (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr Δ₁ Γ₁ e₁ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ e₂ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ body (.Expr .unit) →
  Typ .Expr Δ₁ Γ₁ (.While cond body) (.Expr .unit)
| BreakExpr (type : Ty) (l : Nat) :
  l < Δ₁.length →
  Typ .Expr Δ₁ Γ₁ (.Break l) (.Expr type)
| ScopeExpr (s : Lang .Stmt) (e : Lang .Expr) (type : Ty) :
  Typ .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  Typ .Expr Δ₁ Γ₂ e (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign (x : VarName) (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt Δ₁ Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt Δ₁ Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt Δ₁ Γ₂ s₂ Γ₃ →
  Typ .Stmt Δ₁ Γ₁ (s₁; s₂) Γ₃
| Do (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Do e) (.Stmt Γ₁)

end Types

section TypeProperties

def TypR.extL (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

end TypeProperties

def liftValue : Value → Lang .Expr
| .True => .True
| .False => .False
| .Nat (n : Nat) => .Nat n
| .Unit => .Unit

def value_type : Value → Ty → Prop
| .True, .bool => True
| .False, .bool => True
| .Nat _, .nat => True
| .Unit, .unit => True
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

abbrev JStackCtx := List (Nat × List Cont)

structure CEK where
  C : Control
  E : Environment
  J : JStackCtx
  K : List Cont

-- Do we need this relation in the current Jump Context implementation?
/-
inductive PopLoopK : List Cont → List Cont → Nat → Prop
| loopK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopK c body n :: rest) rest n
| loopContK (c body : Lang .Expr) (n : Nat) (rest : List Cont) :
  PopLoopK (.loopContK c body n :: rest) rest n
| skip (k : Cont) (rest result : List Cont) (n : Nat) :
  PopLoopK rest result n →
  PopLoopK (k :: rest) result n
-/

inductive Eval : CEK → CEK → Prop
-- # Expr
| Val (v : Value) :
  Eval
    ⟨.sourceExpr (liftValue v), E, J, K⟩
    ⟨.value v, E, J, K⟩
| Var (x : VarName) :
  Eval
    ⟨.sourceExpr (.Var x), E, J, K⟩
    ⟨.value (E[x]!), E, J, K⟩
| VarDecl (type : Ty) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Decl type e), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.declK type) :: K⟩
| Assign (x : VarName) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Assign x e), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.assignK x) :: K⟩
| Seq (s₁ s₂ : Lang .Stmt) :
  Eval
    ⟨.sourceStmt (.Seq s₁ s₂), E, J, K⟩
    ⟨.sourceStmt s₁, E, J, (.seqK s₂) :: K⟩
| ExprStmt (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Do e), E, J, K⟩
    ⟨.sourceExpr e, E, J, .exprStmtK :: K⟩
| BinOp (e₁ e₂ : Lang .Expr) (op : BinOp) :
  Eval
    ⟨.sourceExpr (.BinOp e₁ e₂ op), E, J, K⟩
    ⟨.sourceExpr e₁, E, J, (.binopLK op e₂) :: K⟩
| UnOp (e : Lang .Expr) (op : UnOp) :
  Eval
    ⟨.sourceExpr (.UnOp e op), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.unopK op) :: K⟩
| If (e : Lang .Expr) (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.If e s₁ s₂), E, J, K⟩
    ⟨.sourceExpr e, E, J, (.ifCondK s₁ s₂) :: K⟩
| While (c : Lang .Expr) (body : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.While c body), E, J, K⟩
    ⟨.sourceExpr c, E, J, (.loopK c body E.length) :: K⟩
| Break (K' : List Cont) (l : Nat):
  Eval
    ⟨.sourceExpr (.Break l), E, J, K⟩
    -- was skip before, should it be .skip?
    ⟨.value .Unit, E.drop (E.length - J[l]!.1), J.drop (l + 1), J[l]!.2⟩
| Scope (s : Lang .Stmt) (e : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.Scope s e), E, J, K⟩
    ⟨.sourceStmt s, E, J, .scopeBodyK e E.length :: K⟩
-- # Cont
| IfTrue (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .True, E, J, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₁, E, J, K⟩
| IfFalse (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .False, E, J, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₂, E, J, K⟩
| VarDeclDone (type : Ty) (v : Value) :
  Eval
    ⟨.value v, E, J, .declK type :: K⟩
    ⟨.skip, v :: E, J, K⟩
| AssignDone (x : VarName) (v : Value) :
  Eval
    ⟨.value v, E, J, .assignK x :: K⟩
    ⟨.skip, E.set x v, J, K⟩
| SeqDone (s₂ : Lang .Stmt) :
  Eval
    ⟨.skip, E, J, .seqK s₂ :: K⟩
    ⟨.sourceStmt s₂, E, J, K⟩
| ExprStmtDone (v : Value) :
  Eval
    ⟨.value v, E, J, .exprStmtK :: K⟩
    ⟨.skip, E, J, K⟩
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr) :
  Eval
    ⟨.value v₁, E, J, .binopLK op e₂ :: K⟩
    ⟨.sourceExpr e₂, E, J, .binopRK op v₁ :: K⟩
| BinOpR (op : BinOp) (v₁ v₂ result : Value) :
  op.step v₁ v₂ result →
  Eval
    ⟨.value v₂, E, J, .binopRK op v₁ :: K⟩
    ⟨.value result, E, J, K⟩
| UnOpDone (op : UnOp) (v result : Value) :
  op.step v result →
  Eval
    ⟨.value v, E, J, .unopK op :: K⟩
    ⟨.value result, E, J, K⟩
| LoopTrue (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .True, E, J, .loopK c body n :: K⟩
    ⟨.sourceExpr body, E, ⟨n, K⟩ :: J, .loopContK c body n :: K⟩
| LoopFalse (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .False, E, J, .loopK c body n :: K⟩
    ⟨.value .Unit, E.drop (E.length - n), J, K⟩
| LoopCont (body : Lang .Expr) (c : Lang .Expr) (n : Nat) (K' : List Cont) :
  Eval
    ⟨.value .Unit, E, ⟨n, K⟩ :: J, .loopContK c body n :: K'⟩
    ⟨.sourceExpr c, E, J, .loopK c body n :: K⟩
| ScopeBody (body : Lang .Expr) (n : Nat) :
  Eval
    ⟨.skip, E, J, .scopeBodyK body n :: K⟩
    ⟨.sourceExpr body, E, J, .scopeExitK n :: K⟩
| ScopeExit (body : Lang .Expr) (n : Nat) (v : Value) :
  Eval
    ⟨.value v, E, J, .scopeExitK n :: K⟩
    ⟨.value v, E.drop (E.length - n), J, K⟩


def initState (s : Lang .Stmt) : CEK := ⟨.sourceStmt s, [], [], []⟩

def terminalState (E : Environment) (J : JStackCtx) : CEK := ⟨.skip, E, J, []⟩

inductive ContTypeRes : Tag → Type
| Expr (type : Ty) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

def ctx_limit (n : Nat) : JCtx → Prop
| [] => True
| x :: _ => x ≤ n

-- # Expression Continuations
inductive ContType : (tg : Tag) → JCtx → Ctx → List Cont → ContTypeRes tg → Prop
| IfCondK (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ : Ctx) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ s₁ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ s₂ (.Expr type) →
  ContType .Expr Δ₁ Γ₁ K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ (.ifCondK s₁ s₂ :: K) (.Expr .bool)
| DeclK (type : Ty) (Γ₁ : Ctx) :
  ContType .Stmt Δ₁ (type :: Γ₁) K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.declK type :: K) (.Expr type)
| AssignK (x : VarName) (type : Ty) (Γ₁ : Ctx) :
  (Γ₁(x) = type) →
  ContType .Stmt Δ₁ Γ₁ K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.assignK x :: K) (.Expr type)
| BinOpLK (Γ₁ : Ctx) (op : BinOp) (e₂ : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ e₂ (.Expr op.args.2) →
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK (Γ₁ : Ctx) (op : BinOp) (v₁ : Value) :
  value_type v₁ op.args.1 →
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK (Γ₁ : Ctx) (op : UnOp) :
  ContType .Expr Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ (.unopK op :: K) (.Expr op.args.1)
-- is this rule too strong now?
| LoopK (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ c (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ K (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ (.loopK c e Γ₁.length :: K) (.Expr .bool)
| LoopContK (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ c (.Expr .bool) →
  Typ .Expr (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ K (.Expr .unit) →
  ContType .Expr (Γ₁.length :: Δ₁) Γ₁ (.loopContK c e Γ₁.length :: K) (.Expr .unit)
| ScopeExitK (Γ₁ : Ctx) (n : Nat) (type : Ty) :
  ctx_limit n Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ (.scopeExitK n :: K) (.Expr type)
| ExprStmtK (Γ₁ : Ctx) (type : Ty) :
  ContType .Stmt Δ₁ Γ₁ K .Stmt →
  ContType .Expr Δ₁ Γ₁ (.exprStmtK :: K) (.Expr type)
-- # Statement Continuations
| HaltK (Γ₁ : Ctx) :
  ContType .Stmt Δ₁ Γ₁ [] .Stmt
| SeqK (Γ₁ : Ctx) (Γ₂ : Ctx) (s : Lang .Stmt) :
  Typ .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt Δ₁ Γ₂ K .Stmt →
  ContType .Stmt Δ₁ Γ₁ (.seqK s :: K) .Stmt
| ScopeBodyK (Γ₁ : Ctx) (e : Lang .Expr) (type : Ty) (n : Nat) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  ctx_limit n Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Stmt Δ₁ Γ₁ (.scopeBodyK e n :: K) .Stmt

inductive Coh : Environment → Ctx → Prop
| CohEmp :
  Coh [] []
| CohBind (v : Value) (type : Ty) :
  Coh E Γ →
  value_type v type →
  Coh (v :: E) (type :: Γ)

inductive JCoh : JStackCtx → Ctx → JCtx → Prop
| JCohEmp :
  JCoh [] Γ []
| JCohLoop (n : Nat) (Γ₁ : Ctx) (Δ₁ : JCtx) :
  n ≤ Γ₁.length →
  JCoh J (Γ₁.drop (Γ₁.length - n)) Δ₁ →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr .unit) →
  JCoh (⟨n, K⟩ :: J) Γ₁ (n :: Δ₁)

inductive Wt : CEK → Prop
| WtExprE (e : Lang .Expr) (type : Ty) :
  Coh E Γ →
  JCoh J Γ Δ →
  Typ .Expr Δ Γ e (.Expr type) →
  ContType .Expr Δ Γ K (.Expr type) →
  Wt ⟨.sourceExpr e, E, J, K⟩
| WtExprS (s : Lang .Stmt) :
  Coh E Γ →
  JCoh J Γ Δ →
  Typ .Stmt Δ Γ s (.Stmt Γ₁) →
  ContType .Stmt Δ Γ₁ K .Stmt →
  Wt ⟨.sourceStmt s, E, J, K⟩
| WtContV (v : Value) (type : Ty) :
  Coh E Γ →
  JCoh J Γ Δ →
  value_type v type →
  ContType .Expr Δ Γ K (.Expr type) →
  Wt ⟨.value v, E, J, K⟩
| WtContS :
  Coh E Γ →
  JCoh J Γ Δ →
  ContType .Stmt Δ Γ K .Stmt →
  Wt ⟨.skip, E, J, K⟩
