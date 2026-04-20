import Mathlib.Data.Finmap

abbrev VarName := Nat

def MethodName := Nat

def Addr := Nat
deriving Repr, DecidableEq, Inhabited

inductive Ty
| nat
| bool
| unit
| cls (n : Nat)
deriving Inhabited

inductive Value
| True
| False
| Nat (n : Nat)
| Addr (a : Addr)
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

structure UnOpArgs {c_cnt : Nat} where
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

def UnOp.args {c_cnt : Nat} : UnOp → UnOpArgs (c_cnt := c_cnt)
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
| Var (n : VarName) : Lang .Expr
| Field (f : Nat) (p : Lang .Expr) : Lang .Expr
| True : Lang .Expr
| False : Lang .Expr
| Nat (n : Nat) : Lang .Expr
| Unit : Lang .Expr
| BinOp (arg₁ : Lang .Expr) (arg₂ : Lang .Expr) (op : BinOp) : Lang .Expr
| UnOp (arg : Lang .Expr) (op : UnOp) : Lang .Expr
| New (cls : Nat) (args : Fin n → Lang .Expr) : Lang .Expr
| Call (m : Nat) (cls : Nat) (args : Fin n → Lang .Expr) : Lang .Expr
| Return (l : Nat) (e : Lang .Expr) : Lang .Expr
| If (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) : Lang .Expr
| While (cond : Lang .Expr) (body : Lang .Expr) : Lang .Expr
| Break (l : Nat) : Lang .Expr
| Scope (s : Lang .Stmt) (res : Lang .Expr) : Lang .Expr
-- # Stmt
| Decl (type : Ty) (e : Lang .Expr) : Lang .Stmt
| Assign (x : VarName) (e : Lang .Expr) : Lang .Stmt
| Seq (s₁ : Lang .Stmt) (s₂ : Lang .Stmt) : Lang .Stmt
| Do (e : Lang .Expr) : Lang .Stmt

/-
class signature:
finite type of field names and method names
mapping arities (whether they are static or not)

class implementation:
method name → body (Lang)

Lang depends on the class signature

Then parametrize Ty with class names (and lookup the actual types later in Lang from the signature)
-/
notation:100 s₁:100 ";" s₂:101 => Lang.Seq s₁ s₂
notation x "::=" exp => Lang.Assign x exp
abbrev Ctx := List Ty

abbrev JCtx := List Nat
notation Γ₁ "("x")" "=" type => x < List.length Γ₁ ∧ Γ₁[x]? = Option.some type

inductive TypR : Tag → Type
| Stmt (Γ₁ : Ctx) : TypR .Stmt
| Expr (type : Ty) : TypR .Expr

structure Method where
  nArg : Nat
  argTy : Fin nArg → Ty
  body : Lang .Expr
  ret : Ty

structure Defs (cCnt : Nat) where
  fieldsCnt : Fin cCnt → Nat
  fieldsTy : (cls : Fin cCnt) → (Fin (fieldsCnt cls)) → Ty
  methodsCnt : Fin cCnt → Nat
  methods : (cls : Fin cCnt) → (Fin (methodsCnt cls)) → Method

variable (cCnt : Nat) (defs : Defs cCnt)

inductive Typ :
  (tg : Tag) → (cCur : Fin cCnt) → (Fin (defs.methodsCnt cCur)) →
  JCtx → Ctx → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur)) :
  Typ .Expr cCur mCur Δ₁ Γ₁ .True (.Expr .bool)
| FalseConst
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur)) :
  Typ .Expr cCur mCur Δ₁ Γ₁ .False (.Expr .bool)
| NatConst
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (n : Nat) :
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Nat n) (.Expr .nat)
| UnitConst
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur)) :
  Typ .Expr cCur mCur Δ₁ Γ₁ .Unit (.Expr .unit)
| VarAccess
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (x : VarName) (type : Ty) :
  (Γ₁(x) = type) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Var x) (.Expr type)
| FieldAccess
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (n : Nat) (f : Nat) (p : Lang .Expr) :
  (hn : n < cCnt) →
  (hf : f < defs.fieldsCnt ⟨n, hn⟩) →
  Typ .Expr cCur mCur Δ₁ Γ₁ p (.Expr (.cls n)) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Field f p) (.Expr (defs.fieldsTy ⟨n, hn⟩ ⟨f, hf⟩))
| UnOp
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (arg : Lang .Expr) (op : UnOp) :
  Typ .Expr cCur mCur Δ₁ Γ₁ arg (.Expr op.args.1) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.UnOp arg op) (.Expr op.args.2)
| BinOp
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (arg₁ arg₂ : Lang .Expr) (op : BinOp) :
  Typ .Expr cCur mCur Δ₁ Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr cCur mCur Δ₁ Γ₁ arg₂ (.Expr op.args.2) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.BinOp arg₁ arg₂ op) (.Expr op.args.3)
| New
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cls : Nat) (hc : cls < cCnt) (args : Fin (defs.fieldsCnt ⟨cls, hc⟩) → Lang .Expr):
  ∀ i, Typ .Expr cCur mCur Δ₁ Γ₁ (args i) (.Expr (defs.fieldsTy ⟨cls, hc⟩ i)) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.New cls args) (.Expr (.cls cls))
| Call
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cls : Nat) (hc : cls < cCnt)
  (m : Nat) (hm : m < defs.methodsCnt ⟨cls, hc⟩)
  (args : Fin (defs.methods ⟨cls, hc⟩ ⟨m, hm⟩).nArg → Lang .Expr) (ret : Ty) :
  (defs.methods ⟨cls, hc⟩ ⟨m, hm⟩).ret = ret →
  ∀ i, Typ .Expr cCur mCur Δ₁ Γ₁ (args i) (.Expr ((defs.methods ⟨cls, hc⟩ ⟨m, hm⟩).argTy i)) →
  /-
  -- well typed part
  Typ .Expr ⟨cls, hc⟩ ⟨m, hm⟩
    [] (List.ofFn (defs.methods ⟨cls, hc⟩ ⟨m, hm⟩).argTy)
    (defs.methods ⟨cls, hc⟩ ⟨m, hm⟩).body (.Expr ret) →
  -/
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Call m cls args) (.Expr ret)
| Return (l : Nat)
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (type : Ty) :
  type = (defs.methods cCur mCur).ret →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Return l e) (.Expr type)
| IfExpr
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : Ty) :
  Typ .Expr cCur mCur Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr cCur mCur Δ₁ Γ₁ e₁ (.Expr type) →
  Typ .Expr cCur mCur Δ₁ Γ₁ e₂ (.Expr type) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr cCur mCur Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr cCur mCur (Γ₁.length :: Δ₁) Γ₁ body (.Expr .unit) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.While cond body) (.Expr .unit)
| BreakExpr
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (type : Ty) (l : Nat) :
  l < Δ₁.length →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Break l) (.Expr .unit)
| ScopeExpr
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (s : Lang .Stmt) (e : Lang .Expr) (type : Ty) :
  Typ .Stmt cCur mCur Δ₁ Γ₁ s (.Stmt Γ₂) →
  Typ .Expr cCur mCur Δ₁ Γ₂ e (.Expr type) →
  Typ .Expr cCur mCur Δ₁ Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (e : Lang .Expr) (type : Ty) :
  Typ .Expr cCur mCur Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt cCur mCur Δ₁ Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (x : VarName) (e : Lang .Expr) (type : Ty) :
  Typ .Expr cCur mCur Δ₁ Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt cCur mCur Δ₁ Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt cCur mCur Δ₁ Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt cCur mCur Δ₁ Γ₂ s₂ Γ₃ →
  Typ .Stmt cCur mCur Δ₁ Γ₁ (s₁; s₂) Γ₃
| Do
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (e : Lang .Expr) (type : Ty) :
  Typ .Expr cCur mCur Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt cCur mCur Δ₁ Γ₁ (.Do e) (.Stmt Γ₁)

section TypeProperties

def TypR.extL (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

end TypeProperties

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
| fieldK (f : Nat)
| ifCondK (e₁ e₂ : Lang .Expr)
| declK (type : Ty)
| returnK (l : Nat)
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
| argK (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (values : Fin sep → Value)
  (rems : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
| newK (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (values : Fin sep → Value)
  (rems : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
| callK (E : Environment)

abbrev JStackCtx (cCnt : Nat) (defs : Defs cCnt) := List (Nat × List (Cont cCnt defs))

variable (cCnt : Nat) (defs : Defs cCnt)

structure Object where
  cls : Fin cCnt
  values : Fin (defs.fieldsCnt cls) → Value

abbrev Map (val : Type) := Finmap (fun _ : Addr => val)

abbrev Store := Map (Object cCnt defs)

structure CEK where
  C : Control
  E : Environment
  J : JStackCtx cCnt defs
  S : Store cCnt defs
  K : List (Cont cCnt defs)
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

inductive liftValue : Value → Lang .Expr → Prop
| True : liftValue .True .True
| False : liftValue .False .False
| Nat (n : Nat) : liftValue (.Nat n) (.Nat n)
| Unit : liftValue .Unit .Unit

inductive ValueTyp : Value → Ty → (Store cCnt defs) → Prop
| True :
  ValueTyp .True .bool S
| False :
  ValueTyp .False .bool S
| Nat (n : Nat) :
  ValueTyp (.Nat n) .nat S
| Unit :
  ValueTyp .Unit .unit S
| Cls (cls : Fin cCnt) (a : Addr) (S : Store cCnt defs) (vls : Fin (defs.fieldsCnt cls) → Value) :
  S.lookup a = .some (⟨cls, vls⟩ : Object cCnt defs) →
  ∀ i, ValueTyp (vls i) (defs.fieldsTy cls i) S →
  ValueTyp (.Addr a) (.cls cls) S

inductive Eval : CEK cCnt defs → CEK cCnt defs → Prop
-- # Expr
| Val (v : Value) (e : Lang .Expr) :
  liftValue v e →
  Eval
    ⟨.sourceExpr e, E, J, S, K⟩
    ⟨.value v, E, J, S, K⟩
| Var (x : VarName) :
  Eval
    ⟨.sourceExpr (.Var x), E, J, S, K⟩
    ⟨.value (E[x]!), E, J, S, K⟩
| Field (f : Nat) (p : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.Field f p), E, J, S, K⟩
    ⟨.sourceExpr p, E, J, S, (.fieldK f) :: K⟩
| Return (e : Lang .Expr) (l : Nat) :
  Eval
    ⟨.sourceExpr (.Return l e), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, (.returnK l) :: K⟩
| VarDecl (type : Ty) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Decl type e), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, (.declK type) :: K⟩
| Assign (x : VarName) (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Assign x e), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, (.assignK x) :: K⟩
| Seq (s₁ s₂ : Lang .Stmt) :
  Eval
    ⟨.sourceStmt (.Seq s₁ s₂), E, J, S, K⟩
    ⟨.sourceStmt s₁, E, J, S, (.seqK s₂) :: K⟩
| ExprStmt (e : Lang .Expr) :
  Eval
    ⟨.sourceStmt (.Do e), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, .exprStmtK :: K⟩
| BinOp (e₁ e₂ : Lang .Expr) (op : BinOp) :
  Eval
    ⟨.sourceExpr (.BinOp e₁ e₂ op), E, J, S, K⟩
    ⟨.sourceExpr e₁, E, J, S, (.binopLK op e₂) :: K⟩
| UnOp (e : Lang .Expr) (op : UnOp) :
  Eval
    ⟨.sourceExpr (.UnOp e op), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, (.unopK op) :: K⟩
| If (e : Lang .Expr) (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.If e s₁ s₂), E, J, S, K⟩
    ⟨.sourceExpr e, E, J, S, (.ifCondK s₁ s₂) :: K⟩
| While (c : Lang .Expr) (body : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.While c body), E, J, S, K⟩
    ⟨.sourceExpr c, E, J, S, (.loopK c body E.length) :: K⟩
| Break (K' : List (Cont cCnt defs)) (l : Nat):
  Eval
    ⟨.sourceExpr (.Break l), E, J, S, K⟩
    ⟨.value .Unit, E.drop (E.length - J[l]!.1), J.drop (l + 1), S, J[l]!.2⟩
| Scope (s : Lang .Stmt) (e : Lang .Expr) :
  Eval
    ⟨.sourceExpr (.Scope s e), E, J, S, K⟩
    ⟨.sourceStmt s, E, J, S, .scopeBodyK e E.length :: K⟩
| Call₀ (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (args : Fin (defs.methods cls m).nArg → Lang .Expr) :
  (0 = (defs.methods cls m).nArg) →
  Eval
    ⟨.sourceExpr (.Call m cls args), E, J, S, K⟩
    ⟨.sourceExpr (defs.methods cls m).body, [], ⟨E.length, K⟩ :: J, S,
      (.callK E) :: K⟩
| Call (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (args : Fin (defs.methods cls m).nArg → Lang .Expr) :
  (hn : 0 < (defs.methods cls m).nArg) →
  Eval
    ⟨.sourceExpr (.Call m cls args), E, J, S, K⟩
    ⟨.sourceExpr (args ⟨0, hn⟩), E, J, S,
      (.argK cls m ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩)) :: K⟩
| New₀ (cls : Fin cCnt) (a : Addr)
  (args : Fin (defs.fieldsCnt cls) → Lang .Expr) :
  (h0 : 0 = defs.fieldsCnt cls) →
  (ha : a ∉ S) →
  Eval
    ⟨.sourceExpr (.New cls args), E, J, S, K⟩
    ⟨.value (.Addr a), E, J, S.insert a ⟨cls, fun _ => by grind [Fin]⟩, K⟩
| New (cls : Fin cCnt)
  (args : Fin (defs.fieldsCnt cls) → Lang .Expr) :
  (hn : 0 < defs.fieldsCnt cls) →
  Eval
    ⟨.sourceExpr (.Call m cls args), E, J, S, K⟩
    ⟨.sourceExpr (args ⟨0, hn⟩), E, J, S,
      (.newK cls ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩)) :: K⟩
-- # Cont
| FieldDone (a : Addr) (cls : Fin cCnt) (k : Fin (defs.fieldsCnt cls))
  (values : Fin (defs.fieldsCnt cls) → Value) :
  S.lookup a = some ⟨cls, values⟩ →
  Eval
    ⟨.value (.Addr a), E, J, S, (.fieldK k) :: K⟩
    ⟨.value (values k), E, J, S, K⟩
| IfTrue (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .True, E, J, S, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₁, E, J, S, K⟩
| IfFalse (s₁ s₂ : Lang .Expr) :
  Eval
    ⟨.value .False, E, J, S, .ifCondK s₁ s₂ :: K⟩
    ⟨.sourceExpr s₂, E, J, S, K⟩
| ReturnDone (v : Value) (l : Nat) :
  Eval
    ⟨.value v, E, J, S, (.returnK l) :: K⟩
    ⟨.value v, E.drop (E.length - J[l]!.1), J.drop (l + 1), S, J[l]!.2⟩
| VarDeclDone (type : Ty) (v : Value) :
  Eval
    ⟨.value v, E, J, S, .declK type :: K⟩
    ⟨.skip, v :: E, J, S, K⟩
| AssignDone (x : VarName) (v : Value) :
  Eval
    ⟨.value v, E, J, S, .assignK x :: K⟩
    ⟨.skip, E.set x v, J, S, K⟩
| SeqDone (s₂ : Lang .Stmt) :
  Eval
    ⟨.skip, E, J, S, .seqK s₂ :: K⟩
    ⟨.sourceStmt s₂, E, J, S, K⟩
| ExprStmtDone (v : Value) :
  Eval
    ⟨.value v, E, J, S, .exprStmtK :: K⟩
    ⟨.skip, E, J, S, K⟩
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr) :
  Eval
    ⟨.value v₁, E, J, S, .binopLK op e₂ :: K⟩
    ⟨.sourceExpr e₂, E, J, S, .binopRK op v₁ :: K⟩
| BinOpR (op : BinOp) (v₁ v₂ result : Value) :
  op.step v₁ v₂ result →
  Eval
    ⟨.value v₂, E, J, S, .binopRK op v₁ :: K⟩
    ⟨.value result, E, J, S, K⟩
| UnOpDone (op : UnOp) (v result : Value) :
  op.step v result →
  Eval
    ⟨.value v, E, J, S, .unopK op :: K⟩
    ⟨.value result, E, J, S, K⟩
| LoopTrue (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .True, E, J, S, .loopK c body n :: K⟩
    ⟨.sourceExpr body, E, ⟨n, K⟩ :: J, S, .loopContK c body n :: K⟩
| LoopFalse (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval
    ⟨.value .False, E, J, S, .loopK c body n :: K⟩
    ⟨.value .Unit, E.drop (E.length - n), J, S, K⟩
| LoopCont (body : Lang .Expr) (c : Lang .Expr) (n : Nat) (K' : List (Cont cCnt defs)) :
  Eval
    ⟨.value .Unit, E, ⟨n, K⟩ :: J, S, .loopContK c body n :: K'⟩
    ⟨.sourceExpr c, E, J, S, .loopK c body n :: K⟩
| ScopeBody (body : Lang .Expr) (n : Nat) :
  Eval
    ⟨.skip, E, J, S, .scopeBodyK body n :: K⟩
    ⟨.sourceExpr body, E, J, S, .scopeExitK n :: K⟩
| ScopeExit (body : Lang .Expr) (n : Nat) (v : Value) :
  Eval
    ⟨.value v, E, J, S, .scopeExitK n :: K⟩
    ⟨.value v, E.drop (E.length - n), J, S, K⟩
| ArgNext (body : Lang .Expr)
  (v : Value) (e : Lang .Expr)
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (hn : sep + 1 < (defs.methods cls m).nArg) :
  Eval
    ⟨.value v, E, J, S, .argK cls m sep vals exprs :: K⟩
    ⟨.sourceExpr e, E, J, S,
      .argK cls m ⟨sep + 1, hn⟩
      (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
      (fun i => exprs ⟨i + 1, by grind⟩) :: K⟩
| ArgDone
  (v : Value)
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (hn : sep + 1 = (defs.methods cls m).nArg) :
  Eval
    ⟨.value v, E, J, S, .argK cls m sep vals exprs :: K⟩
    ⟨.sourceExpr (defs.methods cls m).body,
      List.ofFn (fun i => if hs : i = sep then v else vals ⟨i, by grind⟩),
      J, S, .callK E :: K⟩
| NewNext
  (v : Value) (e : Lang .Expr)
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (hn : sep + 1 < defs.fieldsCnt cls) :
  Eval
    ⟨.value v, E, J, S, .newK cls sep vals exprs :: K⟩
    ⟨.sourceExpr e, E, J, S,
      .newK cls ⟨sep + 1, hn⟩
      (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
      (fun i => exprs ⟨i + 1, by grind⟩) :: K⟩
| NewDone
  (v : Value)
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (hn : sep + 1 = defs.fieldsCnt cls) (a : Addr) (ha : a ∉ S) :
  Eval
    ⟨.value v, E, J, S, .newK cls sep vals exprs :: K⟩
    ⟨.value (.Addr a), E, J,
      S.insert a ⟨cls, (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)⟩,
      .callK E :: K⟩



def initState (s : Lang .Stmt) : CEK cCnt defs := ⟨.sourceStmt s, [], [], ∅, []⟩

def terminalState (E : Environment) (J : JStackCtx cCnt defs) (S : Store cCnt defs) :
  CEK cCnt defs := ⟨.skip, E, J, S, []⟩

inductive ContTypeRes : Tag → Type
| Expr (type : Ty) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

def ctx_limit (n : Nat) : JCtx → Prop
| [] => True
| x :: _ => x ≤ n

inductive Coh : Environment → (Store cCnt defs) → Ctx → Prop
| CohEmp :
  Coh [] S []
| CohBind (v : Value) (type : Ty) :
  Coh E S Γ →
  ValueTyp cCnt defs v type S →
  Coh (v :: E) S (type :: Γ)

-- # Expression Continuations
inductive ContType : (tg : Tag) →
  (cCur : Fin cCnt) → (Fin (defs.methodsCnt cCur)) →
  JCtx → Ctx → List (Cont cCnt defs) → ContTypeRes tg → Prop
| IfCondK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ : Ctx) (type : Ty) :
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ s₁ (.Expr type) →
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ s₂ (.Expr type) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr type) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.ifCondK s₁ s₂ :: K) (.Expr .bool)
| DeclK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (type : Ty) (Γ₁ : Ctx) :
  ContType .Stmt cCur mCur Δ₁ (type :: Γ₁) K .Stmt →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.declK type :: K) (.Expr type)
| AssignK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (x : VarName) (type : Ty) (Γ₁ : Ctx) :
  (Γ₁(x) = type) →
  ContType .Stmt cCur mCur Δ₁ Γ₁ K .Stmt →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.assignK x :: K) (.Expr type)
| BinOpLK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (op : BinOp) (e₂ : Lang .Expr) :
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ e₂ (.Expr op.args.2) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (op : BinOp) (v₁ : Value) :
  value_type v₁ op.args.1 →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (op : UnOp) :
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr op.args.out) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.unopK op :: K) (.Expr op.args.1)
| ReturnK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur)) :
  ContType .Expr cCur mCur Δ₁ Γ₁ (.returnK l :: K) (.Expr (defs.methods cCur mCur).ret)
| FieldK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cls : Fin cCnt) (ty : Ty) (f : Fin (defs.fieldsCnt cls)) :
  defs.fieldsTy cls f = ty →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr ty) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.fieldK f :: K) (.Expr (.cls cls))
| ArgK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg) (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (retTy : Ty) (tyRes : Ty) :
  retTy = (defs.methods cls m).ret →
  tyRes = (defs.methods cls m).argTy sep →
  /- do we even need this?
  (∀ i,
    ValueTyp cCnt defs (vals i) ((defs.methods cls m).argTy ⟨i, by omega⟩) S) →-/
  (∀ i,
    Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁
      (exprs i)
      (.Expr ((defs.methods cls m).argTy ⟨i + sep + 1, by omega⟩))) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr retTy) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.argK cls m sep vals exprs :: K) (.Expr tyRes)
| NewK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls)) (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (retTy : Ty) (tyRes : Ty) :
  retTy = .cls cls →
  tyRes = (defs.fieldsTy cls sep) →
  /- do we even need this?
  (∀ i,
    ValueTyp cCnt defs (vals i) (defs.fieldsTy cls ⟨i, by omega⟩) S) →-/
  (∀ i,
    Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁
      (exprs i)
      (.Expr (defs.fieldsTy cls ⟨i + sep + 1, by omega⟩))) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr retTy) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.newK cls sep vals exprs :: K) (.Expr tyRes)
| LoopK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ c (.Expr .bool) →
  Typ cCnt defs .Expr cCur mCur (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr .unit) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.loopK c e Γ₁.length :: K) (.Expr .bool)
| LoopContK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ c (.Expr .bool) →
  Typ cCnt defs .Expr cCur mCur (Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr cCur mCur Δ₁ Γ₁ K (.Expr .unit) →
  ContType .Expr cCur mCur (Γ₁.length :: Δ₁) Γ₁ (.loopContK c e Γ₁.length :: K) (.Expr .unit)
| ScopeExitK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (n : Nat) (type : Ty) :
  ctx_limit n Δ₁ →
  ContType .Expr cCur mCur Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.scopeExitK n :: K) (.Expr type)
| ExprStmtK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (type : Ty) :
  ContType .Stmt cCur mCur Δ₁ Γ₁ K .Stmt →
  ContType .Expr cCur mCur Δ₁ Γ₁ (.exprStmtK :: K) (.Expr type)
-- # Statement Continuations
| HaltK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) :
  ContType .Stmt cCur mCur Δ₁ Γ₁ [] .Stmt
| SeqK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (Γ₂ : Ctx) (s : Lang .Stmt) :
  Typ cCnt defs .Stmt cCur mCur Δ₁ Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt cCur mCur Δ₁ Γ₂ K .Stmt →
  ContType .Stmt cCur mCur Δ₁ Γ₁ (.seqK s :: K) .Stmt
| ScopeBodyK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Γ₁ : Ctx) (e : Lang .Expr) (type : Ty) (n : Nat) :
  Typ cCnt defs .Expr cCur mCur Δ₁ Γ₁ e (.Expr type) →
  ctx_limit n Δ₁ →
  ContType .Expr cCur mCur Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr type) →
  ContType .Stmt cCur mCur Δ₁ Γ₁ (.scopeBodyK e n :: K) .Stmt
| CallK
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (Δ' : JCtx) (Γ' : Ctx) (ty : Ty) :
  -- add which type is returned?
  Coh cCnt defs E S Γ' →
  ContType .Expr cCur mCur Δ' Γ' K (.Expr ty) →
  ContType .Stmt cCur mCur Δ₁ Γ₁ (.callK E :: K) .Stmt

inductive JCoh : JStackCtx cCnt defs → Ctx → JCtx → Prop
| JCohEmp :
  JCoh [] Γ []
| JCohLoop
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (n : Nat) (Γ₁ : Ctx) (Δ₁ : JCtx) :
  n ≤ Γ₁.length →
  JCoh J (Γ₁.drop (Γ₁.length - n)) Δ₁ →
  ContType cCnt defs .Expr cCur mCur Δ₁ (Γ₁.drop (Γ₁.length - n)) K (.Expr .unit) →
  JCoh (⟨n, K⟩ :: J) Γ₁ (n :: Δ₁)

def S_ok (S : Store cCnt defs) : Prop :=
  ∀ obj ∈ S.entries, (ValueTyp cCnt defs (.Addr obj.1) (.cls obj.2.cls) S)

def defs_ok : Prop :=
  ∀ cls m,
    Typ cCnt defs .Expr cls m []
      (List.ofFn (defs.methods cls m).argTy)
      (defs.methods cls m).body
      (.Expr (defs.methods cls m).ret)

inductive Wt : CEK cCnt defs → Prop
| WtExprE
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (e : Lang .Expr) (type : Ty) :
  Coh cCnt defs E S Γ →
  JCoh cCnt defs J Γ Δ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  Typ cCnt defs .Expr cCur mCur Δ Γ e (.Expr type) →
  ContType cCnt defs .Expr cCur mCur Δ Γ K (.Expr type) →
  Wt ⟨.sourceExpr e, E, J, S, K⟩
| WtExprS
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (s : Lang .Stmt) :
  Coh cCnt defs E S Γ →
  JCoh cCnt defs J Γ Δ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  Typ cCnt defs .Stmt cCur mCur Δ Γ s (.Stmt Γ₁) →
  ContType cCnt defs .Stmt cCur mCur Δ Γ₁ K .Stmt →
  Wt ⟨.sourceStmt s, E, J, S, K⟩
| WtContV
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur))
  (v : Value) (type : Ty) :
  Coh cCnt defs E S Γ →
  JCoh cCnt defs J Γ Δ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  ValueTyp cCnt defs v type S →
  ContType cCnt defs .Expr cCur mCur Δ Γ K (.Expr type) →
  Wt ⟨.value v, E, J, S, K⟩
| WtContS
  (cCur : Fin cCnt) (mCur : Fin (defs.methodsCnt cCur)) :
  Coh cCnt defs E S Γ →
  JCoh cCnt defs J Γ Δ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  ContType cCnt defs .Stmt cCur mCur Δ Γ K .Stmt →
  Wt ⟨.skip, E, J, S, K⟩
