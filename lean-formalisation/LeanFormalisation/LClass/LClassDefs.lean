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
| Return (e : Lang .Expr) (l : Nat) : Lang .Expr
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

inductive JumpFrame
| Loop (n : Nat)
| Method (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
deriving Inhabited

abbrev JCtx := List (JumpFrame cCnt defs)

inductive LoopJump : JCtx cCnt defs → Nat → Prop
| LoopBase (n : Nat) :
  LoopJump (.Loop n :: Δ) 0
| Loop (n : Nat) (l : Nat) :
  LoopJump Δ (l - 1) →
  LoopJump (.Loop n :: Δ) l

inductive Typ :
  (tg : Tag) →
  JCtx cCnt defs → Ctx → Lang tg → TypR tg → Prop
-- # Expr
| TrueConst :
  Typ .Expr Δ₁ Γ₁ .True (.Expr .bool)
| FalseConst :
  Typ .Expr Δ₁ Γ₁ .False (.Expr .bool)
| NatConst
  (n : Nat) :
  Typ .Expr Δ₁ Γ₁ (.Nat n) (.Expr .nat)
| UnitConst :
  Typ .Expr Δ₁ Γ₁ .Unit (.Expr .unit)
| VarAccess
  (x : VarName) (type : Ty) :
  (Γ₁(x) = type) →
  Typ .Expr Δ₁ Γ₁ (.Var x) (.Expr type)
| FieldAccess
  (n : Nat) (f : Nat) (p : Lang .Expr) (ty : Ty) :
  (hn : n < cCnt) →
  (hf : f < defs.fieldsCnt ⟨n, hn⟩) →
  Typ .Expr Δ₁ Γ₁ p (.Expr (.cls n)) →
  ty = (defs.fieldsTy ⟨n, hn⟩ ⟨f, hf⟩) →
  Typ .Expr Δ₁ Γ₁ (.Field f p) (.Expr ty)
| UnOp
  (arg : Lang .Expr) (op : UnOp) (ty : Ty) :
  Typ .Expr Δ₁ Γ₁ arg (.Expr op.args.1) →
  ty = op.args.2 →
  Typ .Expr Δ₁ Γ₁ (.UnOp arg op) (.Expr ty)
| BinOp
  (arg₁ arg₂ : Lang .Expr) (op : BinOp) (ty : Ty) :
  Typ .Expr Δ₁ Γ₁ arg₁ (.Expr op.args.1) →
  Typ .Expr Δ₁ Γ₁ arg₂ (.Expr op.args.2) →
  ty = op.args.3 →
  Typ .Expr Δ₁ Γ₁ (.BinOp arg₁ arg₂ op) (.Expr ty)
| New
  (cls : Nat) (hc : cls < cCnt)
  (narg : Nat) (harg : narg = defs.fieldsCnt ⟨cls, hc⟩)
  (args : Fin narg → Lang .Expr) :
  (∀ i, Typ .Expr Δ₁ Γ₁ (args i) (.Expr (defs.fieldsTy ⟨cls, hc⟩ ⟨i, by omega⟩))) →
  Typ .Expr Δ₁ Γ₁ (.New cls args) (.Expr (.cls cls))
| Call
  (cls : Nat) (hcls : cls < cCnt)
  (m : Nat) (hm : m < defs.methodsCnt ⟨cls, hcls⟩)
  (narg : Nat) (harg : (defs.methods ⟨cls, hcls⟩ ⟨m, hm⟩).nArg = narg)
  (args : Fin narg → Lang .Expr) (ret : Ty) :
  (defs.methods ⟨cls, hcls⟩ ⟨m, hm⟩).ret = ret →
  (∀ i,
    Typ .Expr Δ₁ Γ₁ (args i)
      (.Expr ((defs.methods ⟨cls, hcls⟩ ⟨m, hm⟩).argTy ⟨i, by omega⟩))) →
  Typ .Expr Δ₁ Γ₁ (.Call m cls args) (.Expr ret)
| Return (e : Lang .Expr) (l : Nat) (type : Ty)
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls)) :
  (hl : l < Δ₁.length) →
  Δ₁[l]! = .Method cls m →
  (l = 0 ∨ LoopJump cCnt defs Δ₁ (l - 1)) →
  Typ .Expr Δ₁ Γ₁ e (.Expr (defs.methods cls m).ret) →
  Typ .Expr Δ₁ Γ₁ (.Return e l) (.Expr type)
| IfExpr
  (cond : Lang .Expr) (e₁ : Lang .Expr) (e₂ : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr Δ₁ Γ₁ e₁ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ e₂ (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.If cond e₁ e₂) (.Expr type)
| WhileExpr
  (cond : Lang .Expr) (body : Lang .Expr) :
  Typ .Expr Δ₁ Γ₁ cond (.Expr .bool) →
  Typ .Expr (.Loop Γ₁.length :: Δ₁) Γ₁ body (.Expr .unit) →
  Typ .Expr Δ₁ Γ₁ (.While cond body) (.Expr .unit)
| BreakExpr
  (type : Ty) (l : Nat) :
  LoopJump cCnt defs Δ₁ l →
  Typ .Expr Δ₁ Γ₁ (.Break l) (.Expr type)
| ScopeExpr
  (s : Lang .Stmt) (e : Lang .Expr) (type : Ty) :
  Typ .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  Typ .Expr Δ₁ Γ₂ e (.Expr type) →
  Typ .Expr Δ₁ Γ₁ (.Scope s e) (.Expr type)
-- # Stmt
| VarDecl
  (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Decl type e) (.Stmt (type :: Γ₁))
| VarAssign
  (x : VarName) (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) → (Γ₁(x) = type) →
  Typ .Stmt Δ₁ Γ₁ (.Assign x e) (.Stmt Γ₁)
| Seq
  (s₁ s₂ : Lang .Stmt) :
  Typ .Stmt Δ₁ Γ₁ s₁ (.Stmt Γ₂) →
  Typ .Stmt Δ₁ Γ₂ s₂ Γ₃ →
  Typ .Stmt Δ₁ Γ₁ (s₁; s₂) Γ₃
| Do
  (e : Lang .Expr) (type : Ty) :
  Typ .Expr Δ₁ Γ₁ e (.Expr type) →
  Typ .Stmt Δ₁ Γ₁ (.Do e) (.Stmt Γ₁)

section TypeProperties

def TypR.extL (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₁ ++ Γ₂)

def TypR.extR (Γ₁ : Ctx) (tg : Tag) : TypR tg → TypR tg
| .Expr type => .Expr type
| .Stmt Γ₂ => .Stmt (Γ₂ ++ Γ₁)

end TypeProperties

inductive simpleType : Value → Ty → Prop
| True : simpleType .True .bool
| False : simpleType .False .bool
| Nat (n : Nat) : simpleType (.Nat n) .nat
| Unit : simpleType .Unit .unit

inductive Res
| value (v : Value)
| skip

abbrev Environment := List Value

inductive Cont
| fieldK (f : Nat)
| ifCondK (e₁ e₂ : Lang .Expr)
| declK (type : Ty)
| assignK (x : VarName)
| seqK (s : Lang .Stmt)
| exprStmtK
| binopLK (op : BinOp) (e₂ : Lang .Expr)
| binopRK (op : BinOp) (v : Value)
| unopK (op : UnOp)
| loopK (c : Lang .Expr) (body : Lang .Expr)
| loopContK (c : Lang .Expr) (body : Lang .Expr) (n : Nat) (J : List (List Cont))
| scopeBodyK (e : Lang .Expr) (n : Nat) (J : List (List Cont))
| scopeExitK (n : Nat) (J : List (List Cont))
| returnJumpK (l : Nat)
| argK (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (values : Fin sep → Value)
  (rems : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
| newK (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (values : Fin sep → Value)
  (rems : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
| breakRestoreK (n : Nat) (J : List (List Cont))
| returnRestoreK (E : Environment) (J : List (List Cont))
| callRestoreK (E : Environment) (J : List (List Cont))
deriving Inhabited

abbrev JStackCtx (cCnt : Nat) (defs : Defs cCnt) :=
  List (List (Cont cCnt defs))

variable (cCnt : Nat) (defs : Defs cCnt)

structure Object where
  cls : Fin cCnt
  values : Fin (defs.fieldsCnt cls) → Value

abbrev Map (val : Type) := Finmap (fun _ : Addr => val)

abbrev Store := Map (Object cCnt defs)

inductive EvalMode
| Eval
| Cont


inductive CEK : EvalMode → Type
| Eval
  (tg : Tag)
  (C : Lang tg)
  (E : Environment)
  (J : JStackCtx cCnt defs)
  (S : Store cCnt defs)
  (K : List (Cont cCnt defs)) : CEK .Eval
| Cont
  (res : Res)
  (E : Environment)
  (J : JStackCtx cCnt defs)
  (S : Store cCnt defs)
  (K : List (Cont cCnt defs)) : CEK .Cont

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
| Cls (cls : Fin cCnt)
  (cls_tp : Nat)
  (a : Addr) (S : Store cCnt defs) (vls : Fin (defs.fieldsCnt cls) → Value) :
  S.lookup a = .some (⟨cls, vls⟩ : Object cCnt defs) →
  (∀ i, ValueTyp (vls i) (defs.fieldsTy cls i) S) →
  cls_tp = cls.val →
  ValueTyp (.Addr a) (.cls cls_tp) S

inductive Eval : (m₁ : EvalMode) → (m₂ : EvalMode) → CEK cCnt defs m₁ → CEK cCnt defs m₂ → Prop
-- # Expr
| Val (v : Value) (e : Lang .Expr) :
  liftValue v e →
  Eval .Eval .Cont
    (.Eval .Expr e E J S K)
    (.Cont (.value v) E J S K)
| Var (x : VarName) :
  Eval .Eval .Cont
    (.Eval .Expr (.Var x) E J S K)
    (.Cont (.value (E[x]!)) E J S K)
| Field (f : Nat) (p : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Expr (.Field f p) E J S K)
    (.Eval .Expr p E J S ((.fieldK f) :: K))
| VarDecl (type : Ty) (e : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Stmt (.Decl type e) E J S K)
    (.Eval .Expr e E J S ((.declK type) :: K))
| Assign (x : VarName) (e : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Stmt (.Assign x e) E J S K)
    (.Eval .Expr e E J S ((.assignK x) :: K))
| Seq (s₁ s₂ : Lang .Stmt) :
  Eval .Eval .Eval
    (.Eval .Stmt (.Seq s₁ s₂) E J S K)
    (.Eval .Stmt s₁ E J S ((.seqK s₂) :: K))
| ExprStmt (e : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Stmt (.Do e) E J S K)
    (.Eval .Expr e E J S (.exprStmtK :: K))
| BinOp (e₁ e₂ : Lang .Expr) (op : BinOp) :
  Eval .Eval .Eval
    (.Eval .Expr (.BinOp e₁ e₂ op) E J S K)
    (.Eval .Expr e₁ E J S ((.binopLK op e₂) :: K))
| UnOp (e : Lang .Expr) (op : UnOp) :
  Eval .Eval .Eval
    (.Eval .Expr (.UnOp e op) E J S K)
    (.Eval .Expr e E J S ((.unopK op) :: K))
| If (e : Lang .Expr) (s₁ s₂ : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Expr (.If e s₁ s₂) E J S K)
    (.Eval .Expr e E J S ((.ifCondK s₁ s₂) :: K))
| While (c : Lang .Expr) (body : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Expr (.While c body) E J S K)
    (.Eval .Expr c E J S ((.loopK c body) :: K))
| Break (l : Nat) :
  Eval .Eval .Cont
    (.Eval .Expr (.Break l) E J S K)
    (.Cont (.value .Unit) E J S J[l]!)
| Scope (s : Lang .Stmt) (e : Lang .Expr) :
  Eval .Eval .Eval
    (.Eval .Expr (.Scope s e) E J S K)
    (.Eval .Stmt s E J S (.scopeBodyK e E.length J :: K))
| Return (e : Lang .Expr):
  Eval .Eval .Eval
    (.Eval .Expr (.Return e l) E J S K)
    (.Eval .Expr e E J S (.returnJumpK l :: K))
| Call₀ (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (args : Fin (defs.methods cls m).nArg → Lang .Expr) :
  (0 = (defs.methods cls m).nArg) →
  Eval .Eval .Eval
    (.Eval .Expr (.Call m cls args) E J S K)
    (.Eval .Expr (defs.methods cls m).body [] [.returnRestoreK E J :: K] S (.callRestoreK E J :: K))
| Call (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (args : Fin (defs.methods cls m).nArg → Lang .Expr) :
  (hn : 0 < (defs.methods cls m).nArg) →
  Eval .Eval .Eval
    (.Eval .Expr (.Call m cls args) E J S K)
    (.Eval .Expr (args ⟨0, hn⟩) E J S
      ((.argK cls m ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩)) :: K))
| New₀ (cls : Fin cCnt) (a : Addr)
  (args : Fin (defs.fieldsCnt cls) → Lang .Expr) :
  (h0 : 0 = defs.fieldsCnt cls) →
  (ha : a ∉ S) →
  Eval .Eval .Cont
    (.Eval .Expr (.New cls args) E J S K)
    (.Cont (.value (.Addr a)) E J (S.insert a ⟨cls, fun _ => by grind [Fin]⟩) K)
| New (cls : Fin cCnt)
  (args : Fin (defs.fieldsCnt cls) → Lang .Expr) :
  (hn : 0 < defs.fieldsCnt cls) →
  Eval .Eval .Eval
    (.Eval .Expr (.New cls args) E J S K)
    (.Eval .Expr (args ⟨0, hn⟩) E J S
      ((.newK cls ⟨0, hn⟩ (fun x => by grind [Fin]) (fun i => args ⟨i + 1, by grind⟩)) :: K))
-- # Cont
| FieldDone (a : Addr) (cls : Fin cCnt) (k : Fin (defs.fieldsCnt cls))
  (values : Fin (defs.fieldsCnt cls) → Value) :
  S.lookup a = some ⟨cls, values⟩ →
  Eval .Cont .Cont
    (.Cont (.value (.Addr a)) E J S ((.fieldK k) :: K))
    (.Cont (.value (values k)) E J S K)
| VarDeclDone (type : Ty) (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.declK type :: K))
    (.Cont .skip (v :: E) J S K)
| AssignDone (x : VarName) (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.assignK x :: K))
    (.Cont .skip (E.set x v) J S K)
| SeqDone (s₂ : Lang .Stmt) :
  Eval .Cont .Eval
    (.Cont .skip E J S (.seqK s₂ :: K))
    (.Eval .Stmt s₂ E J S K)
| ExprStmtDone (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.exprStmtK :: K))
    (.Cont .skip E J S K)
| BinOpL (op : BinOp) (v₁ : Value) (e₂ : Lang .Expr) :
  Eval .Cont .Eval
    (.Cont (.value v₁) E J S (.binopLK op e₂ :: K))
    (.Eval .Expr e₂ E J S (.binopRK op v₁ :: K))
| BinOpR (op : BinOp) (v₁ v₂ result : Value) :
  op.step v₁ v₂ result →
  Eval .Cont .Cont
    (.Cont (.value v₂) E J S (.binopRK op v₁ :: K))
    (.Cont (.value result) E J S K)
| UnOpDone (op : UnOp) (v result : Value) :
  op.step v result →
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.unopK op :: K))
    (.Cont (.value result) E J S K)
| IfTrue (s₁ s₂ : Lang .Expr) :
  Eval .Cont .Eval
    (.Cont (.value .True) E J S (.ifCondK s₁ s₂ :: K))
    (.Eval .Expr s₁ E J S K)
| IfFalse (s₁ s₂ : Lang .Expr) :
  Eval .Cont .Eval
    (.Cont (.value .False) E J S (.ifCondK s₁ s₂ :: K))
    (.Eval .Expr s₂ E J S K)
| LoopTrue (body : Lang .Expr) (c : Lang .Expr) :
  Eval .Cont .Eval
    (.Cont (.value .True) E J S (.loopK c body :: K))
    (.Eval .Expr body E ((.breakRestoreK E.length J :: K) :: J) S (.loopContK c body E.length J :: K))
| LoopFalse (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval .Cont .Cont
    (.Cont (.value .False) E J S (.loopK c body :: K))
    (.Cont (.value .Unit) E J S K)
| LoopCont (body : Lang .Expr) (c : Lang .Expr) (n : Nat) :
  Eval .Cont .Eval
    (.Cont (.value .Unit) E J S (.loopContK c body n J₀ :: K))
    (.Eval .Expr c (E.drop (E.length - n)) J₀ S (.loopK c body :: K))
| BreakRestore :
  Eval .Cont .Cont
    (.Cont (.value .Unit) E J S (.breakRestoreK n J₀ :: K))
    (.Cont (.value .Unit) (E.drop (E.length - n)) J₀ S K)
| ScopeBody (body : Lang .Expr) (n : Nat) :
  Eval .Cont .Eval
    (.Cont .skip E J S (.scopeBodyK body n J₀ :: K))
    (.Eval .Expr body E J S (.scopeExitK n J₀ :: K))
| ScopeExit (n : Nat) (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.scopeExitK n J₀ :: K))
    (.Cont (.value v) (E.drop (E.length - n)) J₀ S K)
| ReturnJump (v : Value) (l : Nat) :
  J[l]! = K' →
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.returnJumpK l :: K))
    (.Cont (.value v) E J S K')
| ReturnRestore (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.returnRestoreK E₀ J₀ :: K))
    (.Cont (.value v) E₀ J₀ S K)
| ArgNext
  (v : Value)
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (hn : sep + 1 < (defs.methods cls m).nArg) :
  Eval .Cont .Eval
    (.Cont (.value v) E J S (.argK cls m sep vals exprs :: K))
    (.Eval .Expr (exprs ⟨0, by omega⟩) E J S
      (.argK cls m ⟨sep + 1, hn⟩
        (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
        (fun i => exprs ⟨i + 1, by grind⟩) :: K))
| ArgDone
  (v : Value)
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg)
  (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (hn : sep + 1 = (defs.methods cls m).nArg) :
  Eval .Cont .Eval
    (.Cont (.value v) E J S (.argK cls m sep vals exprs :: K))
    (.Eval .Expr (defs.methods cls m).body
      (List.ofFn (fun i => if hs : i = sep then v else vals ⟨i, by grind⟩))
      ([.returnRestoreK E J :: K]) S (.callRestoreK E J :: K))
| CallRestore (v : Value) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.callRestoreK E₀ J₀ :: K))
    (.Cont (.value v) E₀ J₀ S K)
| NewNext
  (v : Value)
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (hn : sep + 1 < defs.fieldsCnt cls) :
  Eval .Cont .Eval
    (.Cont (.value v) E J S (.newK cls sep vals exprs :: K))
    (.Eval .Expr (exprs ⟨0, by omega⟩) E J S
      (.newK cls ⟨sep + 1, hn⟩
        (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)
        (fun i => exprs ⟨i + 1, by grind⟩) :: K))
| NewDone
  (v : Value)
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls))
  (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (hn : sep + 1 = defs.fieldsCnt cls) (a : Addr) (ha : a ∉ S) :
  Eval .Cont .Cont
    (.Cont (.value v) E J S (.newK cls sep vals exprs :: K))
    (.Cont (.value (.Addr a)) E J
      (S.insert a ⟨cls, (fun i => if hs : i.val = sep.val then v else vals ⟨i, by grind⟩)⟩)
      K)



def initState (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls)) : CEK cCnt defs .Eval :=
  .Eval .Expr (defs.methods cls m).body [] [] ∅ []

def terminalState :
  CEK cCnt defs m → Prop
| .Cont (.value _) _ _ S [] => True
| _ => False

inductive ContTypeRes : Tag → Type
| Expr (type : Ty) : ContTypeRes .Expr
| Stmt : ContTypeRes .Stmt

def ctx_limit (n : Nat) : JCtx cCnt defs → Prop
| [] => True
| .Loop x :: _ => x ≤ n
| _ => True

inductive Coh : Environment → (Store cCnt defs) → Ctx → Prop
| CohEmp :
  Coh [] S []
| CohBind (v : Value) (type : Ty) :
  Coh E S Γ →
  ValueTyp cCnt defs v type S →
  Coh (v :: E) S (type :: Γ)

-- # Expression Continuations
inductive ContType : (tg : Tag) →
  JCtx cCnt defs → Ctx → Store cCnt defs → List (Cont cCnt defs) → ContTypeRes tg → Prop
| EmptyValueK (ty : Ty) :
  ContType .Expr Δ Γ S [] (.Expr ty)
| FieldK
  (cls : Fin cCnt) (ty : Ty) (f : Nat) (hf : f < defs.fieldsCnt cls) :
  defs.fieldsTy cls ⟨f, hf⟩ = ty →
  ContType .Expr Δ₁ Γ₁ S K (.Expr ty) →
  ContType .Expr Δ₁ Γ₁ S (.fieldK f :: K) (.Expr (.cls cls))
| DeclK
  (type : Ty) (Γ₁ : Ctx) :
  ContType .Stmt Δ₁ (type :: Γ₁) S K .Stmt →
  ContType .Expr Δ₁ Γ₁ S (.declK type :: K) (.Expr type)
| AssignK
  (x : VarName) (type : Ty) (Γ₁ : Ctx) :
  (Γ₁(x) = type) →
  ContType .Stmt Δ₁ Γ₁ S K .Stmt →
  ContType .Expr Δ₁ Γ₁ S (.assignK x :: K) (.Expr type)
| ExprStmtK
  (Γ₁ : Ctx) (type : Ty) :
  ContType .Stmt Δ₁ Γ₁ S K .Stmt →
  ContType .Expr Δ₁ Γ₁ S (.exprStmtK :: K) (.Expr type)
| BinOpLK
  (Γ₁ : Ctx) (op : BinOp) (e₂ : Lang .Expr) :
  Typ cCnt defs .Expr Δ₁ Γ₁ e₂ (.Expr op.args.2) →
  ContType .Expr Δ₁ Γ₁ S K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ S (.binopLK op e₂ :: K) (.Expr op.args.1)
| BinOpRK
  (Γ₁ : Ctx) (op : BinOp) (v₁ : Value) :
  simpleType v₁ op.args.1 →
  ContType .Expr Δ₁ Γ₁ S K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ S (.binopRK op v₁ :: K) (.Expr op.args.2)
| UnOpK
  (Γ₁ : Ctx) (op : UnOp) :
  ContType .Expr Δ₁ Γ₁ S K (.Expr op.args.out) →
  ContType .Expr Δ₁ Γ₁ S (.unopK op :: K) (.Expr op.args.1)
| IfCondK
  (s₁ : Lang .Expr) (s₂ : Lang .Expr) (Γ₁ : Ctx) (type : Ty) :
  Typ cCnt defs .Expr Δ₁ Γ₁ s₁ (.Expr type) →
  Typ cCnt defs .Expr Δ₁ Γ₁ s₂ (.Expr type) →
  ContType .Expr Δ₁ Γ₁ S K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ S (.ifCondK s₁ s₂ :: K) (.Expr .bool)
| LoopK
  (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr) :
  Typ cCnt defs .Expr Δ₁ Γ₁ c (.Expr .bool) →
  Typ cCnt defs .Expr (.Loop Γ₁.length :: Δ₁) Γ₁ e (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ S K (.Expr .unit) →
  ContType .Expr Δ₁ Γ₁ S (.loopK c e :: K) (.Expr .bool)
| LoopContK
  (Γ₁ : Ctx) (e : Lang .Expr) (c : Lang .Expr)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  n ≤ Γ₁.length →
  Typ cCnt defs .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) c (.Expr .bool) →
  Typ cCnt defs .Expr (.Loop n :: Δ₁) (Γ₁.drop (Γ₁.length - n)) e (.Expr .unit) →
  Δ₁.length = J₀.length →
  Δ₁.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 →
   ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m →
    ContType .Expr Δ₁ Γ₁ S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S K (.Expr .unit) →
  ContType .Expr (.Loop Γ₁.length :: Δ₁) Γ₁ S (.loopContK c e n J₀ :: K) (.Expr .unit)
| BreakRestoreK (Γ₁ : Ctx)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  n ≤ Γ₁.length →
  Δ₁.length = J₀.length →
  Δ₁.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 →
   ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m →
    ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S K (.Expr .unit) →
  ContType .Expr Δ Γ₁ S (.breakRestoreK n J₀ :: K) (.Expr .unit)
| ScopeExitK
  (Γ₁ : Ctx) (n : Nat) (type : Ty)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  n ≤ Γ₁.length →
  Δ₂.length = J₀.length →
  Δ₂.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 →
   ContType .Expr Δ₂ (Γ₁.drop (Γ₁.length - n)) S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m →
    ContType .Expr Δ₂ Γ₁ S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₂ (Γ₁.drop (Γ₁.length - n)) S K (.Expr type) →
  ContType .Expr Δ₁ Γ₁ S (.scopeExitK n J₀ :: K) (.Expr type)
| ReturnJumpK
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (ret : Ty) (l : Nat) :
  l < Δ₁.length →
  Δ₁[l]! = .Method cls m →
  -- is this one needed?
  (l = 0 ∨ LoopJump cCnt defs Δ₁ (l - 1)) →
  ret = (defs.methods cls m).ret →
  ContType .Expr Δ₁ Γ₁ S (.returnJumpK l :: K) (.Expr ret)
| ReturnRestoreK (ty : Ty) (J₀ : JStackCtx cCnt defs)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  Coh cCnt defs E₀ S Γ₂ →
  Δ₂.length = J₀.length →
  Δ₂.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 →
   ContType .Expr Δ₂ Γ₂ S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m →
    ContType .Expr Δ₂ Γ₂ S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₂ Γ₂ S K (.Expr ty) →
  ContType .Expr Δ₁ Γ₁ S (.returnRestoreK E₀ J₀ :: K) (.Expr ty)
| CallRestoreK (ty : Ty)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  Coh cCnt defs E₀ S Γ₂ →
  Δ₂.length = J₀.length →
  Δ₂.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 →
   ContType .Expr Δ₂ Γ₂ S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₂[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m →
    ContType .Expr Δ₂ Γ₂ S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₂[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₂ Γ₂ S K (.Expr ty) →
  ContType .Expr Δ₁ Γ₁ S (.callRestoreK E₀ J₀ :: K) (.Expr ty)
| ArgK
  (cls : Fin cCnt) (m : Fin (defs.methodsCnt cls))
  (sep : Fin (defs.methods cls m).nArg) (vals : Fin sep → Value)
  (exprs : Fin ((defs.methods cls m).nArg - sep - 1) → Lang .Expr)
  (retTy : Ty) (tyRes : Ty) :
  retTy = (defs.methods cls m).ret →
  tyRes = (defs.methods cls m).argTy sep →
  (∀ i,
    ValueTyp cCnt defs (vals i) ((defs.methods cls m).argTy ⟨i, by omega⟩) S) →
  (∀ i,
    Typ cCnt defs .Expr Δ₁ Γ₁
      (exprs i)
      (.Expr ((defs.methods cls m).argTy ⟨i + sep + 1, by omega⟩))) →
  ContType .Expr Δ₁ Γ₁ S K (.Expr retTy) →
  ContType .Expr Δ₁ Γ₁ S (.argK cls m sep vals exprs :: K) (.Expr tyRes)
| NewK
  (cls : Fin cCnt)
  (sep : Fin (defs.fieldsCnt cls)) (vals : Fin sep → Value)
  (exprs : Fin (defs.fieldsCnt cls - sep - 1) → Lang .Expr)
  (retTy : Ty) (tyRes : Ty) :
  retTy = .cls cls →
  tyRes = (defs.fieldsTy cls sep) →
  (∀ i,
    ValueTyp cCnt defs (vals i) (defs.fieldsTy cls ⟨i, by omega⟩) S) →
  (∀ i,
    Typ cCnt defs .Expr Δ₁ Γ₁
      (exprs i)
      (.Expr (defs.fieldsTy cls ⟨i + sep + 1, by omega⟩))) →
  ContType .Expr Δ₁ Γ₁ S K (.Expr retTy) →
  ContType .Expr Δ₁ Γ₁ S (.newK cls sep vals exprs :: K) (.Expr tyRes)
-- # Statement Continuations
| SeqK
  (Γ₁ : Ctx) (Γ₂ : Ctx) (s : Lang .Stmt) :
  Typ cCnt defs .Stmt Δ₁ Γ₁ s (.Stmt Γ₂) →
  ContType .Stmt Δ₁ Γ₂ S K .Stmt →
  ContType .Stmt Δ₁ Γ₁ S (.seqK s :: K) .Stmt
| ScopeBodyK
  (Γ₁ : Ctx) (e : Lang .Expr) (type : Ty) (n : Nat)
  (cnts : List (List (Cont cCnt defs))) :
  --add coherence
  Typ cCnt defs .Expr Δ₁ Γ₁ e (.Expr type) →
  n ≤ Γ₁.length →
  Δ₁.length = J₀.length →
  Δ₁.length = cnts.length →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 →
   ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S J₀[l]! (.Expr .unit))) →
  (∀ l < J₀.length, ∀ n1,
    (Δ₁[l]! = .Loop n1 → ∃ J₁, J₀[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m →
    ContType .Expr Δ₁ Γ₁ S J₀[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J₀.length, ∀ cls m,
    (Δ₁[l]! = .Method cls m → ∃ E₀ J₁, J₀[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType .Expr Δ₁ (Γ₁.drop (Γ₁.length - n)) S K (.Expr type) →
  ContType .Stmt Δ₁ Γ₁ S (.scopeBodyK e n J₀ :: K) .Stmt

def S_ok (S : Store cCnt defs) : Prop :=
  ∀ obj ∈ S.entries, (ValueTyp cCnt defs (.Addr obj.1) (.cls obj.2.cls) S)

def defs_ok : Prop :=
  ∀ cls m,
    Typ cCnt defs .Expr [.Method cls m]
      (List.ofFn (defs.methods cls m).argTy)
      (defs.methods cls m).body
      (.Expr (defs.methods cls m).ret)

inductive Wt : (m : EvalMode) → CEK cCnt defs m → Prop
| WtExprE
  (e : Lang .Expr) (type : Ty)
  (cnts : List (List (Cont cCnt defs))) :
  Coh cCnt defs E S Γ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  Typ cCnt defs .Expr Δ Γ e (.Expr type) →
  Δ.length = J.length →
  Δ.length = cnts.length →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 →
   ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr .unit))) →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 → ∃ J₁, J[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m →
    ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m → ∃ E₀ J₁, J[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType cCnt defs .Expr Δ Γ S K (.Expr type) →
  Wt .Eval (.Eval .Expr e E J S K)
| WtExprS
  (s : Lang .Stmt)
  (cnts : List (List (Cont cCnt defs))) :
  Coh cCnt defs E S Γ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  Typ cCnt defs .Stmt Δ Γ s (.Stmt Γ₁) →
  Δ.length = J.length →
  Δ.length = cnts.length →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 →
   ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr .unit))) →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 → ∃ J₁, J[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m →
    ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m → ∃ E₀ J₁, J[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType cCnt defs .Stmt Δ Γ₁ S K .Stmt →
  Wt .Eval (.Eval .Stmt s E J S K)
| WtContV
  (v : Value) (type : Ty)
  (cnts : List (List (Cont cCnt defs))) :
  Coh cCnt defs E S Γ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  ValueTyp cCnt defs v type S →
  Δ.length = J.length →
    Δ.length = cnts.length →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 →
   ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr .unit))) →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 → ∃ J₁, J[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m →
    ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m → ∃ E₀ J₁, J[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType cCnt defs .Expr Δ Γ S K (.Expr type) →
  Wt .Cont (.Cont (.value v) E J S K)
| WtContS
  (cnts : List (List (Cont cCnt defs))) :
  Coh cCnt defs E S Γ →
  S_ok cCnt defs S →
  defs_ok cCnt defs →
  Δ.length = J.length →
    Δ.length = cnts.length →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 →
   ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr .unit))) →
  (∀ l < J.length, ∀ n1,
    (Δ[l]! = .Loop n1 → ∃ J₁, J[l]! = .breakRestoreK n1 J₁ :: cnts[l]!)) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m →
    ContType cCnt defs .Expr Δ Γ S J[l]! (.Expr (defs.methods cls m).ret))) →
  (∀ l < J.length, ∀ cls m,
    (Δ[l]! = .Method cls m → ∃ E₀ J₁, J[l]! = .returnRestoreK E₀ J₁ :: cnts[l]!)) →
  ContType cCnt defs .Stmt Δ Γ S K .Stmt →
  Wt .Cont (.Cont .skip E J S K)
