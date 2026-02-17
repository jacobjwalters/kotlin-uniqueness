--import Finmap
abbrev MethodName := Nat
abbrev VarName := Nat

inductive Expr
| Null
| Var (x : VarName)
| Call (m : MethodName) (args : List Expr)
| Bool (cond : Bool)
| Nat (n : Nat)
deriving Repr

inductive τ
| Nat
| Bool
deriving Repr

inductive Statement
| Decl (x : VarName) (type : τ)
| Assign (x : VarName) (exp : Expr)
| Seq (s₁ : Statement) (s₂ : Statement)
| If (cond : Expr) (s₁ : Statement) (s₂ : Statement)
| Return (val : Expr)
| Call (m : MethodName) (args : List Expr)
deriving Repr

notation:100 s₁:100 ";" s₂:101 => Statement.Seq s₁ s₂
notation x "::=" exp => Statement.Assign x exp

inductive MethodDeclaration : MethodName → List τ → τ → Type
| Decl (name : MethodName) (args : List τ) (σ : τ) :
  MethodDeclaration name args σ


section Context

inductive Ctx
| VarExt (x : VarName) (type : τ)
| MethodDel (type : τ)
| ControlDel

abbrev Γ := List Ctx

inductive WFC : Γ → Prop
| CtxEmp : WFC []
| CtxVarExt (x : VarName) (type : τ) (tail : Γ) (h : ¬∃ type₁, (.VarExt x type₁) ∈ tail) :
  WFC tail → WFC ((.VarExt x type) :: tail)
| CtxStackFrame (type : τ) (tail : Γ) : WFC tail → WFC ((.MethodDel type) :: tail)

def dropMethodStack : Γ → Γ
| [] => []
| .MethodDel type :: tail => .MethodDel type :: tail
| .ControlDel :: tail => dropMethodStack tail
| .VarExt _ _ :: tail => dropMethodStack tail

def dropControlStack : Γ → Γ
| [] => []
| .MethodDel type :: tail => .MethodDel type :: tail
| .ControlDel :: tail => .ControlDel :: tail
| .VarExt _ _ :: tail => dropControlStack tail

end Context

section Types

inductive ExprType : Γ → Expr → τ → Prop
| TrueConst (ctx : Γ) : ExprType ctx (.Bool true) .Bool
| FalseConst (ctx : Γ) : ExprType ctx (.Bool false) .Bool
| NatConst (ctx : Γ) (n : Nat) : ExprType ctx (.Nat n) .Nat
| NullConst (ctx : Γ) (type : τ) : ExprType ctx .Null type
| VarAccess {name : VarName} {type : τ} (ctx : Γ) (h : (.VarExt name type) ∈ ctx) :
  ExprType ctx (.Var name) type
| CallExpr {name : MethodName} {arg_types : List τ} {args : List Expr}
  (method : MethodDeclaration name arg_types σ) :
  (∀ elem ∈ (args.zip arg_types), ExprType Γ₁ elem.1 elem.2) →
  ExprType Γ₁ (.Call name args) σ

inductive StmtType : Γ → Statement → Γ → Prop
| VarDecl {name : VarName} {type : τ} (ctx : Γ) (h : ¬∃ type₁, (.VarExt name type₁) ∈ ctx) :
  StmtType ctx (.Decl name type) (.VarExt name type :: ctx)
| VarAssign {name : VarName} {type : τ} {e : Expr} (ctx : Γ)
  (exp_type : ExprType (.VarExt name type :: ctx) e type) :
  StmtType (.VarExt name type :: ctx) (name ::= e) (.VarExt name type :: ctx)
| Seq (s1 : Statement) (s2 : Statement) :
  StmtType Γ₁ s1 Γ₂ → StmtType Γ₂ s2 Γ₃ → StmtType Γ₁ (s1; s2) Γ₃
| IfStmt {e : Expr} (s1 : Statement) (s2 : Statement) :
  StmtType (.ControlDel :: Γ₁) s1 (.ControlDel :: Γ₂) →
  StmtType (.ControlDel :: Γ₁) s2 (.ControlDel :: Γ₂) →
  StmtType Γ₁ (.If e s1 s2) Γ₂
| Return {e : Expr} {type : τ} (exp_type : ExprType Γ₁ e type) :
  StmtType Γ₁ (.Return e) (dropMethodStack Γ₁)
| CallStmt {name : MethodName} {arg_types : List τ} {args : List Expr}
  (method : MethodDeclaration name arg_types σ) :
  (∀ elem ∈ (args.zip arg_types), ExprType Γ₁ elem.1 elem.2) →
  StmtType Γ₁ (.Call name args) Γ₁

end Types
