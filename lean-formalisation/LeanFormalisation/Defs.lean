--import Finmap
abbrev MethodName := Nat
abbrev VarName := Nat


inductive Expr
| Null
| Var (x : VarName)
| Call (m : MethodName) (args : List Expr)
| Bool (cond : Bool)
| Nat (n : Nat)

inductive τ
| Nat
| Bool

inductive Statement
| Decl (x : VarName) (type : τ)
| Assign (x : VarName) (exp : Expr)
| Seq (s₁ : Statement) (s₂ : Statement)
| If (cond : Expr) (s₁ : Statement) (s₂ : Statement)
| Return (val : Expr)
| Call (m : MethodName) (args : List Expr)

--add right assoc
notation s₁ ";" s₂ => Statement.Seq s₁ s₂
notation x "::=" exp => Statement.Assign x exp


--for Context, our heap : Variable Name → Type (τ)
--Future work : top level method name → method type

--abbrev Ctx := List (MethodName × Finmap (fun _ => MethodName) VarName)
