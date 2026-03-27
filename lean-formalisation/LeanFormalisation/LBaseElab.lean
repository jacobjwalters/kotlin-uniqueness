import LeanFormalisation.LBase

/-! # Elaborator for LBase

A monadic builder that lets you write LBase programs with named
variables instead of raw de Bruijn indices. The elaboration monad
tracks the variable context and resolves names to indices automatically.

Usage:
```
def myProg : Lang .Stmt := elaborate do
  eStmts [
    eDecl "x" .nat (eNat 5),
    eDecl "y" .nat (eNat 3),
    eAssign "x" (eAdd (eVar "x") (eVar "y"))
  ]
```
-/

/-- Elaboration context: list of variable names, most recent first. -/
abbrev ECtx := List String

/-- Look up a variable name, returning its de Bruijn index. -/
def ECtx.indexOf? (ctx : ECtx) (name : String) : Option Nat :=
  ctx.findIdx? (· == name)

/-- Elaboration monad: tracks the variable context. -/
abbrev Elab := StateM ECtx

-- Expression builders

def eNat (n : Nat) : Elab (Lang .Expr) := pure (.Nat n)
def eTrue : Elab (Lang .Expr) := pure .True
def eFalse : Elab (Lang .Expr) := pure .False
def eUnit : Elab (Lang .Expr) := pure .Unit

def eVar (name : String) : Elab (Lang .Expr) := do
  let ctx ← get
  match ctx.indexOf? name with
  | some i => return .Var i
  | none => return .Var 9999  -- sentinel for unbound

def eBinOp (op : BinOp) (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .BinOp (← a) (← b) op

def eAdd (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .Add a b
def eSub (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .Sub a b
def eNatEq (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .NatEq a b
def eBoolEq (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .BoolEq a b

def eIsZero (a : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .UnOp (← a) .IsZero

def eIf (cond e₁ e₂ : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .If (← cond) (← e₁) (← e₂)

def eWhile (cond : Elab (Lang .Expr)) (body : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .While (← cond) (← body)

def eBreak (level : Nat := 0) : Elab (Lang .Expr) := pure (.Break level)

/-- Build a scope: runs the statement builder (which may declare vars),
    then evaluates the result expression, then restores the context. -/
def eScope (body : Elab (Lang .Stmt)) (result : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  let saved ← get
  let s ← body
  let e ← result
  set saved
  return .Scope s e

-- Statement builders

def eDecl (name : String) (ty : Ty) (init : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  let e ← init
  modify (name :: ·)
  return .Decl ty e

def eAssign (name : String) (val : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  let ctx ← get
  let v ← val
  match ctx.indexOf? name with
  | some i => return .Assign i v
  | none => return .Assign 9999 v  -- sentinel for unbound

def eSeq (s₁ s₂ : Elab (Lang .Stmt)) : Elab (Lang .Stmt) := do
  return .Seq (← s₁) (← s₂)

def eDo (e : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  return .Do (← e)

/-- Sequence multiple statements left-to-right. -/
def eStmts : List (Elab (Lang .Stmt)) → Elab (Lang .Stmt)
  | [] => pure (.Do .Unit)  -- no-op fallback
  | [s] => s
  | s :: ss => eSeq s (eStmts ss)

/-- Run the elaborator, producing a closed statement. -/
def elaborate (m : Elab (Lang .Stmt)) : Lang .Stmt :=
  (m.run []).1

/-- Run the elaborator for an expression. -/
def elaborateExpr (m : Elab (Lang .Expr)) : Lang .Expr :=
  (m.run []).1
