import LeanFormalisation.LBase

/-! # Elaborator for LBase

A monadic builder that lets you write LBase programs with named
variables instead of raw de Bruijn indices. The elaboration monad
tracks the variable context and resolves names to indices automatically.

Usage:
```
def myProg : Lang .Stmt := elaborate do
  eStmts [
    var_ "x" .nat 5,
    var_ "y" .nat 3,
    set_ "x" (v "x" + v "y")
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

/-! ## Literal coercions -/

/-- Nat literals lift into the elaboration monad: `(5 : Elab (Lang .Expr))`. -/
instance (n : Nat) : OfNat (Elab (Lang .Expr)) n where
  ofNat := pure (.Nat n)

/-! ## Expression builders -/

def eNat (n : Nat) : Elab (Lang .Expr) := pure (.Nat n)
def eTrue : Elab (Lang .Expr) := pure .True
def eFalse : Elab (Lang .Expr) := pure .False
def eUnit : Elab (Lang .Expr) := pure .Unit

/-- Variable reference by name. -/
def v (name : String) : Elab (Lang .Expr) := do
  let ctx ← get
  match ctx.indexOf? name with
  | some i => return .Var i
  | none => return .Var 9999  -- sentinel for unbound

abbrev eVar := v

/-! ## Operators -/

def eBinOp (op : BinOp) (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .BinOp (← a) (← b) op

def eAdd (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .Add a b
def eSub (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .Sub a b
def eNatEq (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .NatEq a b
def eBoolEq (a b : Elab (Lang .Expr)) : Elab (Lang .Expr) := eBinOp .BoolEq a b

/-- `a + b` for LBase Nat addition. -/
instance : HAdd (Elab (Lang .Expr)) (Elab (Lang .Expr)) (Elab (Lang .Expr)) where
  hAdd := eAdd

/-- `a - b` for LBase Nat subtraction. -/
instance : HSub (Elab (Lang .Expr)) (Elab (Lang .Expr)) (Elab (Lang .Expr)) where
  hSub := eSub

/-- `a .==. b` for LBase Nat equality test. -/
notation:50 a " .==. " b => eNatEq a b

/-- `a .=b=. b` for LBase Bool equality test. -/
notation:50 a " .=b=. " b => eBoolEq a b

def eIsZero (a : Elab (Lang .Expr)) : Elab (Lang .Expr) := do
  return .UnOp (← a) .IsZero

/-! ## Control flow expressions -/

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

/-- `not (isZero a)`: true when a is nonzero. Common loop-condition pattern. -/
def eNotZero (a : Elab (Lang .Expr)) : Elab (Lang .Expr) :=
  eIf (eIsZero a) eFalse eTrue

/-! ## Statement builders -/

/-- Declare a variable: `var_ "x" .nat 5` -/
def var_ (name : String) (ty : Ty) (init : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  let e ← init
  modify (name :: ·)
  return .Decl ty e

abbrev eDecl := var_

/-- Assign to a variable: `set_ "x" (v "x" + 1)` -/
def set_ (name : String) (val : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  let ctx ← get
  let rhs ← val
  match ctx.indexOf? name with
  | some i => return .Assign i rhs
  | none => return .Assign 9999 rhs  -- sentinel for unbound

abbrev eAssign := set_

def eSeq (s₁ s₂ : Elab (Lang .Stmt)) : Elab (Lang .Stmt) := do
  return .Seq (← s₁) (← s₂)

def eDo (e : Elab (Lang .Expr)) : Elab (Lang .Stmt) := do
  return .Do (← e)

/-- Sequence multiple statements left-to-right. -/
def eStmts : List (Elab (Lang .Stmt)) → Elab (Lang .Stmt)
  | [] => pure (.Do .Unit)  -- no-op fallback
  | [s] => s
  | s :: ss => eSeq s (eStmts ss)

/-! ## Common patterns -/

/-- Scope that executes statements and returns unit.
    `scope_ [s₁, s₂, ...]` = `{ s₁; s₂; ...; unit }` -/
def scope_ (body : List (Elab (Lang .Stmt))) : Elab (Lang .Expr) :=
  eScope (eStmts body) eUnit

/-- Scope with statements and a custom result expression.
    `scopeReturn [s₁, s₂] (v "x")` = `{ s₁; s₂; x }` -/
def scopeReturn (body : List (Elab (Lang .Stmt))) (result : Elab (Lang .Expr))
    : Elab (Lang .Expr) :=
  eScope (eStmts body) result

/-- While loop as a statement (wraps body in scope + unit).
    `while_ cond [s₁, s₂]` = `do while cond { s₁; s₂; unit }` -/
def while_ (cond : Elab (Lang .Expr)) (body : List (Elab (Lang .Stmt)))
    : Elab (Lang .Stmt) :=
  eDo (eWhile cond (scope_ body))

/-- If-then-else as a statement (each branch is a scoped block).
    `if_ cond [s₁] [s₂]` = `do (if cond then { s₁; unit } else { s₂; unit })` -/
def if_ (cond : Elab (Lang .Expr))
    (thenBody : List (Elab (Lang .Stmt)))
    (elseBody : List (Elab (Lang .Stmt))) : Elab (Lang .Stmt) :=
  eDo (eIf cond (scope_ thenBody) (scope_ elseBody))

/-- Break from the nearest enclosing loop, as a statement. -/
def break_ (level : Nat := 0) : Elab (Lang .Stmt) :=
  eDo (eBreak level)

/-! ## Run the elaborator -/

/-- Run the elaborator, producing a closed statement. -/
def elaborate (m : Elab (Lang .Stmt)) : Lang .Stmt :=
  (m.run []).1

/-- Run the elaborator for an expression. -/
def elaborateExpr (m : Elab (Lang .Expr)) : Lang .Expr :=
  (m.run []).1
