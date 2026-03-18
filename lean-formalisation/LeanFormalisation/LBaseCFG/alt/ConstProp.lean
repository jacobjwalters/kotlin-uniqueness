import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis
import LeanFormalisation.LBaseCFG.alt.AltCFGRepr

open LeanFormalisation AltCFG

-- don't want to touch the other file so i derive this here
-- but i could very much not.
instance : DecidableEq Value := by
  intro v₁ v₂
  cases v₁ <;> cases v₂ <;> try exact isTrue rfl
  case Nat.Nat =>
    rename_i n n'
    by_cases h : n = n'
    case pos =>
      refine isTrue (by congr)
    case neg =>
      refine isFalse ?_
      intro h'; injection h' with heq; exact h heq
  all_goals
    refine isFalse ?_
    intros h; cases h

section Flat
inductive Flat where
| Bot
| Val (v : Value)
| Top
deriving DecidableEq

instance : Repr Flat where
  reprPrec := fun s _ =>
    match s with
    | .Bot => "∅"
    | .Top => "⊤"
    | .Val v => repr v

instance : Bot Flat where bot := .Bot
instance : Top Flat where top := .Top

def Flat.sup : Flat -> Flat -> Flat
| .Bot, x
| x, .Bot => x
| .Top, _
| _, .Top => .Top
| .Val v₁, .Val v₂ =>
  if v₁ = v₂ then
    .Val v₁
  else
    .Top

def Flat.inf : Flat -> Flat -> Flat
| .Top, x
| x, .Top => x
| .Bot, _
| _, .Bot => .Bot
| .Val v₁, .Val v₂ =>
  if v₁ = v₂ then
    .Val v₁
  else
    .Bot

def Flat.exclude : Flat -> Value -> Flat
| .Bot, _ => .Bot
| .Top, _ => .Top
| .Val v, blocked => if v = blocked then .Bot else .Val v

instance : Max Flat where
  max := Flat.sup

instance : Min Flat where
  min := Flat.inf
end Flat

abbrev FlatFact := fact (Domain Flat)

private def evalBinOpConst (op : BinOp) (v₁ v₂ : Value) : Flat :=
  match op, v₁, v₂ with
  | .Add, .Nat n₁, .Nat n₂ => .Val (.Nat (n₁ + n₂))
  | .Sub, .Nat n₁, .Nat n₂ => .Val (.Nat (n₁ - n₂))
  | .NatEq, .Nat n₁, .Nat n₂ => .Val (if n₁ = n₂ then .True else .False)
  | .BoolEq, .True, .True => .Val .True
  | .BoolEq, .False, .False => .Val .True
  | .BoolEq, .True, .False => .Val .False
  | .BoolEq, .False, .True => .Val .False
  | _, _, _ => .Top

private def evalUnOpConst (op : UnOp) (v : Value) : Flat :=
  match op, v with
  | .IsZero, .Nat 0 => .Val .True
  | .IsZero, .Nat _ => .Val .False
  | _, _ => .Top

def evalExprFlat (ρ : Domain Flat) : Lang .Expr -> Flat
| .Var x => getVar ρ x
| .Nat n => .Val (.Nat n)
| .True => .Val .True
| .False => .Val .False
| .Unit => .Val .Unit
| .BinOp e₁ e₂ op =>
    match evalExprFlat ρ e₁, evalExprFlat ρ e₂ with
    | .Bot, _
    | _, .Bot => .Bot
    | .Val v₁, .Val v₂ => evalBinOpConst op v₁ v₂
    | _, _ => .Top
| .UnOp e op =>
    match evalExprFlat ρ e with
    | .Bot => .Bot
    | .Val v => evalUnOpConst op v
    | .Top => .Top
| .If cond e₁ e₂ =>
    match evalExprFlat ρ cond with
    | .Val .True => evalExprFlat ρ e₁
    | .Val .False => evalExprFlat ρ e₂
    | .Bot => .Bot
    | _ => evalExprFlat ρ e₁ ⊔ evalExprFlat ρ e₂
| .Scope _ res => evalExprFlat ρ res
| .While _ _
| .Break => .Top

def refineCondConst (cond : Lang .Expr) (assumeTrue : Bool) (ρ : Domain Flat) : Domain Flat :=
  match cond, assumeTrue with
  | .True, true => ρ
  | .True, false => ⊥
  | .False, true => ⊥
  | .False, false => ρ
  | .UnOp (.Var x) .IsZero, true => setVar ρ x ((getVar ρ x) ⊓ .Val (.Nat 0))
  | .UnOp (.Var x) .IsZero, false => setVar ρ x ((getVar ρ x).exclude (.Nat 0))
  | .BinOp (.Var x) (.Nat n) .NatEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val (.Nat n))
  | .BinOp (.Var x) (.Nat n) .NatEq, false => setVar ρ x ((getVar ρ x).exclude (.Nat n))
  | .BinOp (.Nat n) (.Var x) .NatEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val (.Nat n))
  | .BinOp (.Nat n) (.Var x) .NatEq, false => setVar ρ x ((getVar ρ x).exclude (.Nat n))
  | .BinOp (.Var x) .True .BoolEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val .True)
  | .BinOp (.Var x) .True .BoolEq, false => setVar ρ x ((getVar ρ x).exclude .True)
  | .BinOp (.Var x) .False .BoolEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val .False)
  | .BinOp (.Var x) .False .BoolEq, false => setVar ρ x ((getVar ρ x).exclude .False)
  | .BinOp .True (.Var x) .BoolEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val .True)
  | .BinOp .True (.Var x) .BoolEq, false => setVar ρ x ((getVar ρ x).exclude .True)
  | .BinOp .False (.Var x) .BoolEq, true => setVar ρ x ((getVar ρ x) ⊓ .Val .False)
  | .BinOp .False (.Var x) .BoolEq, false => setVar ρ x ((getVar ρ x).exclude .False)
  | _, _ => ρ

def transferConstNode (n : CFGNode) (ρ : Domain Flat) : Domain Flat :=
  transferScopedNode evalExprFlat n ρ

def transferConstEdge (e : CFGEdge) (ρ : Domain Flat) : Domain Flat :=
  transferBranchEdge refineCondConst e ρ

def runConstProp (g : CFG) (entryInit : Domain Flat := ⊥) : FlatFact × FlatFact :=
  worklistForwardEdge g transferConstNode transferConstEdge
    entryInit (fun _ => ⊥) (fun _ => ⊥) g.nodes

def constOverlay (inF outF : FlatFact) : AltCFGRepr.DotOverlay :=
  { nodeMeta := fun n =>
      [ s!"in={repr (inF n)}"
      , s!"out={repr (outF n)}"
      ]
    edgeAttrs := fun e =>
      match e.kind with
      | .trueBranch => [("color", "darkgreen")]
      | .falseBranch => [("color", "firebrick")]
      | .back => [("color", "royalblue")]
      | .breakOut => [("style", "dashed"), ("color", "gray40")]
      | .normal => []
  }

def printResult (g : CFG) (inF outF : FlatFact) : IO Unit := do
  IO.println (AltCFGRepr.toDotWith g (constOverlay inF outF))

def main (_ : List String) : IO Unit := do
  let g := stmtCFG sampleProgram
  let (inF, outF) := runConstProp g
  printResult g inF outF
