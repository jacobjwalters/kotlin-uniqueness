import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis
import LeanFormalisation.LBaseCFG.alt.AltCFGRepr

open LeanFormalisation AltCFG

section Sign
inductive Sign where
| Pos
| Neg
| Zero
| NonPos
| NonNeg
| Bot
| Top
deriving DecidableEq

instance : Bot Sign where bot := .Bot
instance : Top Sign where top := .Top
instance : Repr Sign where
  reprPrec := fun s _ =>
    match s with
    | .Pos => "+"
    | .Neg => "-"
    | .Zero => "0"
    | .NonPos => "<=0"
    | .NonNeg => ">=0"
    | .Bot => "∅"
    | .Top => "ℕ"

private def Sign.fromAtomFlags (hasNeg hasZero hasPos : Bool) : Sign :=
  match hasNeg, hasZero, hasPos with
  | false, false, false => .Bot
  | false, false, true  => .Pos
  | false, true, false  => .Zero
  | false, true, true   => .NonNeg
  | true, false, false  => .Neg
  | true, false, true   => .Top
  | true, true, false   => .NonPos
  | true, true, true    => .Top

private def Sign.hasNeg : Sign → Bool
| .Neg | .NonPos | .Top => true
| _ => false

private def Sign.hasZero : Sign → Bool
| .Zero | .NonNeg | .NonPos | .Top => true
| _ => false

private def Sign.hasPos : Sign → Bool
| .Pos | .NonNeg | .Top => true
| _ => false

def Sign.sup : Sign → Sign → Sign
| s₁, s₂ =>
    Sign.fromAtomFlags
      (s₁.hasNeg || s₂.hasNeg)
      (s₁.hasZero || s₂.hasZero)
      (s₁.hasPos || s₂.hasPos)

def Sign.inf : Sign → Sign → Sign
| s₁, s₂ =>
    Sign.fromAtomFlags
      (s₁.hasNeg && s₂.hasNeg)
      (s₁.hasZero && s₂.hasZero)
      (s₁.hasPos && s₂.hasPos)

instance : Max Sign where
  max := Sign.sup

instance : Min Sign where
  min := Sign.inf

def Sign.addAtomic : Sign → Sign → Sign
| .Pos, .Pos => .Pos
| .Pos, .Zero => .Pos
| .Pos, .Neg => .Top
| .Zero, .Pos => .Pos
| .Zero, .Zero => .Zero
| .Zero, .Neg => .Neg
| .Neg, .Pos => .Top
| .Neg, .Zero => .Neg
| .Neg, .Neg => .Neg
| _, _ => .Top

def Sign.subAtomic : Sign → Sign → Sign
| .Pos, .Pos => .Top
| .Pos, .Zero => .Pos
| .Pos, .Neg => .Pos
| .Zero, .Pos => .Neg
| .Zero, .Zero => .Zero
| .Zero, .Neg => .Pos
| .Neg, .Pos => .Neg
| .Neg, .Zero => .Neg
| .Neg, .Neg => .Top
| _, _ => .Top

private def Sign.atomicChoices : Sign → List Sign
| .Pos => [.Pos]
| .Neg => [.Neg]
| .Zero => [.Zero]
| .NonPos => [.Neg, .Zero]
| .NonNeg => [.Zero, .Pos]
| .Top => [.Neg, .Zero, .Pos]
| .Bot => []

private def Sign.foldSup (xs : List Sign) : Sign :=
  xs.foldl (fun acc s => acc ⊔ s) .Bot

private def Sign.combineAtomic (op : Sign → Sign → Sign)
    (lhs rhs : List Sign) : Sign :=
  lhs.foldl
    (fun acc a => rhs.foldl (fun acc' b => acc' ⊔ op a b) acc)
    .Bot

def Sign.add : Sign → Sign → Sign
| s₁, s₂ =>
  Sign.combineAtomic Sign.addAtomic s₁.atomicChoices s₂.atomicChoices

def Sign.sub : Sign → Sign → Sign
| s₁, s₂ =>
  Sign.combineAtomic Sign.subAtomic s₁.atomicChoices s₂.atomicChoices

def Sign.excludeZero : Sign → Sign
| s => Sign.fromAtomFlags s.hasNeg false s.hasPos
end Sign

abbrev PosFact := fact (Domain Sign)

def signOfNat (n : Nat) : Sign :=
  if n = 0 then .Zero else .Pos

def evalExprSign (ρ : Domain Sign) : Lang .Expr -> Sign
| .Var x => getVar ρ x
| .Nat n => signOfNat n
| .BinOp e₁ e₂ op =>
    match op with
    | .Add => Sign.add (evalExprSign ρ e₁) (evalExprSign ρ e₂)
    | .Sub => Sign.sub (evalExprSign ρ e₁) (evalExprSign ρ e₂)
    | .NatEq => .Top
    | .BoolEq => .Top
| .UnOp _ _ => .Top
| .If _ e₁ e₂ => evalExprSign ρ e₁ ⊔ evalExprSign ρ e₂
| .Scope _ res => evalExprSign ρ res
| .True
| .False
| .Unit
| .While _ _
| .Break => .Top

def transferPosNode (n : CFGNode) (ρ : Domain Sign) : Domain Sign :=
  transferScopedNode evalExprSign n ρ

def refineCond (cond : Lang .Expr) (assumeTrue : Bool) (ρ : Domain Sign) : Domain Sign :=
  match cond, assumeTrue with
  | .True, true => ρ
  | .True, false => ⊥
  | .False, true => ⊥
  | .False, false => ρ
  | .UnOp (.Var x) .IsZero, true => setVar ρ x ((getVar ρ x) ⊓ .Zero)
  | .UnOp (.Var x) .IsZero, false => setVar ρ x ((getVar ρ x).excludeZero)
  | .BinOp (.Var x) (.Nat 0) .NatEq, true => setVar ρ x ((getVar ρ x) ⊓ .Zero)
  | .BinOp (.Var x) (.Nat 0) .NatEq, false => setVar ρ x ((getVar ρ x).excludeZero)
  | .BinOp (.Nat 0) (.Var x) .NatEq, true => setVar ρ x ((getVar ρ x) ⊓ .Zero)
  | .BinOp (.Nat 0) (.Var x) .NatEq, false => setVar ρ x ((getVar ρ x).excludeZero)
  | _, _ => ρ

def transferPosEdge (e : CFGEdge) (ρ : Domain Sign) : Domain Sign :=
  transferBranchEdge refineCond e ρ

def runPositivity (g : CFG) (entryInit : Domain Sign := ⊥) : PosFact × PosFact :=
  worklistForwardEdge g transferPosNode transferPosEdge
    entryInit (fun _ => ⊥) (fun _ => ⊥) g.nodes

def demoProgram : Lang .Stmt :=
  .Seq
    (.Decl .Nat (.Nat 1))
    (.Do
      (.If
        (.BinOp (.Var 0) (.Nat 0) .NatEq)
        (.Scope (.Assign 0 (.Nat 0)) .Unit)
        (.Scope (.Assign 0 (.Nat 2)) .Unit)))

def positivityOverlay (inF outF : PosFact) : AltCFGRepr.DotOverlay :=
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

def printResult (g : CFG) (inF outF : PosFact) : IO Unit := do
  IO.println (AltCFGRepr.toDotWith g (positivityOverlay inF outF))

def main (_ : List String) : IO Unit := do
  let g := stmtCFG demoProgram
  let (inF, outF) := runPositivity g
  printResult g inF outF
