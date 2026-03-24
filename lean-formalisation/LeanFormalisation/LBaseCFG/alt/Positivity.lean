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

@[simp]
private def Sign.hasNeg : Sign → Bool
| .Neg | .NonPos | .Top => true
| _ => false

@[simp]
private def Sign.hasZero : Sign → Bool
| .Zero | .NonNeg | .NonPos | .Top => true
| _ => false

@[simp]
private def Sign.hasPos : Sign → Bool
| .Pos | .NonNeg | .Top => true
| _ => false

@[simp]
def Sign.sup : Sign → Sign → Sign
| s₁, s₂ =>
    Sign.fromAtomFlags
      (s₁.hasNeg || s₂.hasNeg)
      (s₁.hasZero || s₂.hasZero)
      (s₁.hasPos || s₂.hasPos)

@[simp]
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

@[simp]
def Sign.height : Sign → Nat
| .Bot => 0
| .Pos => 1
| .Neg => 1
| .Zero => 1
| .NonPos => 2
| .NonNeg => 2
| .Top => 3

instance : FiniteHeight Sign where
  height := Sign.height
  maxHeight := 3
  maxHeight_ub := by intro a; cases a <;> simp
  height_mono := by
    intro a b h
    cases a <;> cases b <;> simp [Sign.fromAtomFlags, Max.max] at *

end Sign

abbrev PosFact (n : Nat) := fact (Domain n Sign)

def signOfNat (k : Nat) : Sign :=
  if k = 0 then .Zero else .Pos

def evalExprSign {n : Nat} (ρ : Domain n Sign) : Lang .Expr -> Sign
| .Var x => getVar ρ x
| .Nat k => signOfNat k
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
| .Break _ => .Top

def transferPosNode {n : Nat} (node : CFGNode) (ρ : Domain n Sign) : Domain n Sign :=
  transferScopedNode evalExprSign node ρ

def refineCond {n : Nat} (cond : Lang .Expr) (assumeTrue : Bool)
    (ρ : Domain n Sign) : Domain n Sign :=
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

def transferPosEdge {n : Nat} (e : CFGEdge) (ρ : Domain n Sign) : Domain n Sign :=
  transferBranchEdge refineCond e ρ

def runPositivity (n : Nat) (g : CFG) (entryInit : Domain n Sign := ⊥) : PosFact n × PosFact n :=
  let bot : fact (Domain n Sign) := fun _ => ⊥
  runDataflow g transferPosNode transferPosEdge
    entryInit bot g.nodes (fun _ h => h)

def positivityOverlay {n : Nat} (inF outF : PosFact n) : AltCFGRepr.DotOverlay :=
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

def printResult {n : Nat} (g : CFG) (inF outF : PosFact n) : IO Unit := do
  IO.println (AltCFGRepr.toDotWith g (positivityOverlay inF outF))

def main (_ : List String) : IO Unit := do
  let g := stmtCFG sampleProgram
  let (inF, outF) := runPositivity 10 g
  printResult g inF outF
