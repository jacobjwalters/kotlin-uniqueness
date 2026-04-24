import LeanFormalisation.LBase.CFG.AltCFG
import LeanFormalisation.LBase.CFG.Analysis
import LeanFormalisation.LBase.CFG.AltCFGRepr

import LeanFormalisation.LBase.CFG.Framework
import LeanFormalisation.LBase.CFG.CorrespondenceProofs
import LeanFormalisation.LBase.CFG.Correspondence

open LeanFormalisation AltCFG AltCFGProofs

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

@[simp]
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

lemma Sign.sup_comm {a b : Sign} : a ⊔ b = b ⊔ a := by
  simp only [max, Sign.sup, Sign.hasNeg, Sign.hasZero, Sign.hasPos]
  cases a <;> simp

lemma Sign.sup_assoc {a b c : Sign} : a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  simp only [max, Sign.sup, Sign.hasNeg, Sign.hasZero, Sign.hasPos]
  cases a <;> cases b <;> cases c <;> simp

instance : Min Sign where
  min := Sign.inf

@[simp]
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

@[simp]
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

@[simp]
private def Sign.atomicChoices : Sign → List Sign
| .Pos => [.Pos]
| .Neg => [.Neg]
| .Zero => [.Zero]
| .NonPos => [.Neg, .Zero]
| .NonNeg => [.Zero, .Pos]
| .Top => [.Neg, .Zero, .Pos]
| .Bot => []

@[simp]
private def Sign.foldSup (xs : List Sign) : Sign :=
  xs.foldl (fun acc s => acc ⊔ s) .Bot

@[simp]
private def Sign.combineAtomic (op : Sign → Sign → Sign)
    (lhs rhs : List Sign) : Sign :=
  lhs.foldl
    (fun acc a => rhs.foldl (fun acc' b => acc' ⊔ op a b) acc)
    .Bot

@[simp]
def Sign.add : Sign → Sign → Sign
| s₁, s₂ =>
  Sign.combineAtomic Sign.addAtomic s₁.atomicChoices s₂.atomicChoices

lemma Sign.add_comm (a b : Sign) : a.add b = b.add a := by
  cases a <;> cases b <;> simp [Sign.add, max, Sign.sup]

@[simp]
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

abbrev PosFact (n : Nat) (g : CFG) := GFact g (Domain n Sign)

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

set_option maxHeartbeats 240000 in
-- it seems that the default 200000 is just barely not enough to find this proof
-- and i cannot be arsed to optimize for a better one.
lemma Sign.add_mono_right (a b c : Sign) (h : a ⊔ b = a) :
    a.add c ⊔ b.add c = a.add c := by
  cases a <;> cases b <;> cases c <;>
    simp [max, Sign.sup, Sign.add, Sign.hasNeg, Sign.hasZero,
      Sign.hasPos, Sign.fromAtomFlags] at h ⊢

lemma Sign.add_mono (a b c d : Sign) (h₁ : a ⊔ b = a) (h₂ : c ⊔ d = c) :
    a.add c ⊔ b.add d = a.add c := by
  have int₁ := add_mono_right _ _ c h₁
  have int₂ := add_mono_right _ _ a h₂
  calc
  a.add c ⊔ b.add d
      = (a.add c ⊔ b.add c) ⊔ b.add d := by
          conv => lhs; rw [<- int₁]
  _   = a.add c ⊔ (b.add c ⊔ b.add d) := by
          rw [Sign.sup_assoc]
  _   = a.add c ⊔ b.add c := by
          rw [Sign.add_comm b c, Sign.add_comm b d, add_mono_right c d b h₂]
  _   = a.add c := int₁

set_option maxHeartbeats 240000 in
-- et simile
lemma Sign.sub_mono_right (a b c : Sign) (h : a ⊔ b = a) :
    a.sub c ⊔ b.sub c = a.sub c := by
  cases a <;> cases b <;> cases c <;>
    simp [max, Sign.sup, Sign.sub, Sign.hasNeg, Sign.hasZero,
      Sign.hasPos, Sign.fromAtomFlags] at h ⊢

set_option maxHeartbeats 400000 in
-- et simile
lemma Sign.sub_mono_left (a b c : Sign) (h : c ⊔ b = c) :
    a.sub c ⊔ a.sub b = a.sub c := by
  cases a <;> cases b <;> cases c <;>
    simp [max, Sign.sup, Sign.sub, Sign.hasNeg, Sign.hasZero,
      Sign.hasPos, Sign.fromAtomFlags] at h ⊢

set_option maxHeartbeats 1000000 in
-- needs big simp
-- provable but slow. isok.
lemma Sign.sub_mono (a b c d : Sign) (h₁ : a ⊔ b = a) (h₂ : c ⊔ d = c) :
    a.sub c ⊔ b.sub d = a.sub c := by
  have int₁ := Sign.sub_mono_right a b d h₁
  have int₂ := Sign.sub_mono_left a d c h₂
  calc
    a.sub c ⊔ b.sub d = (a.sub c ⊔ a.sub d) ⊔ b.sub d := by
      exact congrArg (fun x => x ⊔ b.sub d) (Eq.symm int₂)
    _ = a.sub c ⊔ (a.sub d ⊔ b.sub d) := by
      symm
      rw [Sign.sup_assoc]
    _ = a.sub c ⊔ a.sub d := by
      rw [int₁]
    _ = a.sub c := int₂

lemma Sign.meet_mono {a b c : Sign} (h : a ⊔ b = a) :
    (a ⊓ c) ⊔ (b ⊓ c) = a ⊓ c := by
  cases a <;> cases b <;> cases c <;>
    simp [max, Sign.sup, min, Sign.inf] at h ⊢

lemma Sign.meet_bot_right {x : Sign} :
    x ⊓ ⊥ = ⊥ := by
  cases x <;> simp [min, Sign.inf] <;> rfl

lemma Sign.meet_eq_of_join_right {a b c : Sign} (h : a ⊔ b = b) (hc : c ⊓ a = c) :
    c ⊓ b = c := by
  cases a <;> cases b <;> cases c <;>
    simp [max, Sign.sup, min, Sign.inf] at h hc ⊢

-- fake motive to apply false indcution.
def M (n : Nat) : (t : Tag) → Lang t → Prop
| .Expr, e =>
    ∀ x y : Domain n Sign, x ⊔ y = x →
      evalExprSign x e ⊔ evalExprSign y e = evalExprSign x e
| .Stmt, _ => True

lemma evalExprSign_mono {n : Nat} : ∀ e : Lang .Expr, M n .Expr e := by
  intro e
  refine (Lang.rec (motive := M n)
    ?hVar ?hTrue ?hFalse ?hNat ?hUnit ?hBinOp ?hUnOp ?hIf ?hWhile ?hBreak ?hScope
    ?hDecl ?hAssign ?hSeq ?hDo) e
  · intro x ρ₁ ρ₂ hxy
    simp [evalExprSign, getVar]
    by_cases h : x < n
    · simpa [h, max, Sign.fromAtomFlags] using congrFun hxy ⟨x, by assumption⟩
    · simp only [h, ↓reduceDIte]; rfl
  · intro x y hxy
    simp [evalExprSign, max, Sign.fromAtomFlags]
  · intro x y hxy
    simp [evalExprSign, max, Sign.fromAtomFlags]
  · intro n x y hxy
    simp only [max, Sign.sup, Sign.fromAtomFlags, Sign.hasNeg, evalExprSign, signOfNat,
      Bool.or_self, Sign.hasZero, Sign.hasPos]
    cases n <;> simp
  · intro x y hxy
    simp [evalExprSign, max, Sign.fromAtomFlags]
  · intro e₁ e₂ op ih₁ ih₂ ρ₁ ρ₂ hxy
    specialize ih₁ _ _ hxy
    specialize ih₂ _ _ hxy
    cases op <;> simp only [evalExprSign]
    · grind [Sign.add_mono]
    · grind [Sign.sub_mono]
    · simp [max]
    · simp [max]
  · intros a o ih
    intros x y hxy
    specialize ih x y hxy
    cases o <;> simp [evalExprSign, max, Sign.fromAtomFlags]
  · intros c e₁ e₂ _ ih₁ ih₂
    intros x y hxy
    specialize ih₁ x y hxy
    specialize ih₂ x y hxy
    unfold evalExprSign
    calc
      evalExprSign x e₁ ⊔ evalExprSign x e₂ ⊔
        (evalExprSign y e₁ ⊔ evalExprSign y e₂)
        =
        (evalExprSign x e₁ ⊔ evalExprSign y e₁) ⊔
        (evalExprSign x e₂ ⊔ evalExprSign y e₂) := by
          grind [Sign.sup_comm, Sign.sup_assoc]
      _ = evalExprSign x e₁ ⊔ evalExprSign x e₂ := by
        simp [ih₁, ih₂]
  · intros c b ihc ihb
    intros x y hxy
    simp [evalExprSign, max, Sign.fromAtomFlags]
  · intros l x y hxy
    simp [evalExprSign, max, Sign.fromAtomFlags]
  · intros s res ihs ihres
    intros x y hxy
    unfold evalExprSign
    exact ihres _ _ hxy
  · intros; simp only [M]
  · intros; simp only [M]
  · intros; simp only [M]
  · intros; simp only [M]

lemma excludeZero_mono {a b : Sign} (h : a ⊔ b = a) :
    a.excludeZero ⊔ b.excludeZero = a.excludeZero := by
  cases a <;> cases b <;> simp [Sign.excludeZero, max] at h ⊢

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

def runPositivity (n : Nat) (g : CFG)
    (entryInit : Domain n Sign := ⊥) : PosFact n g × PosFact n g :=
  runDataflowOf g transferPosNode transferPosEdge entryInit

def absPos : CEK -> Domain n Sign -> Prop := fun σ ρ =>
  σ.E.length ≤ n ∧
  ∀ x : Fin n,
    let concreteSign : Sign :=
      if h : x.val < σ.E.length then
        match σ.E[x.val] with
        | .Nat 0 => Sign.Zero
        | .Nat _ => Sign.Pos
        | .True | .False | .Unit => Sign.Top
      else
        Sign.Bot -- unreachable?
    concreteSign ⊓ (getVar ρ x.val) = concreteSign

theorem absPos_mono {σ : CEK} {a b : Domain n Sign}
    (hab : a ⊔ b = b) (habsa : absPos σ a) :
    absPos σ b := by
  obtain ⟨hlen, habsa⟩ := habsa
  refine ⟨hlen, ?_⟩
  intro x
  simp only [getVar, Fin.is_lt, ↓reduceDIte, Fin.eta]
  refine Sign.meet_eq_of_join_right (congrFun hab x) ?_
  simpa [getVar] using (habsa x)

lemma positivity_step_sound_core {s σ σ' nod nod'}
    (hrel : cfgcekRel s σ nod)
    (hrel' : cfgcekRel s σ' nod')
    (heval : Eval σ σ')
    (hreach : CFGReach (stmtCFG s) nod nod')
    (hfact : GFact (stmtCFG s) (Domain n Sign))
    (habs : absPos σ (hfact nod)) :
    absPos σ' (transferPosNode nod'.val
      (expectedInOf (stmtCFG s) transferPosEdge (fun _ => ⊥) hfact nod')) := by
  sorry

instance [TranslationReq s (cfgcekRel s)] :
  Framework (Domain n Sign) transferPosEdge transferPosNode s (cfgcekRel s) absPos where
  join_comm := fun a b => by
    funext x
    simp only [max, Sign.sup, Sign.hasNeg, Sign.hasZero, Sign.hasPos]
    cases (a x) <;> simp
  join_assoc :=  fun a b c => by
    funext x
    simp only [max, Sign.sup, Sign.hasNeg, Sign.hasZero, Sign.hasPos, Sign.fromAtomFlags]
    cases (a x) <;> cases (b x) <;> cases (c x) <;> simp
  join_idem := fun a => by
    funext x
    simp [max, Sign.sup, Sign.fromAtomFlags]
    cases (a x) <;> simp
  bot_le := fun a => by
    funext x
    simp [max, Sign.sup, Sign.fromAtomFlags]
    cases (a x) <;> simp
  node_mono := fun node => by
    intro x y hxy
    unfold transferPosNode transferScopedNode
    cases node.kind with
    | stmtExit s =>
      cases s with
        | Assign x₀ rhs =>
          funext i
          simp only [max, setVar]
          split
          case isTrue h =>
            apply evalExprSign_mono
            exact hxy
          case isFalse h =>
            simpa [h, ↓reduceIte] using congrFun hxy _
        | Decl _ _ =>
          funext i
          simp only [max, pushBinding]
          split
          case isTrue h =>
            apply evalExprSign_mono
            exact hxy
          case isFalse h =>
            split
            case isTrue h' =>
              apply congrFun hxy
            case isFalse h' => rfl
        | _ =>
          simpa using hxy
    | exprExit e =>
      cases e with
      | Scope s _ =>
        funext i
        simp only [max, popBindings]
        split
        case isTrue h =>
          apply congrFun hxy
        case isFalse h => rfl
      | _ => simpa using hxy
    | _ =>
      simpa using hxy
  edge_mono := by
    intro e x y hxy
    unfold transferPosEdge transferBranchEdge
    cases e.kind <;> try simpa using hxy
    · cases e.src.kind <;> try simpa using hxy
      case exprExit e =>
      cases e <;> try simpa [refineCond] using hxy
      case False =>
        simp only [refineCond]
        rfl
      case BinOp a₁ a₂ o =>
        simp only [refineCond]
        cases o <;> try simpa using hxy
        cases a₁ <;> cases a₂ <;> try simpa using hxy
        case Nat v n =>
          cases n <;> simp only
          case zero =>
            funext i
            rw [max_app]
            simp only [setVar]
            split
            case isTrue h =>
              apply Sign.meet_mono
              have : v < n := by grind
              simp only [max, Sign.sup, Sign.fromAtomFlags, Sign.hasNeg, getVar, this, ↓reduceDIte,
                Sign.hasZero, Sign.hasPos]
              exact congrFun hxy ⟨v, this⟩
            case isFalse h =>
              apply congrFun hxy
          case succ => exact hxy
        case Var n v =>
          cases n <;> simp only
          case zero =>
            funext i
            rw [max_app]
            simp only [setVar]
            split
            case isTrue h =>
              apply Sign.meet_mono
              have : v < n := by grind
              simp only [max, Sign.sup, Sign.fromAtomFlags, Sign.hasNeg, getVar, this, ↓reduceDIte,
                Sign.hasZero, Sign.hasPos]
              exact congrFun hxy ⟨v, this⟩
            case isFalse =>
              apply congrFun hxy
          case succ => exact hxy
      case UnOp a o =>
        simp only [refineCond]
        cases o <;> cases a <;> try simpa using hxy
        case Var v =>
        funext i
        simp only
        rw [max_app]
        simp only [setVar]
        split
        case isTrue h =>
          apply Sign.meet_mono
          have : v < n := by grind
          simp only [max, Sign.sup, Sign.fromAtomFlags, Sign.hasNeg, getVar, this, ↓reduceDIte,
            Sign.hasZero, Sign.hasPos]
          exact congrFun hxy ⟨v, this⟩
        case isFalse h =>
          apply congrFun hxy
    · cases e.src.kind <;> try simpa using hxy
      case exprExit e =>
      cases e <;> try simpa using hxy
      case True =>
        simp [refineCond]; rfl
      case BinOp a₁ a₂ o =>
        simp only [refineCond]
        cases o <;> try simpa using hxy
        cases a₁ <;> cases a₂ <;> try simpa using hxy
        case Nat v n =>
          cases n <;> simp only
          case zero =>
            funext i
            rw [max_app]
            by_cases hi : i.val = v
            · rw [<- hi]
              simp only [setVar, ↓reduceIte, getVar]
              apply excludeZero_mono
              have : i < n := by grind
              simpa [this, Max.max] using congrFun hxy i
            · simp only [max, Sign.sup, Sign.fromAtomFlags, Sign.hasNeg, setVar, hi, ↓reduceIte,
              Sign.hasZero, Sign.hasPos]
              exact congrFun hxy i
          case succ => exact hxy
        case Var n v =>
          cases n <;> simp only
          case zero =>
            funext i
            rw [max_app]
            simp only [setVar]
            split
            case isTrue h =>
              subst h
              apply excludeZero_mono
              simp only [getVar]
              have : i < n := by grind
              simpa [this, Max.max] using congrFun hxy i
            case isFalse => apply congrFun hxy
          case succ => exact hxy
      case UnOp a o =>
        simp only [refineCond]
        cases o <;> cases a <;> try simpa using hxy
        case Var v =>
          simp only
          funext i
          rw [max_app]
          simp only [setVar]
          split
          case isTrue h =>
            subst h
            apply excludeZero_mono
            simp only [getVar]
            have : i < n := by grind
            simpa [this, Max.max] using congrFun hxy i
          case isFalse h => apply congrFun hxy
  entryInit := (fun _ => ⊥)

  init_sound := by
    refine ⟨?_, ?_⟩
    · simp only [initState, List.length_nil, Nat.zero_le]
    · simp only [initState, List.length_nil, Nat.not_lt_zero, ↓reduceDIte, getVar, Fin.is_lt]
      simp [min, Sign.inf]
  abs_mono := absPos_mono

  abs_preserves_init := by
    intros a habsa
    simp only [absPos, initState, List.length_nil, Nat.zero_le, Nat.not_lt_zero, ↓reduceDIte,
      getVar, Fin.is_lt, Fin.eta, true_and] at habsa ⊢
    simp [min]

  step_sound := by
    intros σ σ' nod nod' hrel hrel' heval hreach hfact hfp habs
    apply absPos_mono (hfp nod')
    apply positivity_step_sound_core hrel hrel' heval hreach hfact habs

def positivityOverlay {n : Nat} {g : CFG} (inF outF : PosFact n g) : AltCFGRepr.DotOverlay :=
  { nodeMeta := fun node =>
      if h : node ∈ g.nodes then
        let nd := (⟨node, h⟩ : NodeOf g)
        [ s!"in={repr (inF nd)}"
        , s!"out={repr (outF nd)}"
        ]
      else
        [ "in=⊥", "out=⊥" ]
    edgeAttrs := fun e =>
      match e.kind with
      | .trueBranch => [("color", "darkgreen")]
      | .falseBranch => [("color", "firebrick")]
      | .back => [("color", "royalblue")]
      | .breakOut => [("style", "dashed"), ("color", "gray40")]
      | .normal => []
  }

def printResult {n : Nat} (g : CFG) (inF outF : PosFact n g) : IO Unit := do
  IO.println (AltCFGRepr.toDotWith g (positivityOverlay inF outF))

def main (_ : List String) : IO Unit := do
  let g := stmtCFG sampleProgram
  let (inF, outF) := runPositivity 10 g
  printResult g inF outF
