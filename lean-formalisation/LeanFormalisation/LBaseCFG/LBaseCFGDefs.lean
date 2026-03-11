-- CFGs.lean
-- CFG construction for the language defined in LBase.

import LeanFormalisation.LBase
import ControlFlow.Graphs.FuncGraph
import ControlFlow.Graphs.Digraph
import ControlFlow.Graphs.CFG

-- add classical logic instances to make proofs easier
noncomputable instance : DecidableEq Value := Classical.decEq _
noncomputable instance : DecidableEq BinOp := Classical.decEq _
noncomputable instance : DecidableEq UnOp  := Classical.decEq _
noncomputable instance : DecidableEq τ     := Classical.decEq _
noncomputable instance : DecidableEq Expr  := Classical.decEq _
noncomputable instance : DecidableEq Stmt  := Classical.decEq _

-- define symbolic representaiton of control flow
-- Control mode
inductive CFGControl where
  | sourceStmt (s : Stmt)
  | sourceExpr (e : Expr)
  | value   -- a value has been produced; its identity is irrelevant
  | skip    -- the current statement has completed
deriving Repr

-- continuation mode
inductive CFGCont where
  | ifCondK  (s₁ s₂ : Stmt)
  | jumpK                          -- scope-exit marker (erased depth)
  | declK    (x : VarName) (tp : τ)
  | assignK  (x : VarName)
  | seqK     (s : Stmt)
  | binopLK  (op : BinOp) (e₂ : Expr)
  | binopRK  (op : BinOp)          -- right-hand value is forgotten
  | unopK    (op : UnOp)
  | loopK    (c : Expr) (body : Stmt)
deriving Repr

noncomputable instance : DecidableEq CFGControl := Classical.decEq _
noncomputable instance : DecidableEq CFGCont    := Classical.decEq _

-- a full node!
structure CFGNode where
  control : CFGControl
  kont    : List CFGCont
deriving Repr

noncomputable instance : DecidableEq CFGNode := Classical.decEq _

-- CEK state to CFG projection
@[local simp]
def toCFGControl : Control → CFGControl
  | .sourceExpr e => .sourceExpr e
  | .sourceStmt s => .sourceStmt s
  | .value _      => .value
  | .skip         => .skip

def toCFGCont : Cont → CFGCont
  | .ifCondK s₁ s₂  => .ifCondK s₁ s₂
  | .jumpK _        => .jumpK
  | .declK x tp     => .declK x tp
  | .assignK x       => .assignK x
  | .seqK s          => .seqK s
  | .binopLK op e₂   => .binopLK op e₂
  | .binopRK op _    => .binopRK op
  | .unopK op        => .unopK op
  | .loopK c s       => .loopK c s

def fromCFGCont : CFGCont → Cont
  | .ifCondK s₁ s₂  => .ifCondK s₁ s₂
  | .jumpK          => .jumpK 0         -- Dummy scope depth (0 is fine if env depth is 0)
  | .declK x tp     => .declK x tp
  | .assignK x      => .assignK x
  | .seqK s         => .seqK s
  | .binopLK op e₂  => .binopLK op e₂
  | .binopRK op     => .binopRK op .True -- Supply a dummy value like .True
  | .unopK op       => .unopK op
  | .loopK c s      => .loopK c s

@[local simp, grind =, grind! .]
theorem to_from_CFGCont_eq (c : CFGCont) :
    (toCFGCont (fromCFGCont c)) = c := by
  cases c <;> rfl

@[local simp, grind =, grind! .]
theorem to_from_CFGCont_list_eq (k : List CFGCont) : (k.map fromCFGCont |>.map toCFGCont) = k := by
  induction k <;> simp [*]

@[local simp, grind]
def toNode (state : CEK) : CFGNode :=
  ⟨toCFGControl state.1, state.2.2.map toCFGCont⟩

def cfgInit (s : Stmt) : CFGNode := ⟨.sourceStmt s, []⟩

-- `succs` mirrors the Eval relation: for each Eval constructor there is
-- a corresponding case below.  For branching rules (IfTrue/IfFalse,
-- LoopTrue/LoopFalse) we return both successors.
def CFGNode.succs (n : CFGNode) : List CFGNode :=
  match n.control, n.kont with
  -- ── Source expressions ────────────────────────────────────────────
  -- Literal values (True, False, Nat _) and variable lookups always
  -- produce a value.  These correspond to the Val and Var rules.
  | .sourceExpr .True,    K
  | .sourceExpr .False,   K
  | .sourceExpr (.Nat _), K
  | .sourceExpr (.Var _), K => [⟨.value, K⟩]
  -- BinOp: push binopLK and evaluate the left argument first.
  | .sourceExpr (.BinOp e₁ e₂ op), K =>
      [⟨.sourceExpr e₁, .binopLK op e₂ :: K⟩]
  -- UnOp: push unopK and evaluate the argument.
  | .sourceExpr (.UnOp e op), K =>
      [⟨.sourceExpr e, .unopK op :: K⟩]
  -- ── Source statements ─────────────────────────────────────────────
  -- Variable declaration: evaluate the initialiser, bind afterwards.
  | .sourceStmt (.Decl x tp e), K =>
      [⟨.sourceExpr e, .declK x tp :: K⟩]
  -- Assignment: evaluate the right-hand side.
  | .sourceStmt (.Assign x e), K =>
      [⟨.sourceExpr e, .assignK x :: K⟩]
  -- Sequence: run s₁ first, remembering s₂.
  | .sourceStmt (.Seq s₁ s₂), K =>
      [⟨.sourceStmt s₁, .seqK s₂ :: K⟩]
  -- If: evaluate the condition; the branch is chosen by the ifCondK frame.
  | .sourceStmt (.If e s₁ s₂), K =>
      [⟨.sourceExpr e, .ifCondK s₁ s₂ :: K⟩]
  -- While: push loopK (back-edge marker) and jumpK (scope-exit marker),
  -- then evaluate the condition.
  | .sourceStmt (.While c body), K =>
      [⟨.sourceExpr c, .loopK c body :: .jumpK :: K⟩]
  -- ── Continuation pop rules ────────────────────────────────────────
  -- If-condition done: two branches, each entering a fresh scope.
  -- (Concrete: IfTrue / IfFalse)
  | .value, .ifCondK s₁ s₂ :: K =>
      [ ⟨.sourceStmt s₁, .jumpK :: K⟩  -- taken branch
      , ⟨.sourceStmt s₂, .jumpK :: K⟩  -- not-taken branch
      ]
  -- Scope exit: pop the jumpK marker and continue.
  -- (Concrete: ScopeDone)
  | .skip, .jumpK :: K =>
      [⟨.skip, K⟩]
  -- Declaration done: initialiser evaluated, now skip.
  -- (Concrete: VarDeclDone)
  | .value, .declK _ _ :: K =>
      [⟨.skip, K⟩]
  -- Assignment done: value has been stored, now skip.
  -- (Concrete: AssignDone)
  | .value, .assignK _ :: K =>
      [⟨.skip, K⟩]
  -- Sequence: first statement done, start the second.
  -- (Concrete: SeqDone)
  | .skip, .seqK s₂ :: K =>
      [⟨.sourceStmt s₂, K⟩]
  -- BinOp left done: pop binopLK, push binopRK, evaluate the right subexpr.
  -- (Concrete: BinOpL)
  | .value, .binopLK op e₂ :: K =>
      [⟨.sourceExpr e₂, .binopRK op :: K⟩]
  -- BinOp right done: both operands evaluated, result is a value.
  -- (Concrete: BinOpR)
  | .value, .binopRK _ :: K =>
      [⟨.value, K⟩]
  -- UnOp done: argument evaluated, result is a value.
  -- (Concrete: UnOpDone)
  | .value, .unopK _ :: K =>
      [⟨.value, K⟩]
  -- Loop condition: two successors.
  --   LoopTrue:  enter the body (loopK stays for the back-edge).
  --   LoopFalse: exit the loop (jumpK is still on the kont; ScopeDone
  --              will pop it in the next step).
  -- (Concrete: LoopTrue / LoopFalse)
  | .value, .loopK c body :: K =>
      [ ⟨.sourceStmt body, .loopK c body :: K⟩  -- LoopTrue: keep loopK
      , ⟨.skip, K⟩                               -- LoopFalse: exit
      ]
  -- Loop body done: re-evaluate the condition (back-edge).
  -- (Concrete: LoopCont)
  | .skip, .loopK c body :: K =>
      [⟨.sourceExpr c, .loopK c body :: K⟩]
  | .skip,  [] => []   -- normal program termination
  | .value, [] => []   -- value with empty kont (well-typed programs halt at .skip)

  -- All other combinations are unreachable in a well-formed execution.
  | _, _ => []


-- # Completeness
-- Every step corresponds to some edge in the CFG

-- extracted for readability. Thanks Lean Linter!
local macro "cfg_simp" : tactic => `(tactic|
  simp only [
    CFGNode.succs, toCFGControl, toCFGCont, toNode,
    CFGNode.mk.injEq, CFGControl.sourceStmt.injEq,
    List.map_cons, List.mem_cons, List.not_mem_nil, List.cons_ne_self, List.ne_cons_self,
    reduceCtorEq, and_true, and_self, or_false, or_true, true_or, or_self
  ])

theorem eval_maps_to_succ {src dst : CEK} (h : Eval src dst) :
    toNode dst ∈ (toNode src).succs := by
  cases h <;> cfg_simp
  case Val E K v =>
    cases v <;> simp [liftValue]

-- # Soundness
-- Every edge in the CFG corresponds to some edge in the CFG

-- automate the procedure of showing that a node is indeed the correct reduction
local macro "solve_node" dst:term : tactic =>
  `(tactic | (exact ⟨$dst, by constructor, by simp [to_from_CFGCont_list_eq _]⟩))

-- only needed for cases where constructor chooses not to work for mysterious reasons
local macro "solve_node'" dst:term : tactic =>
  `(tactic | (refine ⟨$dst, ?_, by simp [to_from_CFGCont_list_eq _]⟩))


-- this proof could be heavily simplified to be quite honest but i'll take care
-- of that another day
theorem succ_is_inhabited {n m : CFGNode} (h : m ∈ n.succs) :
    ∃ (src : CEK), toNode src = n ∧
    ∃ (dst : CEK), Eval src dst ∧ toNode dst = m := by
  obtain ⟨c, k⟩ := n
  simp only [CFGNode.succs] at h
  cases c with
  -- statement
  | sourceStmt s =>
    exists ⟨.sourceStmt s, [], k.map fromCFGCont⟩
    cases s <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      subst h <;> refine ⟨by simp [to_from_CFGCont_list_eq _], ?_⟩
    case Decl x typ e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.declK x typ :: k).map fromCFGCont⟩
    case Assign x e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.assignK x :: k).map fromCFGCont⟩
    case Seq s₁ s₂ =>
      solve_node  ⟨.sourceStmt s₁, [], (CFGCont.seqK s₂ :: k).map fromCFGCont⟩
    case If e s₁ s₂ =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.ifCondK s₁ s₂ :: k).map fromCFGCont⟩
    case While c body =>
      solve_node ⟨.sourceExpr c, [∅], (CFGCont.loopK c body :: CFGCont.jumpK :: k).map fromCFGCont⟩
  -- expressions
  | sourceExpr e =>
    exists ⟨.sourceExpr e, [], k.map fromCFGCont⟩
    refine ⟨by simp [to_from_CFGCont_list_eq k], ?_⟩
    cases e <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h
    case Var x =>
      solve_node' ⟨.value default, [], k.map fromCFGCont⟩
      apply Eval.Var default
    case True =>
      solve_node' ⟨.value .True, [], k.map fromCFGCont⟩
      exact Eval.Val .True
    case False =>
      solve_node' ⟨.value .False, [], k.map fromCFGCont⟩
      exact Eval.Val .False
    case Nat n =>
      solve_node' ⟨.value (.Nat n), [], k.map fromCFGCont⟩
      exact Eval.Val (.Nat n)
    case BinOp arg₁ arg₂ o =>
      solve_node ⟨.sourceExpr arg₁, [], (CFGCont.binopLK o arg₂ :: k).map fromCFGCont⟩
    case UnOp arg o =>
      solve_node ⟨.sourceExpr arg, [], (CFGCont.unopK o :: k).map fromCFGCont⟩
  -- values
  | value =>
    cases k <;> try simp at h
    case cons hd tl =>
    cases hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> try subst h
    case ifCondK s₁ s₂ =>
      rcases h with rfl | rfl
      · exists ⟨.value .True, [], (CFGCont.ifCondK s₁ s₂ :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq _], ?_⟩
        exists ⟨.sourceStmt s₁, [∅], Cont.jumpK 0 :: tl.map fromCFGCont⟩
        split_ands <;> try constructor
        · simp [toCFGCont, to_from_CFGCont_list_eq tl]
      · exists ⟨.value .False, [], (CFGCont.ifCondK s₁ s₂ :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq _], ?_⟩
        exists ⟨.sourceStmt s₂, [∅], Cont.jumpK 0 :: tl.map fromCFGCont⟩
        split_ands <;> try constructor
        · simp [toCFGCont, to_from_CFGCont_list_eq tl]
    case declK x typ =>
      exists ⟨.value .True, [∅], (CFGCont.declK x typ :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.skip, insert_first x .True [∅], tl.map fromCFGCont⟩
    case assignK x =>
      exists ⟨.value .True, [∅], (CFGCont.assignK x :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.skip, insert_first x .True [∅], tl.map fromCFGCont⟩
    case binopLK o arg₂ =>
      exists ⟨.value .True, [], (CFGCont.binopLK o arg₂ :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.sourceExpr arg₂, [], (CFGCont.binopRK o :: tl).map fromCFGCont⟩
    case binopRK o =>
      exists ⟨.value .True, [], (CFGCont.binopRK o :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.value (o.run .True .True), [], tl.map fromCFGCont⟩
    case unopK o =>
      exists ⟨.value .True, [], (CFGCont.unopK o :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.value (o.run .True), [], tl.map fromCFGCont⟩
    case loopK c body =>
      rcases h with rfl | rfl
      · exists ⟨.value .True, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
        solve_node ⟨.sourceStmt body, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
      · exists ⟨.value .False, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
        solve_node ⟨.skip, [], tl.map fromCFGCont⟩
  -- skip
  | skip =>
    cases k <;> try simp at h
    case cons hd tl =>
    exists ⟨.skip, [], (hd :: tl).map fromCFGCont⟩
    refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
    cases hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> try subst h
    case jumpK =>
      solve_node ⟨.skip, [], tl.map fromCFGCont⟩
    case seqK s =>
      solve_node ⟨.sourceStmt s, [], tl.map fromCFGCont⟩
    case loopK c body =>
      solve_node ⟨.sourceExpr c, [∅], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
-- QED

theorem succs_iff_exists_eval (n m : CFGNode) :
    m ∈ n.succs ↔ ∃ (src dst : CEK), toNode src = n ∧ toNode dst = m ∧ Eval src dst := by
  constructor
  · intro h
    obtain ⟨src, h_src, dst, h_eval, h_dst⟩ := succ_is_inhabited h
    exact ⟨src, dst, h_src, h_dst, h_eval⟩
  · intro ⟨src, dst, h_src, h_dst, h_eval⟩
    have h_succ := eval_maps_to_succ h_eval
    rw [h_src, h_dst] at h_succ
    exact h_succ

-- Example LBase program:
-- let x : Nat = 5;
-- while (true) { x = 0; }
def exampleProgram : Stmt :=
  .Seq (.Decl 0 .Nat (.Nat 5))
        (.While .True
          (.Assign 0 (.Nat 0)))

def exampleCFG : CFGNode := cfgInit exampleProgram

#eval exampleCFG.succs
