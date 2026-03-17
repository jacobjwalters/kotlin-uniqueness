-- LBaseCFGDefs.lean
-- CFG construction for the language defined in LBase.

import LeanFormalisation.LBase

-- define symbolic representation of control flow
-- Control mode: same structure as `Control` but with values erased
inductive CFGControl where
  | sourceStmt (s : Lang .Stmt)
  | sourceExpr (e : Lang .Expr)
  | value   -- a value has been produced; its identity is irrelevant
  | skip    -- the current statement has completed
deriving Repr, DecidableEq

-- Continuation mode: mirrors `Cont` with runtime values / env depths erased.
--   * `declK` drops VarName  (variables are positional in the flat env)
--   * `binopRK` drops the right-hand value
--   * `loopK / loopContK / scopeBodyK / scopeExitK` drop the env-depth `n`
inductive CFGCont where
  | ifCondK    (e₁ e₂ : Lang .Expr)
  | declK      (tp : τ)
  | assignK    (x : VarName)
  | seqK       (s : Lang .Stmt)
  | binopLK    (op : BinOp) (e₂ : Lang .Expr)
  | binopRK    (op : BinOp)
  | unopK      (op : UnOp)
  | loopK      (c : Lang .Expr) (body : Lang .Expr)
  | loopContK  (c : Lang .Expr) (body : Lang .Expr)
  | scopeBodyK (e : Lang .Expr)
  | scopeExitK
  | exprStmtK
deriving Repr, DecidableEq

-- a full node!
structure CFGNode where
  control : CFGControl
  kont    : List CFGCont
deriving Repr, DecidableEq

-- CEK state to CFG projection
@[local simp]
def toCFGControl : Control → CFGControl
  | .sourceExpr e => .sourceExpr e
  | .sourceStmt s => .sourceStmt s
  | .value _      => .value
  | .skip         => .skip

def toCFGCont : Cont → CFGCont
  | .ifCondK e₁ e₂      => .ifCondK e₁ e₂
  | .declK tp            => .declK tp
  | .assignK x           => .assignK x
  | .seqK s              => .seqK s
  | .binopLK op e₂       => .binopLK op e₂
  | .binopRK op _        => .binopRK op
  | .unopK op            => .unopK op
  | .loopK c body _      => .loopK c body
  | .loopContK c body _  => .loopContK c body
  | .scopeBodyK e _      => .scopeBodyK e
  | .scopeExitK _        => .scopeExitK
  | .exprStmtK           => .exprStmtK

def fromCFGCont : CFGCont → Cont
  | .ifCondK e₁ e₂      => .ifCondK e₁ e₂
  | .declK tp            => .declK tp
  | .assignK x           => .assignK x
  | .seqK s              => .seqK s
  | .binopLK op e₂       => .binopLK op e₂
  | .binopRK op          => .binopRK op .True    -- dummy right-hand value
  | .unopK op            => .unopK op
  | .loopK c body        => .loopK c body 0      -- dummy env depth
  | .loopContK c body    => .loopContK c body 0  -- dummy env depth
  | .scopeBodyK e        => .scopeBodyK e 0      -- dummy env depth
  | .scopeExitK          => .scopeExitK 0        -- dummy env depth
  | .exprStmtK           => .exprStmtK

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

def cfgInit (s : Lang .Stmt) : CFGNode := ⟨.sourceStmt s, []⟩

-- Pop loop frames off a CFG continuation stack until reaching a `loopK`
-- or `loopContK`, which is then removed. Mirrors `popLoopK` on the CEK side.
def popCFGLoopK : List CFGCont → List CFGCont
  | .loopK _ _ :: li     => li
  | .loopContK _ _ :: li => li
  | _ :: li              => popCFGLoopK li
  | []                   => []   -- degenerate: Break outside any loop

-- `succs` mirrors the Eval relation: for each Eval constructor there is
-- a corresponding case below.  For branching rules (IfTrue/IfFalse,
-- LoopTrue/LoopFalse) we return both successors.
def CFGNode.succs (n : CFGNode) : List CFGNode :=
  match n.control, n.kont with
  -- ── Source expressions ────────────────────────────────────────────
  -- Literal values and variable lookups always produce a value.
  -- (Eval.Val, Eval.Var)
  | .sourceExpr .True,    K
  | .sourceExpr .False,   K
  | .sourceExpr .Unit,    K
  | .sourceExpr (.Nat _), K
  | .sourceExpr (.Var _), K => [⟨.value, K⟩]
  -- BinOp: push binopLK and evaluate the left argument first.
  -- (Eval.BinOp)
  | .sourceExpr (.BinOp e₁ e₂ op), K =>
      [⟨.sourceExpr e₁, .binopLK op e₂ :: K⟩]
  -- UnOp: push unopK and evaluate the argument.
  -- (Eval.UnOp)
  | .sourceExpr (.UnOp e op), K =>
      [⟨.sourceExpr e, .unopK op :: K⟩]
  -- If (expression): evaluate condition, branches chosen via ifCondK.
  -- (Eval.If)
  | .sourceExpr (.If e e₁ e₂), K =>
      [⟨.sourceExpr e, .ifCondK e₁ e₂ :: K⟩]
  -- While (expression): push loopK and evaluate the condition.
  -- (Eval.While)
  | .sourceExpr (.While c body), K =>
      [⟨.sourceExpr c, .loopK c body :: K⟩]
  -- Break: pop stack past the nearest loop frame.
  -- (Eval.Break)
  | .sourceExpr .Break, K =>
      [⟨.skip, popCFGLoopK K⟩]
  -- Scope: run statement body first, then evaluate the result expression.
  -- (Eval.Scope)
  | .sourceExpr (.Scope s e), K =>
      [⟨.sourceStmt s, .scopeBodyK e :: K⟩]
  -- ── Source statements ─────────────────────────────────────────────
  -- Variable declaration: evaluate the initialiser, bind positionally.
  -- (Eval.VarDecl)
  | .sourceStmt (.Decl tp e), K =>
      [⟨.sourceExpr e, .declK tp :: K⟩]
  -- Assignment: evaluate the right-hand side.
  -- (Eval.Assign)
  | .sourceStmt (.Assign x e), K =>
      [⟨.sourceExpr e, .assignK x :: K⟩]
  -- Sequence: run s₁ first, remembering s₂.
  -- (Eval.Seq)
  | .sourceStmt (.Seq s₁ s₂), K =>
      [⟨.sourceStmt s₁, .seqK s₂ :: K⟩]
  -- Expression statement: evaluate e and discard the result.
  -- (Eval.ExprStmt)
  | .sourceStmt (.Do e), K =>
      [⟨.sourceExpr e, .exprStmtK :: K⟩]
  -- ── Continuation pop rules ────────────────────────────────────────
  -- If-condition done: two branches (both are expressions in the new Lang).
  -- (Eval.IfTrue / Eval.IfFalse)
  | .value, .ifCondK e₁ e₂ :: K =>
      [ ⟨.sourceExpr e₁, K⟩   -- true branch
      , ⟨.sourceExpr e₂, K⟩   -- false branch
      ]
  -- Declaration done: value bound positionally, continue as skip.
  -- (Eval.VarDeclDone)
  | .value, .declK _ :: K =>
      [⟨.skip, K⟩]
  -- Assignment done: value stored, continue as skip.
  -- (Eval.AssignDone)
  | .value, .assignK _ :: K =>
      [⟨.skip, K⟩]
  -- BinOp left done: evaluate the right sub-expression.
  -- (Eval.BinOpL)
  | .value, .binopLK op e₂ :: K =>
      [⟨.sourceExpr e₂, .binopRK op :: K⟩]
  -- BinOp right done: result is a value.
  -- (Eval.BinOpR)
  | .value, .binopRK _ :: K =>
      [⟨.value, K⟩]
  -- UnOp done: result is a value.
  -- (Eval.UnOpDone)
  | .value, .unopK _ :: K =>
      [⟨.value, K⟩]
  -- Loop condition evaluated: two successors.
  --   LoopTrue:  enter body (loopK stays for the back-edge).
  --   LoopFalse: exit the loop (value .Unit propagates upward).
  -- (Eval.LoopTrue / Eval.LoopFalse)
  | .value, .loopK c body :: K =>
      [ ⟨.sourceExpr body, .loopK c body :: K⟩   -- LoopTrue
      , ⟨.value, K⟩                               -- LoopFalse (.Unit exits)
      ]
  -- Loop body done via loopContK back-edge: re-evaluate condition.
  -- (Eval.LoopCont)
  | .value, .loopContK c body :: K =>
      [⟨.sourceExpr c, .loopK c body :: K⟩]
  -- Scope result produced: restore outer env depth (erased in CFG).
  -- (Eval.ScopeExit)
  | .value, .scopeExitK :: K =>
      [⟨.value, K⟩]
    -- No Eval rule consumes `.exprStmtK` after producing a value,
    -- so this state has no outgoing edge in the CFG either.
  | .value, .exprStmtK :: _ =>
      []
  -- Sequence: first statement done, start the second.
  -- (Eval.SeqDone)
  | .skip, .seqK s₂ :: K =>
      [⟨.sourceStmt s₂, K⟩]
  -- Scope statement body done: evaluate the result expression.
  -- (Eval.ScopeBody)
  | .skip, .scopeBodyK e :: K =>
      [⟨.sourceExpr e, .scopeExitK :: K⟩]
  | .skip,  [] => []   -- normal program termination
  | .value, [] => []   -- top-level value (well-typed programs halt at .skip)

  -- All other combinations are unreachable in a well-formed execution.
  | _, _ => []


-- # Completeness
-- Every CEK step corresponds to some edge in the CFG.

-- `popLoopK` commutes with `toCFGCont`.
lemma popLoopK_toCFGCont (K : List Cont) :
    (popLoopK K).1.map toCFGCont = popCFGLoopK (K.map toCFGCont) := by
  induction K with
  | nil =>
    exact Eq.symm List.toList_toArray
  | cons hd tl ih =>
    cases hd <;> simp [popLoopK, popCFGLoopK, toCFGCont, ih]

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
  case Break E K =>
    simp [popLoopK_toCFGCont]

-- # Soundness
-- Every edge in the CFG has a concrete Eval witness.

-- automate the procedure of showing that a node is indeed the correct reduction
local macro "solve_node" dst:term : tactic =>
  `(tactic | (exact ⟨$dst, by constructor, by simp [to_from_CFGCont_list_eq _]⟩))

-- only needed for cases where constructor chooses not to work for mysterious reasons
local macro "solve_node'" dst:term : tactic =>
  `(tactic | (refine ⟨$dst, ?_, by simp [to_from_CFGCont_list_eq _]⟩))

-- `popLoopK` on the `fromCFGCont`-mapped stack commutes back to `popCFGLoopK`.
lemma popCFGLoopK_fromCFGCont (k : List CFGCont) :
    (popLoopK (k.map fromCFGCont)).1.map toCFGCont = popCFGLoopK k := by
  induction k with
  | nil =>
    exact Eq.symm List.toList_toArray
  | cons hd tl ih =>
    cases hd <;>
      simp [fromCFGCont, popLoopK, popCFGLoopK, to_from_CFGCont_list_eq tl, ih]

theorem succ_is_inhabited {n m : CFGNode} (h : m ∈ n.succs) :
    ∃ (src : CEK), toNode src = n ∧
    ∃ (dst : CEK), Eval src dst ∧ toNode dst = m := by
  obtain ⟨c, k⟩ := n
  simp only [CFGNode.succs] at h
  cases c with
  -- statements
  | sourceStmt s =>
    exists ⟨.sourceStmt s, [], k.map fromCFGCont⟩
    cases s <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;>
      subst h <;> refine ⟨by simp [to_from_CFGCont_list_eq _], ?_⟩
    case Decl tp e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.declK tp :: k).map fromCFGCont⟩
    case Assign x e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.assignK x :: k).map fromCFGCont⟩
    case Seq s₁ s₂ =>
      solve_node ⟨.sourceStmt s₁, [], (CFGCont.seqK s₂ :: k).map fromCFGCont⟩
    case Do e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.exprStmtK :: k).map fromCFGCont⟩
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
    case Unit =>
      solve_node' ⟨.value .Unit, [], k.map fromCFGCont⟩
      exact Eval.Val .Unit
    case BinOp arg₁ arg₂ o =>
      solve_node ⟨.sourceExpr arg₁, [], (CFGCont.binopLK o arg₂ :: k).map fromCFGCont⟩
    case UnOp arg o =>
      solve_node ⟨.sourceExpr arg, [], (CFGCont.unopK o :: k).map fromCFGCont⟩
    case If cond e₁ e₂ =>
      solve_node ⟨.sourceExpr cond, [], (CFGCont.ifCondK e₁ e₂ :: k).map fromCFGCont⟩
    case While c body =>
      solve_node ⟨.sourceExpr c, [], (CFGCont.loopK c body :: k).map fromCFGCont⟩
    case Break =>
      -- src = (Break, [], k mapped); dst = (skip, [], pop past loop frame)
      refine ⟨⟨.skip, [], (popLoopK (k.map fromCFGCont)).1⟩, ?_, ?_⟩
      · simpa [List.take_nil] using (Eval.Break (E := []))
      simp [popCFGLoopK_fromCFGCont]
    case Scope s e =>
      solve_node ⟨.sourceStmt s, [], (CFGCont.scopeBodyK e :: k).map fromCFGCont⟩
  -- values
  | value =>
    cases k <;> try simp at h
    case cons hd tl =>
    cases hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> try subst h
    case ifCondK e₁ e₂ =>
      rcases h with rfl | rfl
      · -- true branch: witness with value .True
        exists ⟨.value .True, [], (CFGCont.ifCondK e₁ e₂ :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
        exists ⟨.sourceExpr e₁, [], tl.map fromCFGCont⟩
        exact ⟨Eval.IfTrue e₁ e₂, by simp [to_from_CFGCont_list_eq tl]⟩
      · -- false branch: witness with value .False
        exists ⟨.value .False, [], (CFGCont.ifCondK e₁ e₂ :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
        exists ⟨.sourceExpr e₂, [], tl.map fromCFGCont⟩
        exact ⟨Eval.IfFalse e₁ e₂, by simp [to_from_CFGCont_list_eq tl]⟩
    case declK tp =>
      exists ⟨.value .True, [], (CFGCont.declK tp :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.skip, [.True], tl.map fromCFGCont⟩
    case assignK x =>
      exists ⟨.value .True, [.True], (CFGCont.assignK x :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.skip, [.True].set x .True, tl.map fromCFGCont⟩
    case binopLK o e₂ =>
      exists ⟨.value .True, [], (CFGCont.binopLK o e₂ :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.sourceExpr e₂, [], (CFGCont.binopRK o :: tl).map fromCFGCont⟩
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
        solve_node ⟨.sourceExpr body, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
      · exists ⟨.value .False, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
        refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
        solve_node ⟨.value .Unit, [], tl.map fromCFGCont⟩
    case loopContK c body =>
      exists ⟨.value .Unit, [], (CFGCont.loopContK c body :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node ⟨.sourceExpr c, [], (CFGCont.loopK c body :: tl).map fromCFGCont⟩
    case scopeExitK =>
      exists ⟨.value .True, [], (CFGCont.scopeExitK :: tl).map fromCFGCont⟩
      refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
      solve_node' ⟨.value .True, [].take 0, tl.map fromCFGCont⟩
      simpa [List.take_nil] using Eval.ScopeExit .True 0
  -- skip
  | skip =>
    cases k <;> try simp at h
    case cons hd tl =>
    exists ⟨.skip, [], (hd :: tl).map fromCFGCont⟩
    refine ⟨by simp [to_from_CFGCont_list_eq tl], ?_⟩
    cases hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> try subst h
    case seqK s =>
      solve_node ⟨.sourceStmt s, [], tl.map fromCFGCont⟩
    case scopeBodyK e =>
      solve_node ⟨.sourceExpr e, [], (CFGCont.scopeExitK :: tl).map fromCFGCont⟩
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
-- let _ : Nat = 5;
-- while (true) {
--   scope { _₀ = 0 } in unit
-- }
def exampleProgram : Lang .Stmt :=
  .Seq (.Decl .Nat (.Nat 5))
       (.Do (.While .True (.Scope (.Assign 0 (.Nat 0)) .Unit)))

def exampleCFG : CFGNode := cfgInit exampleProgram

#eval exampleCFG.succs
