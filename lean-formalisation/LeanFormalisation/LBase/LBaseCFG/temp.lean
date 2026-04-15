import LeanFormalisation.LBase.LBaseCFG.AltCFG
import LeanFormalisation.LBase.LBaseCFG.Correspondence

/-!
# Correspondence Relation between CEK and CFG
This file defines a concrete correspondence relation `R : StateRel` that
tracks which CFG node a CEK machine state corresponds to, suitable for
instantiating `TranslationReq`.
## Design Overview
The key insight is that the CEK continuation stack mirrors the nesting structure
of `buildStmt`/`buildExpr`. Each continuation frame (e.g., `declK`, `seqK`,
`binopLK`) tells us which parent AST node we're inside and which child we're
currently processing. Combined with the `Control` component, this uniquely
determines the CFG node (up to shared sub-expressions).
The relation is defined as a pair of mutual inductives:
- `StmtCorr bts nid s σ n`: CEK state `σ` corresponds to node `n` in the
  CFG built by `buildStmt bts nid s`
- `ExprCorr bts nid e σ n`: CEK state `σ` corresponds to node `n` in the
  CFG built by `buildExpr bts nid e`
### "Transparent" vs "Framed" Children
Some AST nodes push a continuation frame when entering a child (e.g., `Decl`
pushes `declK`), while others are "transparent" — the child executes with the
parent's continuation stack (e.g., after branching in `If`, or executing `s₂`
in `Seq s₁ s₂` after `s₁` completes).
For framed children, the constructor peels the frame off `K`.
For transparent children, the constructor passes `σ` through unchanged.
### Multiple Related Nodes
Because `R` is a relation (not a function), a single CEK state may be related
to multiple CFG nodes. For example, `⟨.skip, E, J, []⟩` is related to both
the innermost statement's exit node AND the program's top-level exit node.
This is intentional and required for `terminal_related`.
-/
open LeanFormalisation
open LeanFormalisation.AltCFG
open LeanFormalisation.AltCFG.Internal
namespace LeanFormalisation.AltCFGProofs
-- `StmtCorr bts nid s σ n` holds when CEK state `σ` is "at" CFG node `n`
-- within the CFG fragment built by `buildStmt bts nid s`.
--
-- `ExprCorr bts nid e σ n` holds when CEK state `σ` is "at" CFG node `n`
-- within the CFG fragment built by `buildExpr bts nid e`.
--
-- Constructors are grouped by AST node. "Framed" constructors peel a
-- continuation frame off `K`; "transparent" constructors (e.g. `seqInRight`,
-- `ifInTrue`, `ifInFalse`) pass the CEK state through unchanged, modelling
-- the fact that those children execute without adding a Seq/If frame to K.
set_option relaxedAutoImplicit true in
mutual
inductive StmtCorr :
    List CFGNode → Nat → Lang .Stmt → CEK → CFGNode → Prop where
  -- At the entry of statement s
  | entry (s : Lang .Stmt) (E J K) :
      StmtCorr bts nid s ⟨.sourceStmt s, E, J, K⟩ ⟨nid, .stmtEntry s⟩
  -- At the exit of statement s
  | exit (s : Lang .Stmt) (E J K) :
      StmtCorr bts nid s ⟨.skip, E, J, K⟩ ⟨nid + 1, .stmtExit s⟩
  -- Decl: inside the init expression (declK on stack)
  | declInExpr (ty : Ty) (e : Lang .Expr) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) e ⟨C, E, J, K⟩ n →
      StmtCorr bts nid (.Decl ty e) ⟨C, E, J, .declK ty :: K⟩ n
  -- Assign: inside the RHS expression (assignK on stack)
  | assignInExpr (x : VarName) (e : Lang .Expr) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) e ⟨C, E, J, K⟩ n →
      StmtCorr bts nid (.Assign x e) ⟨C, E, J, .assignK x :: K⟩ n
  -- Seq: inside s₁ (seqK s₂ on stack)
  | seqInLeft (s₁ s₂ : Lang .Stmt) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      StmtCorr bts (nid + 2) s₁ ⟨C, E, J, K⟩ n →
      StmtCorr bts nid (.Seq s₁ s₂) ⟨C, E, J, .seqK s₂ :: K⟩ n
  -- Seq: inside s₂ (transparent — no Seq frame on K)
  | seqInRight (s₁ s₂ : Lang .Stmt) (σ : CEK) (n : CFGNode) :
      StmtCorr bts (buildStmt bts (nid + 2) s₁).nextId s₂ σ n →
      StmtCorr bts nid (.Seq s₁ s₂) σ n
  -- Do: inside the expression (exprStmtK on stack)
  | doInExpr (e : Lang .Expr) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) e ⟨C, E, J, K⟩ n →
      StmtCorr bts nid (.Do e) ⟨C, E, J, .exprStmtK :: K⟩ n
inductive ExprCorr :
    List CFGNode → Nat → Lang .Expr → CEK → CFGNode → Prop where
  -- At the entry of expression e
  | entry (e : Lang .Expr) (E J K) :
      ExprCorr bts nid e ⟨.sourceExpr e, E, J, K⟩ ⟨nid, .exprEntry e⟩
  -- At the exit of expression e (value produced)
  | exit (e : Lang .Expr) (v : Value) (E J K) :
      ExprCorr bts nid e ⟨.value v, E, J, K⟩ ⟨nid + 1, .exprExit e⟩
  -- BinOp: inside left operand (binopLK on stack)
  | binopInLeft (e₁ e₂ : Lang .Expr) (op : BinOp) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) e₁ ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.BinOp e₁ e₂ op) ⟨C, E, J, .binopLK op e₂ :: K⟩ n
  -- BinOp: inside right operand (binopRK on stack)
  | binopInRight (e₁ e₂ : Lang .Expr) (op : BinOp) (v₁ : Value) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (buildExpr bts (nid + 2) e₁).nextId e₂ ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.BinOp e₁ e₂ op) ⟨C, E, J, .binopRK op v₁ :: K⟩ n
  -- UnOp: inside the argument (unopK on stack)
  | unopInArg (arg : Lang .Expr) (op : UnOp) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) arg ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.UnOp arg op) ⟨C, E, J, .unopK op :: K⟩ n
  -- If: inside the condition (ifCondK on stack)
  | ifInCond (c e₁ e₂ : Lang .Expr) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) c ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.If c e₁ e₂) ⟨C, E, J, .ifCondK e₁ e₂ :: K⟩ n
  -- If: inside the true branch (transparent)
  | ifInTrue (c e₁ e₂ : Lang .Expr) (σ : CEK) (n : CFGNode) :
      ExprCorr bts (buildExpr bts (nid + 2) c).nextId e₁ σ n →
      ExprCorr bts nid (.If c e₁ e₂) σ n
  -- If: inside the false branch (transparent)
  | ifInFalse (c e₁ e₂ : Lang .Expr) (σ : CEK) (n : CFGNode) :
      ExprCorr bts
        (buildExpr bts (buildExpr bts (nid + 2) c).nextId e₁).nextId e₂ σ n →
      ExprCorr bts nid (.If c e₁ e₂) σ n
  -- While: inside the condition (loopK on stack)
  | whileInCond (c body : Lang .Expr) (envLen : Nat) (C : Control)
      (E : Environment) (J : JStackCtx) (K : List Cont) (n : CFGNode) :
      ExprCorr bts (nid + 2) c ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.While c body) ⟨C, E, J, .loopK c body envLen :: K⟩ n
  -- While: inside the body (loopContK on stack, jump context extended)
  | whileInBody (c body : Lang .Expr) (envLen : Nat)
      (C : Control) (E : Environment) (J : JStackCtx)
      (savedK : List Cont) (n : CFGNode) :
      ExprCorr (⟨nid + 1, .exprExit (.While c body)⟩ :: bts)
        (buildExpr bts (nid + 2) c).nextId body ⟨C, E, J, savedK⟩ n →
      ExprCorr bts nid (.While c body)
        ⟨C, E, ⟨envLen, savedK⟩ :: J, .loopContK c body envLen :: savedK⟩ n
  -- Scope: inside the statement part (scopeBodyK on stack)
  | scopeInStmt (s : Lang .Stmt) (res : Lang .Expr) (envLen : Nat)
      (C : Control) (E : Environment) (J : JStackCtx)
      (K : List Cont) (n : CFGNode) :
      StmtCorr bts (nid + 2) s ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.Scope s res) ⟨C, E, J, .scopeBodyK res envLen :: K⟩ n
  -- Scope: inside the result expression (scopeExitK on stack)
  | scopeInRes (s : Lang .Stmt) (res : Lang .Expr) (envLen : Nat)
      (C : Control) (E : Environment) (J : JStackCtx)
      (K : List Cont) (n : CFGNode) :
      ExprCorr bts (buildStmt bts (nid + 2) s).nextId res ⟨C, E, J, K⟩ n →
      ExprCorr bts nid (.Scope s res) ⟨C, E, J, .scopeExitK envLen :: K⟩ n
end
/-!
## The Top-Level Relation
For a program `s : Lang .Stmt`, the correspondence relation is obtained by
instantiating `StmtCorr` at the root (no break targets, starting ID 0):
-/
/-- The correspondence relation for program `s`, suitable for `TranslationReq`. -/
def corrRel (s : Lang .Stmt) : @StateRel (stmtCFG s) := fun σ n =>
  StmtCorr [] 0 s σ n.val

/-!
## Key Properties (Proof Sketches)
### `init_related`
`corrRel s (initState s) (stmtCFG s).entry` holds by `StmtCorr.entry`,
since `initState s = ⟨.sourceStmt s, [], [], []⟩` and
`(stmtCFG s).entry = ⟨0, .stmtEntry s⟩`.
### `terminal_related`
`corrRel s (terminalState E []) (stmtCFG s).exit` holds by `StmtCorr.exit`,
since `terminalState E [] = ⟨.skip, E, [], []⟩` and
`(stmtCFG s).exit = ⟨1, .stmtExit s⟩`.
### `init_uniq`
If `corrRel s (initState s) n`, then `n = (stmtCFG s).entry`.
This requires showing that the "transparent" constructors (`seqInRight`,
`ifInTrue`, `ifInFalse`) cannot produce the initial state for the
top-level program — which holds because the control in the initial state
is `.sourceStmt s`, and transparent recursion would require matching a
strict sub-term of `s`.
### `step_sound` / `step_complete`
These require case analysis on each `Eval` rule, showing that the
corresponding CFG edges exist (via `CFGStep`) or that the CFG node
doesn't change (zero-step reachability). The "transparent" constructors
handle the cases where a CEK step crosses an AST boundary without a
corresponding continuation frame change.
-/
instance {s : Lang .Stmt} : TranslationReq s (corrRel s) where
  init_related := by
    cases s <;>
      dsimp [corrRel] <;>
      simp only [stmtCFG, buildStmt, Nat.zero_add, List.cons_append, List.nil_append] <;>
      constructor
  terminal_related := by
    intro E
    cases s <;>
      dsimp [corrRel] <;>
      simp only [stmtCFG, buildStmt, Nat.zero_add, List.cons_append, List.nil_append] <;>
      constructor
  init_uniq := by
    intros n hn
    dsimp [corrRel] at hn
    sorry
  step_sound := by sorry
  step_complete := by sorry
end LeanFormalisation.AltCFGProofs
