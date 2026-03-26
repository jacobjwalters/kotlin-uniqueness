# CorrespondenceProofs: Design, Obstacles & Proof Techniques

## Overview

`CorrespondenceProofs.lean` proves the correctness of the CFG translation defined in `AltCFG.lean` by establishing a bisimulation-style correspondence between the CEK abstract machine semantics and the control-flow graph representation of LBase programs.

The high-level goal is to instantiate `TranslationReq s R` (defined in `Correspondence.lean`) for a concrete relation `R = cfgcekRel s`, which requires four obligations:

| Obligation | Status |
|---|---|
| `init_related` — initial CEK state relates to CFG entry | ✅ Proved |
| `terminal_related` — terminal CEK state relates to CFG exit | ✅ Proved |
| `step_sound` — every CEK step has a matching CFG edge | 🔶 Partial (~25 `sorry`s) |
| `edge_complete` — every CFG edge has a matching CEK step | ❌ Not started |

Once `TranslationReq` is fully instantiated, `translation_sound_reachability` (already proved generically) lifts one-step soundness to whole-path correspondence via reflexive-transitive induction.

## Architecture & Design Choices

### 1. CEK-to-CFG Relation (`cfgcekRel`)

The relation `cfgcekRel s : StateRel` (line 1435) has four constructors matching the four kinds of CFG nodes:

- **`exprEntry`** — CEK control is `.sourceExpr e`, node kind is `.exprEntry e`. Stores an `ExprEntryEdgeInv` witness and a `ContCFGInv` anchored at the corresponding exit node.
- **`exprExit`** — CEK control is `.value v`, node kind is `.exprExit e`. Stores `ContCFGInv` at the current node.
- **`stmtEntry`** — CEK control is `.sourceStmt st`, node kind is `.stmtEntry st`. Stores `StmtEntryEdgeInv` and `ContCFGInv` at the exit node.
- **`stmtExit`** — CEK control is `.skip`, node kind is `.stmtExit st`. Stores `ContCFGInv` at the current node.

**Key design decision:** `ExprEntryEdgeInv`/`StmtEntryEdgeInv` are stored directly in the `cfgcekRel` entry constructors (not only in `ContCFGInv`). This is necessary so that entry-node cases of `step_sound` can case-split on the edge invariant to obtain the `CFGStep` witness for the successor node.

### 2. Edge Invariants (`ExprEntryEdgeInv` / `StmtEntryEdgeInv`)

These mutually inductive predicates (lines 840–979) describe the CFG edge structure reachable from an entry node. Each constructor mirrors a `Lang` AST constructor and records:

- `CFGStep` witnesses for all edges the builder emits,
- Node kind equalities for all intermediate nodes,
- Node membership in `g.nodes`,
- Recursive `ExprEntryEdgeInv`/`StmtEntryEdgeInv` for sub-expressions/sub-statements.

This is the central proof-carrying data structure: it encodes that the builder produced exactly the expected edges.

### 3. Continuation-CFG Invariant (`ContCFGInv`)

`ContCFGInv g K x` (line 1262) relates the CEK continuation stack `K` to CFG edges leading from node `x` back to `g.exit`. Each constructor corresponds to a `Cont` frame and stores:

- The `CFGStep` from the current node to the next relevant node,
- For frames that transition to entry nodes (e.g., `binopLK`, `ifCondK`, `seqK`, `loopK`, `scopeBodyK`): the child's `ExprEntryEdgeInv` or `StmtEntryEdgeInv`, so the successor state can be constructed without a global lookup.
- A recursive `ContCFGInv` for the tail of the stack.

### 4. Jump-Context Invariant (`JCFGInv`)

`JCFGInv g J breakTargets` (line 1382) relates the CEK jump context (for `break` statements) to the list of break-target CFG nodes threaded through the builder. Each entry's saved continuation is valid (via `ContCFGInv`) at the corresponding while-exit node.

### 5. Structural CFG Obligations (Fully Proved)

The first ~690 lines prove structural properties of the CFG builder output, all fully complete:

- **`stmtCFG_entry_exit_in_nodes`** — entry and exit are in the node set.
- **`stmtCFG_true_false_edges_from_exprExit`** — branch edges originate at `exprExit` nodes.
- **`stmtCFG_back_edges_are_loop_back`** — back edges go from body exit to condition entry.
- **`stmtCFG_break_edges_target_loop_exit`** — break edges target `exprExit` nodes.
- **`buildExpr/buildStmt_entry/exit_kind`** — entry/exit node kinds match the AST.
- **Builder edge lemmas** (lines 692–835) — each AST constructor's edges are present.

These are proved via mutual induction over `buildExpr`/`buildStmt`, with a `BreakTargetsWellFormed` predicate threading well-formedness of break targets through the recursion.

## Recent Progress: `entry_edge_inv` Theorems

### Closed Cases

The mutual theorems `buildExpr_entry_edge_inv` / `buildStmt_entry_edge_inv` are now **nearly complete**. The following cases were closed in this session:

#### Expr cases (all in `buildExpr_entry_edge_inv`):

| Case | Status | Technique |
|---|---|---|
| `Var`, `True`, `False`, `Nat`, `Unit` | ✅ Already done | `constructor; exists e; split_ands` |
| **`BinOp`** | ✅ **Closed** | Node kind goals solved by `exact buildExpr_entry_kind ..` / `buildExpr_exit_kind ..` |
| **`UnOp`** | ✅ **Closed** | Same technique as BinOp |
| **`If`** | ✅ **Closed** | Full proof with 5 `CFGStep` witnesses, 3 recursive `mono` calls, 6 kind goals. Required `exact ⟨edge, by simp [..., buildExpr], by simp [mkEdge], by simp [mkEdge]⟩` pattern for deeply nested edges where `grind` timed out. |
| **`While`** | ✅ **Closed** | Required fixing the `.whil` constructor (see below). Back edge also needed the `exact ⟨...⟩` pattern. |
| **`Scope`** | ✅ **Closed** | Straightforward application of `.scope` with `buildStmt_entry_kind`/`buildStmt_exit_kind`/`buildExpr_entry_kind`/`buildExpr_exit_kind`. |
| `Break` | ❌ Still `sorry` | Needs `BreakTargetsWellFormed` precondition (see below) |

#### Stmt cases (all in `buildStmt_entry_edge_inv`):

| Case | Status | Technique |
|---|---|---|
| **`Decl`** | ✅ **Closed** | Kind goals: `exact buildExpr_entry_kind ..` / `buildExpr_exit_kind ..` |
| **`Assign`** | ✅ **Closed** | Same as Decl |
| **`Seq`** | ✅ **Closed** | Kind goals: `exact buildStmt_entry_kind ..` / `buildStmt_exit_kind ..` |
| **`Do`** | ✅ **Closed** | Kind goals: `exact buildExpr_entry_kind ..` / `buildExpr_exit_kind ..` |

### Key Proof Patterns Discovered

1. **Node kind goals** — After `refine .constructor ...`, remaining goals of the form `r₁.entry.kind = .exprEntry a₁` are solved by `exact buildExpr_entry_kind ..` (or the exit/stmt variants). The `..` syntax lets Lean infer the arguments.

2. **Deeply nested `CFGStep` witnesses** — For cases with 3+ sub-results (If, While back edge), `grind [buildExpr, mkEdge]` times out because the terms become too deeply nested after `set` unfolding. The working pattern is:
   ```lean
   exact ⟨mkEdge src dst edgeKind,
     by simp [g, r, rc, rt, rf, buildExpr],
     by simp [mkEdge], by simp [mkEdge]⟩
   ```
   This works because `simp` with the `set` aliases unfolds to the concrete edge list and finds membership, while `simp [mkEdge]` solves the `.src`/`.dst` equalities.

3. **Monotonicity lifting** — Every recursive call uses `.mono (g₂ := g) (by grind [buildExpr])` to lift the sub-graph invariant to the parent graph.

### Constructor Fix: `.whil` breakTargets for `cond`

**Problem:** The original `.whil` constructor specified `ExprEntryEdgeInv g breakTargets cond cen cex` (using the outer `breakTargets`), but `buildExpr` for `While` passes `exit :: breakTargets` to **both** `cond` and `body`. This caused a mismatch: `hec` had type `ExprEntryEdgeInv g (r.exit :: breakTargets) cond ...` but the constructor expected `ExprEntryEdgeInv g breakTargets cond ...`.

**Fix applied:** Changed line 919 from:
```lean
ExprEntryEdgeInv g breakTargets cond cen cex ->
```
to:
```lean
ExprEntryEdgeInv g (ex :: breakTargets) cond cen cex ->
```

**Downstream impact:** This caused one error at line 1607 in the `exprEntry`/`While` case of `step_sound`, where the proof previously matched `hjinv : JCFGInv ... J bts` against the constructor's `breakTargets` parameter. Now the constructor expects `ex :: bts`, so the proof needs `JCFGInv ... J (ex :: bts)`. This requires either:
- A `JCFGInv.cons`-like lemma to extend the jump context, or
- Restructuring the While entry case of `step_sound` to thread the extended break targets.

This is semantically correct: inside a while loop, both the condition and body can see the break target (the while's exit node). The `JCFGInv` at that point should already include the while's break target since we're entering the while's condition from the while's entry node, which means the CEK machine has already pushed the loop frame.

## Remaining Obstacles

### Obstacle 1: `Break` Case in `buildExpr_entry_edge_inv`

The `Break l` case (line 1209) remains `sorry`. The `.brk` constructor requires:
- `l < breakTargets.length` — not provable without a precondition
- `target = breakTargets[l]` — straightforward once length is known
- `∃ loopExpr, target.kind = .exprExit loopExpr` — needs `BreakTargetsWellFormed`
- `target ∈ g.nodes` — needs the target to be in the graph

**Fix:** Add a `BreakTargetsWellFormed` precondition to `buildExpr_entry_edge_inv`, or handle the out-of-bounds case separately (the builder emits no edges when `l ≥ breakTargets.length`, so `ExprEntryEdgeInv` may need a `brkOOB` constructor for that case).

### Obstacle 2: `step_sound` Exit Cases — `ContCFGInv` Mismatch

In the `exprExit` case of `step_sound` (lines 1560–1668), after case-splitting on `hContInv`, the remaining `sorry`s fall into:

#### (a) Node kind facts (~15 `sorry`s)

Goals like `⊢ n'.kind = .exprExit parent_expr` where `n'` is a node obtained from `ContCFGInv`. These should follow from the hypotheses already in `ContCFGInv` constructors but require explicit extraction. **Fix:** add helper lemmas or use `assumption` after appropriate rewrites.

#### (b) `IfTrue`/`IfFalse` continuation mismatch (lines 1562–1582)

The `ifCondK` constructor stores `ContCFGInv g K pex` where `pex` is the *parent* exit node. But after branching, the new state needs `ContCFGInv g K' e₁ex` (anchored at the *branch* exit). The branch exit → parent exit edge exists in `ifCondK`, but there's no mechanism to "prepend" it to the tail continuation.

**Potential fix:** Either:
1. Add a dedicated `ifBranchK` continuation frame that wraps the branch-exit → parent-exit edge, or
2. Store the branch-exit → parent-exit `CFGStep` in a new `ContCFGInv` constructor (analogous to `scopeExitK`).

#### (c) `LoopTrue` case (lines 1618–1631)

Needs to:
1. Build `cfgcekRel.exprEntry` for the loop body using `EntryEdgeInv` from `loopK`,
2. Extend `JCFGInv` with the new loop level,
3. Build `ContCFGInv.loopContK` for the body exit → condition re-entry.

Multiple `sorry`s here relate to threading the extended break targets and jump context correctly.

### Obstacle 3: `stmtEntry` Case of `step_sound` (line ~1747)

Entirely `sorry`. With `StmtEntryEdgeInv` stored in the relation, this should be mechanical: case-split on `heval`, then case-split on the `StmtEntryEdgeInv` to get the `CFGStep` and build the successor. The pattern mirrors the `exprEntry` case.

### Obstacle 4: `edge_complete` (line ~1772)

Entirely `sorry`. This is the hardest obligation: for every CFG edge, exhibit a reachable CEK state that traverses it. Likely requires:
- An inversion principle on `CFGStep` to determine which builder case produced the edge,
- A reachability argument showing the CEK machine can reach the corresponding state,
- Possibly a separate inductive characterization of reachable CEK states.

## Proof Techniques & Required Lemmas

### Technique 1: Monotonicity Lifting

Already implemented (`ExprEntryEdgeInv.mono`, `StmtEntryEdgeInv.mono`, `CFGStep_mono`, `CFG_subgraph_step`). Used to lift child sub-graph results to the parent graph when the parent's edge list is a superset. Critical for all recursive cases of `buildExpr/buildStmt_entry_edge_inv`.

### Technique 2: Mutual Structural Induction

The `buildExpr`/`buildStmt` functions are mutually recursive, so all proofs about them require mutual induction. The pattern is established: prove a `private` mutual pair, then expose public wrappers. The `fun_induction` tactic (used for `eraseDupsBy`) and manual `cases` + `rcases` on edge membership are the main proof methods.

### Technique 3: `grind` for Edge Membership

Many `CFGStep` witnesses are constructed by `exists mkEdge ..; grind [buildExpr, mkEdge]`, which unfolds the builder and solves the edge-membership + field-equality goals. This works well for the top-level edges but **fails for deeply nested sub-expressions** (3+ sub-results). For those, use the `exact ⟨edge, by simp [...], by simp [mkEdge], by simp [mkEdge]⟩` pattern instead.

### Required Lemmas (Not Yet Proved)

1. **`Break` case completion** — Either add `BreakTargetsWellFormed` precondition to `buildExpr_entry_edge_inv`, or add a `brkOOB` constructor to `ExprEntryEdgeInv` for the out-of-bounds case.

2. **Node kind extraction helpers** — Small lemmas that extract `.kind` equalities from `ContCFGInv` constructors, e.g.:
   ```lean
   theorem ContCFGInv.declK_exit_kind (h : ContCFGInv g (.declK ty :: K) x) :
       ∃ sex, sex.kind = .stmtExit ... ∧ CFGStep g x sex
   ```

3. **`IfBranch` continuation constructor** — A new `ContCFGInv` constructor (or wrapper) for the if-branch-exit → parent-exit edge:
   ```lean
   | ifBranchK (pex : CFGNode) :
       CFGStep g x pex → ContCFGInv g K pex →
       ContCFGInv g K x  -- or a new frame type
   ```

4. **`JCFGInv` extension lemma** — For `While` entry, extending the jump context:
   ```lean
   theorem JCFGInv.cons (h : JCFGInv g J bts) (hcont : ContCFGInv g K whileExit)
       (hkind : ∃ le, whileExit.kind = .exprExit le) :
       JCFGInv g (⟨n, K⟩ :: J) (whileExit :: bts)
   ```

5. **Edge inversion for `edge_complete`** — A characterization of which builder case produced a given edge:
   ```lean
   theorem stmtCFG_edge_cases (s : Lang .Stmt) (e : CFGEdge) (he : e ∈ (stmtCFG s).edges) :
       <disjunction of all possible edge origins>
   ```

## File Organization

| Lines | Section | Status |
|---|---|---|
| 1–11 | Module docstring | — |
| 22–688 | Structural CFG obligations | ✅ Complete |
| 692–835 | Builder edge lemmas | ✅ Complete |
| 840–979 | `ExprEntryEdgeInv` / `StmtEntryEdgeInv` definitions | ✅ Complete (`.whil` constructor updated) |
| 981–1070 | Monotonicity (`mono`) lemmas | ✅ Complete |
| 1072–1327 | `buildExpr/buildStmt_entry_edge_inv` | ✅ Nearly complete (1 `sorry`: `Break`) |
| 1329–1470 | `ContCFGInv`, `JCFGInv` definitions + helpers | ✅ Complete |
| 1490–1525 | `cfgcekRel` definition | ✅ Complete |
| 1527–1778 | `cfgcekRelReq` (`TranslationReq` instance) | 🔶 ~25 `sorry`s |
