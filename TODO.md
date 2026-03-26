# Correspondence proof TODO

Tracking remaining work on the CEK-to-CFG correspondence (`CorrespondenceProofs.lean`).

## ContCFGInv redesign

The current `ContCFGInv` definition (line ~1333 of `CorrespondenceProofs.lean`) has two
gaps that block `step_sound`. Detailed writeup with rendered tables at
https://devbot.jesyspa.dev/kotlin/formalization/misc/contcfginv-mismatch/

### Problem 1: anchor-node shift

`ContCFGInv g K x` says continuation stack K describes the CFG path from node x to
g.exit. When the CEK pops a frame (e.g. IfTrue drops `ifCondK`), the sub-expression's
CFG exit node is one edge *before* the anchor stored in the popped frame. Concretely:

- `ifCondK` stores `ContCFGInv g K pex` (parent exit) and `CFGStep g e1ex pex`.
- After IfTrue, we need `ContCFGInv g K e1ex`, but there's no way to shift the anchor
  back across that edge.
- Same pattern in: SeqDone, LoopTrue, LoopFalse, LoopCont, ScopeBody, ScopeExit.

Fix: add a `step` constructor to `ContCFGInv`:
```lean
| step (y : CFGNode) :
    CFGStep g x y ->
    ContCFGInv g K y ->
    ContCFGInv g K x
```
This lets you absorb one CFG edge to shift the anchor. Downside: makes `ContCFGInv`
partly a reachability relation, adding a case to any induction on it (notably
`edge_complete`).

### Problem 2: missing node-kind information

`cfgcekRel.exprExit` needs `n.kind = .exprExit e`. Several `ContCFGInv` constructors
(`binopRK`, `unopK`, `declK`, `assignK`, `exprStmtK`, `scopeExitK`) store
`CFGStep g x pex` but NOT `pex.kind`. When the CEK finishes and steps to pex, the
proof can't produce the kind fact.

Fix: add a kind field to each of these constructors, e.g.:
```lean
| binopRK (op : BinOp) (v1 : Value) (parent : Lang .Expr) (pex : CFGNode) :
    pex.kind = .exprExit parent ->  -- new
    CFGStep g x pex ->
    ContCFGInv g K pex ->
    ContCFGInv g (.binopRK op v1 :: K) x
```
The `buildExpr_exit_kind` / `buildStmt_exit_kind` theorems provide these facts at
construction time.

### Sorry classification

All ~18 sorries in `step_sound` (lines ~1640-1770) fall into these categories:

| Case                      | Anchor shift | Missing kind |
|---------------------------|--------------|--------------|
| IfTrue / IfFalse          | yes          | no           |
| VarDeclDone / AssignDone  | no           | yes          |
| BinOpL                    | no           | yes          |
| BinOpR / UnOpDone         | no           | yes          |
| LoopTrue                  | yes          | yes          |
| LoopFalse                 | no           | yes          |
| LoopCont                  | yes          | yes          |
| ScopeExit / ExprStmtDone  | no           | yes          |
| SeqDone / ScopeBody       | yes          | yes          |

### Steps

- [ ] Add `step` constructor to `ContCFGInv`
- [ ] Add `pex.kind` fields to `binopRK`, `unopK`, `declK`, `assignK`,
      `exprStmtK`, `scopeExitK` constructors
- [ ] Update all construction sites that build `ContCFGInv` values (in
      `step_sound` and `cfgcekRelReq`) to supply the new fields
- [ ] Close the ~18 sorries in `step_sound`

## stmtEntry case in step_sound

- [ ] Case-split on the statement form in the `stmtEntry` branch of
      `step_sound` (line ~1743), analogous to the existing `exprEntry` handler.
      Each statement form (Decl, Assign, Seq, Do) should destructure its
      `StmtEntryEdgeInv` and produce the appropriate `cfgcekRel` for the
      first child's entry node.

## edge_complete

- [ ] Formulate a proof strategy for `edge_complete` (line ~1768).
      This is the completeness direction: every CFG edge corresponds to a
      CEK evaluation path. Currently a single sorry. Likely requires
      induction on the edge membership proof, case-splitting on edge kind
      (normal, trueBranch, falseBranch, back, breakOut).
- [ ] Implement it

## LBase.lean

- [ ] Finish `progress_stuck` (line 599) -- incomplete induction on the
      well-typed state. Need to show either terminal or can step.

## basic/LBaseCFGProofs.lean

- [ ] `all_vertices_reachable` (line 238) -- prove all CFG nodes are
      reachable from the start vertex via edges

## Cleanup

- [x] Remove stray `#eval` in `LBaseCFGDefs.lean`
