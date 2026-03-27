# Abstract CFG → Concrete CFG: TODO list

Branch: `wip/abstract-cfg` (off `quartztz/abscorr`)

## Approach

Patch `ContCFGInv` (add `step` constructor + kind fields) to close
the 22 sorries in `step_sound`.  The bridge approach (routing through
`abs_sim`) is blocked by an `AbsContInv` chaining gap — see report.

Report: `/srv/www-devbot/kotlin/formalization/misc/abstract-cfg-design/`

---

## Phase 1: Patch ContCFGInv

- [ ] **1a.** Add `step` constructor to `ContCFGInv`:
  ```
  | step (y : CFGNode) :
      CFGStep g x y → ContCFGInv g K y → ContCFGInv g K x
  ```

- [ ] **1b.** Add kind fields to simple constructors:
  `binopRK`, `unopK`, `declK`, `assignK`, `exprStmtK`, `scopeExitK`.

- [ ] **1c.** Update all construction sites that build these
  constructors (in `cfgcekRelReq` and the `exprEntry`/`stmtEntry`
  case bodies) to provide the new fields.

- [ ] **1d.** Verify the file compiles (modulo remaining sorries).

## Phase 2: Close step_sound sorries

- [ ] **2a.** Close 14 anchor-mismatch sorries using `ContCFGInv.step`:
  IfTrue, IfFalse, SeqDone, ScopeBody, LoopTrue (×5), LoopCont (×3).

- [ ] **2b.** Close 8 missing-kind sorries using the new kind fields:
  VarDeclDone, AssignDone, BinOpL, BinOpR, UnOpDone, LoopFalse,
  ScopeExit, ExprStmtDone.

- [ ] **2c.** Fill in the `stmtEntry` case (~line 1742) by case
  analysis on `StmtEntryEdgeInv`, analogous to `exprEntry`.

- [ ] **2d.** Handle `brkOOB` (~line 1618): prove unreachable via
  `JCFGInv.length_eq` or add well-typedness precondition.

## Phase 3: Bridge lemma (independent)

- [ ] **3a.** Prove `absStep_implies_cfgEdge` in Bridge.lean.
  Independently valuable for multi-step reachability and analysis
  connection.

## Phase 4: edge_complete

- [ ] **4a.** Prove `edge_complete` (reverse direction).

## Future: abs_sim chaining fix

- [ ] **F1.** Add weakening constructors to `AbsContInv`
  (ifBranchK, seqMidK, scopeMidK, whileBackK).
- [ ] **F2.** Update `abs_sim` to output `AbsContInv K (ac₂.target)`.
- [ ] **F3.** Refactor `cfgcekRel` to use `AbsContInv`, route
  `step_sound` through bridge.  Deletes ContCFGInv/JCFGInv/EntryEdgeInv.
