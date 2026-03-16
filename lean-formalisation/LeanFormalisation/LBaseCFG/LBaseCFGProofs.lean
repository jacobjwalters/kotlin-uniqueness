import LeanFormalisation.LBase
import LeanFormalisation.LBaseCFG.LBaseCFGDefs
import ControlFlow.Graphs.FuncGraph
import ControlFlow.Graphs.Digraph
import ControlFlow.Graphs.CFG

open ControlFlow

/-
# CFGNodes in ControlFlow

the goal is to produce a value of type `CFG CFGNode FuncGraphType`. Three things
are required:

## 1. `DecidableEq CFGNode`
provided as a noncomputable instance in `LBaseCFG.lean`.

## 2. finite `FuncGraphType CFGNode` whose bfs match `CFGNode.succs`
to build a graph for a specific program we BFS from `cfgInit s`, applying
`CFGNode.succs` at each new node.

there is a finite amount of reachable `CFGNode`s from a fixed program `s`, and
every node is a finite object -> the reachable state space is finite.
need to establish a bound though.

## 3. a proof that every vertex is reachable from `start`
the bfs invariant guarantees that every vertex added to the graph was discovered
as a successor of some already reached vertex. proven by induction on the
traversal order.
-/

-- ideally i would want this definition to be further down but it has to be
-- somewhere that isn't after a theorem for reasons that are to me incomprehensible
mutual
  def exprSize : Lang .Expr → Nat
    | .True | .False | .Unit | .Break | .Var _ | .Nat _ => 1
    | .BinOp e₁ e₂ _  => 1 + exprSize e₁ + exprSize e₂
    | .UnOp e _        => 1 + exprSize e
    | .If c e₁ e₂     => 1 + exprSize c + exprSize e₁ + exprSize e₂
    | .While c b       => 1 + exprSize c + exprSize b
    | .Scope s e       => 1 + stmtSize s + exprSize e

  def stmtSize : Lang .Stmt → Nat
    | .Decl _ e   => 1 + exprSize e
    | .Assign _ e => 1 + exprSize e
    | .Seq s₁ s₂  => 1 + stmtSize s₁ + stmtSize s₂
    | .Do e       => 1 + exprSize e
end

set_option linter.unusedVariables false in
/-- collect all `CFGNode`s reachable from `root` -/
def reachableNodes (root : CFGNode) : Nat → List CFGNode
  | 0          => [root]
  | fuel + 1   =>
    let rec go : Nat → List CFGNode → List CFGNode → List CFGNode
      | 0,       _,             visited => visited
      | _ + 1,   [],            visited => visited
      | k + 1,   w :: worklist, visited =>
          if h : w ∈ visited then go k worklist visited
          else go k (worklist ++ w.succs) (w :: visited)
    go (fuel + 1) [root] []

/-- for every node `n` visited during BFS from `root`, add one directed edge
    `(n, m)` per `m ∈ n.succs`.
    the start node is also inserted as an isolated vertex -/
def buildFuncGraph (root : CFGNode) (fuel : Nat)
    : Digraph.FuncGraphType CFGNode :=
  let nodes := reachableNodes root fuel
  let g₀ : Digraph.FuncGraphType CFGNode :=
    Digraph.FuncGraphType.empty.add_vertex root
  nodes.foldl
    (fun g n => n.succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g)
    g₀

/-- any vertex `v` already in `g` remains in `g` after adding a new edge -/
private theorem succs_foldl_pres_vertex
    (succs : List CFGNode) (n : CFGNode)
    {g : Digraph.FuncGraphType CFGNode} {v : CFGNode}
    (hv : g.vertices v = true) :
    (succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g).vertices v = true := by
  induction succs generalizing g with
  | nil => exact hv
  | cons m rest ih =>
    apply ih
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right; assumption

/-- equivalent of succs_foldl_pres_vertex, generalized over a list of nodes. -/
private theorem outer_foldl_pres_vertex
    (nodes : List CFGNode)
    {g : Digraph.FuncGraphType CFGNode} {v : CFGNode}
    (hv : g.vertices v = true) :
    (nodes.foldl
      (fun g n => n.succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g) g
    ).vertices v = true := by
  induction nodes generalizing g with
  | nil  => exact hv
  | cons n rest ih => exact ih (succs_foldl_pres_vertex n.succs n hv)

/-- `root` is a vertex in the graph built from it. -/
theorem root_in_buildFuncGraph (root : CFGNode) (fuel : Nat) :
    (buildFuncGraph root fuel).vertices root = true := by
  simp only [buildFuncGraph]
  apply outer_foldl_pres_vertex
  simp

/-- for every graph `g`, edges `e`, `ne`,
    `ne` ∈ `(g.add_edge e)` iff `ne` = `e` or `e` ∈ `g` -/
private theorem add_edge_edges_iff
    {g : Digraph.FuncGraphType CFGNode} {newEdge e : Edge CFGNode} :
    (g.add_edge newEdge).edges e = true ↔ newEdge = e ∨ g.edges e = true := by
  simp [Bool.or_eq_true, decide_eq_true_eq]

/-- after folding `succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g`, any edge in
    the result was either already in `g`, or is `⟨n, m⟩` for some `m ∈ succs`. -/
private theorem inner_foldl_edges_or
    (succs : List CFGNode) (n : CFGNode)
    {g : Digraph.FuncGraphType CFGNode} {e : Edge CFGNode}
    (h : (succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g).edges e = true) :
    g.edges e = true ∨ (e.start = n ∧ e.finish ∈ succs) := by
  induction succs generalizing g with
  | nil => left; simpa using h
  | cons m rest ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with h' | ⟨hstart, hfin⟩
    · -- h' : (g.add_edge ⟨n, m⟩).edges e = true
      rw [add_edge_edges_iff] at h'
      rcases h' with h_eq | h'
      · right; simp [<- h_eq]
      · left; exact h'
    · right; exact ⟨hstart, List.mem_cons_of_mem m hfin⟩

/-- folding an edge over a succesor list preserves existing edges. -/
private theorem succs_foldl_pres_edge
    (succs : List CFGNode) (n : CFGNode)
    {g : Digraph.FuncGraphType CFGNode} {e : Edge CFGNode}
    (he : g.edges e = true) :
    (succs.foldl (fun g' m => g'.add_edge ⟨n, m⟩) g).edges e = true := by
  induction succs generalizing g with
  | nil => exact he
  | cons m rest ih =>
    apply ih
    exact add_edge_edges_iff.mpr (Or.inr he)

/-- `m in n.succs` -> ⟨n, m⟩ ∈ (graph fold on n) -/
private theorem inner_foldl_edges_complete
    (succs : List CFGNode) (n m : CFGNode) (g : Digraph.FuncGraphType CFGNode)
    (hm : m ∈ succs) :
    (succs.foldl (fun g' x => g'.add_edge ⟨n, x⟩) g).edges ⟨n, m⟩ = true := by
  induction succs generalizing g with
  | nil => exfalso; exact (List.mem_nil_iff m).mp hm
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · refine succs_foldl_pres_edge rest n ?_
      simp
    · exact ih _ hm'

/-- folding `g` over `nodes`, any edge was either in the initial `g`, or
    it is ⟨n, m⟩ for `n ∈ nodes`, `m ∈ n.succ` -/
private theorem outer_foldl_edges_or
    (nodes : List CFGNode) (g : Digraph.FuncGraphType CFGNode) {e : Edge CFGNode}
    (h : (nodes.foldl
          (fun g' n => n.succs.foldl (fun g'' m => g''.add_edge ⟨n, m⟩) g') g).edges
         e = true) :
    g.edges e = true ∨ ∃ n ∈ nodes, e.start = n ∧ e.finish ∈ n.succs := by
  induction nodes generalizing g with
  | nil => exact Or.inl h
  | cons n rest ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨w, hw_mem, hstart, hfin⟩
    · rcases inner_foldl_edges_or n.succs n h' with h'' | ⟨hs, hf⟩
      · left; exact h''
      · right
        exists n
        exact ⟨List.mem_cons_self, hs, hf⟩
    · right
      exists w
      exact ⟨List.mem_cons_of_mem n hw_mem, hstart, hfin⟩

/-- every edge in `buildFuncGraph root fuel` corresponds to a `CFGNode.succs`. -/
theorem buildFuncGraph_edges_sound (root : CFGNode) (fuel : Nat)
    (e : Edge CFGNode)
    (h : (buildFuncGraph root fuel).edges e = true) :
    e.finish ∈ e.start.succs := by
  simp only [buildFuncGraph] at h
  have := outer_foldl_edges_or (reachableNodes root fuel) _ h
  rcases this with h' | ⟨n, _, hstart, hfin⟩
  · simp at h'
  · rwa [hstart]

-- Existing edges are preserved through the outer foldl over more nodes.
/-- outer fold preserves existing edges -/
private theorem outer_foldl_pres_edge
    (nodes : List CFGNode)
    {g : Digraph.FuncGraphType CFGNode} {e : Edge CFGNode}
    (he : g.edges e = true) :
    (nodes.foldl
      (fun g' n => n.succs.foldl (fun g'' m => g''.add_edge ⟨n, m⟩) g') g).edges e = true := by
  induction nodes generalizing g with
  | nil  => exact he
  | cons n rest ih => exact ih (succs_foldl_pres_edge n.succs n he)

/-- MAIN: every successor of a BFS-visited node is an edge in the graph. -/
theorem buildFuncGraph_edges_complete (root : CFGNode) (fuel : Nat)
    (n : CFGNode) (hn : n ∈ reachableNodes root fuel)
    (m : CFGNode) (hm : m ∈ n.succs) :
    (buildFuncGraph root fuel).edges ⟨n, m⟩ = true := by
  simp only [buildFuncGraph]
  obtain ⟨pre, suff, hrfl⟩ := List.mem_iff_append.mp hn
  rw [hrfl, List.foldl_append, List.foldl_cons]
  apply outer_foldl_pres_edge
  exact inner_foldl_edges_complete n.succs n m _ hm

-- fuel bounds
def cfgFuel (s : Lang .Stmt) : Nat :=
  let n := stmtSize s + 2  -- +2 for .value and .skip
  n * n

-- reachability
def programGraph (s : Lang .Stmt) : Digraph.FuncGraphType CFGNode :=
  buildFuncGraph (cfgInit s) (cfgFuel s)

/-- initial node as a subtype (vertex of `programGraph s`).
    the membership proof is given by `root_in_buildFuncGraph`. -/
def startVertex (s : Lang .Stmt) :
    { v : CFGNode // (programGraph s).vertices v = true } :=
  ⟨cfgInit s, root_in_buildFuncGraph (cfgInit s) (cfgFuel s)⟩

/-- TODO: what's left:
    - [ ] sderive full reachability
-/
theorem all_vertices_reachable (s : Lang .Stmt) :
    ∀ (v : CFGNode) (hv : (programGraph s).vertices v = true),
      Path.Reachable (programGraph s) (startVertex s) ⟨v, hv⟩ := by
  sorry

/-- CFG built from `s`.
    remains to prove: `cfgFuel` and `all_vertices_reachable`. -/
def programCFG (s : Lang .Stmt) : CFG CFGNode Digraph.FuncGraphType :=
  { digraph   := programGraph s
  , start     := startVertex s
  , reachable := fun v => all_vertices_reachable s v.val v.property
  }
