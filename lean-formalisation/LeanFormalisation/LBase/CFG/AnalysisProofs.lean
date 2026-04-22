import LeanFormalisation.LBase.CFG.AltCFG
import LeanFormalisation.LBase.CFG.Analysis

open LeanFormalisation.AltCFG

-- ============================================================
-- Helpers
-- ============================================================

private lemma ite_decEq_irrel {α : Type} {p : Prop}
    (d1 d2 : Decidable p) (a b : α) :
    @ite α p d1 a b = @ite α p d2 a b := by
  cases d1 <;> cases d2 <;> simp_all

private lemma newIn_eq_expectedIn
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (n : NodeOf g)
    (newIn : A)
    (hdef : Eq newIn (if _ : n.val = g.entry then entryInit
        else joinPredEdgesOf g edgeTransfer outF n)) :
    Eq newIn (expectedInOf g edgeTransfer entryInit outF n) := by
  rw [hdef]; simp only [expectedInOf]; exact ite_decEq_irrel _ _ _ _

private lemma foldl_join_eT_update
    {A : Type} [Bot A] [Max A]
    (g : CFG)
    (edgeTransfer : CFGEdge -> A -> A) (outF : GFact g A)
    (n : NodeOf g) (v : A) (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (hnoedge : ∀ e ∈ edges, e.val.src ≠ n.val) (init : A) :
    Eq (edges.foldl (fun acc ⟨e, he⟩ =>
        acc ⊔ edgeTransfer e ((outF.update n v) ⟨e.src, g.inEdges_src_mem m.val e he⟩)) init)
       (edges.foldl (fun acc ⟨e, he⟩ =>
        acc ⊔ edgeTransfer e (outF ⟨e.src, g.inEdges_src_mem m.val e he⟩)) init) := by
  induction edges generalizing init with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    have he_src : e.val.src ≠ n.val := hnoedge e (List.Mem.head _)
    have : ⟨e.val.src, g.inEdges_src_mem m.val e.val e.property⟩ ≠ n := by
      intro h
      have hval : e.val.src = n.val := congrArg Subtype.val h
      exact he_src hval
    simp only [GFact.update, this, if_false]
    exact ih (fun e' he' => hnoedge e' (List.mem_cons_of_mem e he')) _

private lemma joinPredEdges_update_non_pred
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A) (outF : GFact g A)
    (n : NodeOf g) (v : A) (m : NodeOf g)
    (hnoedge : ∀ e ∈ g.inEdges m.val, e.src ≠ n.val) :
    Eq (joinPredEdgesOf g edgeTransfer (outF.update n v) m)
       (joinPredEdgesOf g edgeTransfer outF m) := by
  unfold joinPredEdgesOf
  exact foldl_join_eT_update g edgeTransfer outF n v m (g.inEdges m.val).attach
    (fun e _ => hnoedge e.val e.property) ⊥

private lemma not_succ_no_in_edge
    (g : CFG) (n m : NodeOf g) (h : m.val ∉ g.succ n.val) :
    ∀ e ∈ g.inEdges m.val, e.src ≠ n.val := by
  intro e he hsrc
  apply h
  simp only [CFG.succ, CFG.inEdges] at he ⊢
  obtain ⟨he_in, he_prop⟩ := List.mem_filter.mp he
  have he_dst : e.dst = m.val := of_decide_eq_true he_prop
  exact mem_of_mem_eraseDups
    (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he_in, decide_eq_true hsrc⟩, he_dst⟩)

private lemma expectedIn_update_non_pred
    {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A) (outF : GFact g A)
    (entryInit : A) (n : NodeOf g) (v : A) (m : NodeOf g) (h : m.val ∉ g.succ n.val) :
    Eq (expectedInOf g edgeTransfer entryInit (outF.update n v) m)
       (expectedInOf g edgeTransfer entryInit outF m) := by
  simp only [expectedInOf]
  split
  · rfl
  · exact joinPredEdges_update_non_pred g edgeTransfer outF n v m
      (not_succ_no_in_edge g n m h)

private lemma mem_succOf_iff_mem_succ (g : CFG) (n m : NodeOf g) :
    m ∈ g.succOf n ↔ m.val ∈ g.succ n.val := by
  unfold CFG.succOf
  simp only [List.mem_pmap]
  constructor
  · intro ⟨a, ⟨ha, heq⟩⟩
    subst heq
    exact ha
  · intro ha
    exact ⟨m.val, ha, Subtype.ext rfl⟩

/-- a mapping is a forward fixpoint if, at every node, applying the
    transfer function to the incoming facts yields outF itself. -/
def IsForwardFixpointOf {A : Type} [Bot A] [Max A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) : Prop :=
  ∀ n : NodeOf g,
    outF n = nodeTransfer n.val (expectedInOf g edgeTransfer entryInit outF n)

/-- a mapping is a forward post-fixpoint if, at every node, joining the
    transfer function result with outF yields no change. -/
def IsForwardPostFixpointOf {A : Type} [Bot A] [Max A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) : Prop :=
  ∀ n : NodeOf g,
    (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit outF n)) ⊔ (outF n) = (outF n)

private lemma foldl_join_eT_mono
    {A : Type} [Bot A] [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (_join_idem : ∀ a : A, a ⊔ a = a)
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (edge_mono : ∀ e, monotoneD (edgeTransfer e))
    (outF1 outF2 : GFact g A) (hle : gfactLe outF1 outF2)
    (m : NodeOf g) (edges : List {e // e ∈ g.inEdges m.val})
    (acc1 acc2 : A) (hacc : acc1 ⊔ acc2 = acc1) :
    Eq ((edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF1 ⟨e.src, g.inEdges_src_mem m.val e he⟩)) acc1) ⊔
        (edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF2 ⟨e.src, g.inEdges_src_mem m.val e he⟩)) acc2))
       (edges.foldl (fun acc ⟨e, he⟩ =>
          acc ⊔ edgeTransfer e (outF1 ⟨e.src, g.inEdges_src_mem m.val e he⟩)) acc1) := by
  induction edges generalizing acc1 acc2 with
  | nil => exact hacc
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    let e_mem : NodeOf g := ⟨e.val.src, g.inEdges_src_mem m.val e.val e.property⟩
    have h_eT : (edgeTransfer e.val (outF1 e_mem)) ⊔ (edgeTransfer e.val (outF2 e_mem))
              = edgeTransfer e.val (outF1 e_mem) := edge_mono e.val _ _ (hle e_mem)
    calc (acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔ (acc2 ⊔ edgeTransfer e.val (outF2 e_mem))
        = ((acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔ acc2) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [← join_assoc]
      _ = (acc1 ⊔ (edgeTransfer e.val (outF1 e_mem) ⊔ acc2)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [join_assoc acc1]
      _ = (acc1 ⊔ (acc2 ⊔ edgeTransfer e.val (outF1 e_mem))) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [join_comm (edgeTransfer e.val (outF1 e_mem)) acc2]
      _ = ((acc1 ⊔ acc2) ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by
            rw [← join_assoc acc1 acc2]
      _ = (acc1 ⊔ edgeTransfer e.val (outF1 e_mem)) ⊔
            edgeTransfer e.val (outF2 e_mem) := by rw [hacc]
      _ = acc1 ⊔ (edgeTransfer e.val (outF1 e_mem) ⊔
            edgeTransfer e.val (outF2 e_mem)) := by rw [join_assoc]
      _ = acc1 ⊔ edgeTransfer e.val (outF1 e_mem) := by rw [h_eT]

private lemma joinPredEdgesOf_mono
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (join_idem : ∀ a : A, a ⊔ a = a)
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (edge_mono : ∀ e, monotoneD (edgeTransfer e))
    (outF1 outF2 : GFact g A) (hle : gfactLe outF1 outF2) (n : NodeOf g) :
    Eq ((joinPredEdgesOf g edgeTransfer outF1 n) ⊔ (joinPredEdgesOf g edgeTransfer outF2 n))
       (joinPredEdgesOf g edgeTransfer outF1 n) := by
  unfold joinPredEdgesOf
  exact foldl_join_eT_mono join_comm join_assoc join_idem g edgeTransfer edge_mono
    outF1 outF2 hle n (g.inEdges n.val).attach ⊥ ⊥ (join_idem ⊥)

private lemma expectedInOf_mono
  {A : Type} [Bot A] [Max A] [FiniteHeight A]
  (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A) (entryInit : A)
  [ll : LatticeLike A nodeTransfer edgeTransfer]
  (outF1 outF2 : GFact g A)
  (hle : gfactLe outF1 outF2) (n : NodeOf g) :
  Eq ((expectedInOf g edgeTransfer entryInit outF1 n) ⊔
    (expectedInOf g edgeTransfer entryInit outF2 n))
     (expectedInOf g edgeTransfer entryInit outF1 n) := by
  simp only [expectedInOf]
  split
  · exact ll.join_idem _
  · exact joinPredEdgesOf_mono ll.join_comm ll.join_assoc ll.join_idem g edgeTransfer ll.edge_mono
      outF1 outF2 hle n

private lemma T_postfix_of_postfix
    {A : Type} [Bot A] [Max A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode → A → A) (edgeTransfer : CFGEdge → A → A)
    (entryInit : A) (f : GFact g A)
    [ll : LatticeLike A nodeTransfer edgeTransfer]
    (hpost : IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit f) :
    IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedInOf g edgeTransfer entryInit f n)) := by
  intro n
  rw [ll.join_comm]
  apply ll.node_mono
  apply expectedInOf_mono g nodeTransfer edgeTransfer entryInit f
    (fun m => nodeTransfer m.val (expectedInOf g edgeTransfer entryInit f m))
  intro m
  simpa [ll.join_comm] using hpost m

private lemma join_ge_trans {A : Type} [Max A]
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (a b c : A) (hab : a ⊔ b = a) (hbc : b ⊔ c = b) :
    a ⊔ c = a := by
  calc a ⊔ c = (a ⊔ b) ⊔ c := by rw [hab]
    _ = a ⊔ (b ⊔ c) := join_assoc a b c
    _ = a ⊔ b := by rw [hbc]
    _ = a := hab

private lemma gfactLe_trans {g : CFG} {A : Type} [Max A]
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (f1 f2 f3 : GFact g A) (h12 : gfactLe f1 f2) (h23 : gfactLe f2 f3) :
    gfactLe f1 f3 :=
  fun n => join_ge_trans join_assoc _ _ _ (h12 n) (h23 n)

private lemma gfactLe_update_join {g : CFG} {A : Type} [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (join_idem : ∀ a : A, a ⊔ a = a)
    (outF : GFact g A) (n : NodeOf g) (v : A) :
    gfactLe (outF.update n (outF n ⊔ v)) outF := by
  intro m; simp only [GFact.update]
  split
  · rename_i h; subst h; rw [join_assoc, join_comm v, ← join_assoc, join_idem]
  · exact join_idem _

/-- the result of the worklist algorithm is always ≥ the initial facts. -/
theorem worklistForwardEdgeOf_mono
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (wl : List (NodeOf g))
    [ll : LatticeLike A nodeTransfer edgeTransfer] :
    let res := worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit outF wl
    gfactLe res outF := by
  induction outF, wl using worklistForwardEdgeOf.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForwardEdgeOf, gfactLe]
    intro n; exact ll.join_idem _
  | case2 o n r nin nout hnout ih =>
    rw [worklistForwardEdgeOf.eq_2, if_pos (by assumption)]
    exact ih
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForwardEdgeOf, if_neg (by assumption)]
    exact gfactLe_trans ll.join_assoc _ _ _ ih
      (gfactLe_update_join ll.join_comm ll.join_assoc ll.join_idem o n _)

-- ============================================================
-- Step 2: Generic invariant propagation combinator
-- ============================================================

/-- Generic invariant propagation combinator for the worklist algorithm.
    If a predicate `P` on `(outF, wl)` holds initially and is preserved by
    both the "unchanged" and "changed" branches, then `P (result, [])` holds.
    This is the Lean analogue of CompCert's `iterate_prop`. -/
theorem worklistForwardEdgeOf_invariant
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (wl : List (NodeOf g))
    (P : GFact g A → List (NodeOf g) → Prop)
    (hinit : P outF wl)
    (hstep_same : ∀ (o : GFact g A) (n : NodeOf g) (rest : List (NodeOf g)),
      P o (n :: rest) →
      let newIn := if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n
      o n ⊔ nodeTransfer n.val newIn = o n →
      P o rest)
    (hstep_changed : ∀ (o : GFact g A) (n : NodeOf g) (rest : List (NodeOf g)),
      P o (n :: rest) →
      let newIn := if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n
      let newOut := o n ⊔ nodeTransfer n.val newIn
      ¬(newOut = o n) →
      P (o.update n newOut) (rest ++ g.succOf n)) :
    P (worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit outF wl) [] := by
  induction outF, wl using worklistForwardEdgeOf.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    simp only [worklistForwardEdgeOf]
    exact hinit
  | case2 o n r nin nout hnout ih =>
    rw [worklistForwardEdgeOf.eq_2, if_pos (by assumption)]
    exact ih (hstep_same o n r hinit hnout)
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForwardEdgeOf, if_neg (by assumption)]
    exact ih (hstep_changed o n r hinit hnout)

/-- the result of the worklist algorithm is always a post-fixpoint -/
theorem worklistForwardEdgeOf_sound_postfixpoint
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : GFact g A) (wl0 : List (NodeOf g))
    [ll : LatticeLike A nodeTransfer edgeTransfer]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 →
      Eq
        ((nodeTransfer m.val (expectedInOf g edgeTransfer entryInit out0 m)) ⊔ (out0 m))
        (out0 m)) :
    let res := worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit out0 wl0
    IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit res := by
  let P : GFact g A → List (NodeOf g) → Prop := fun o wl =>
    ∀ m : NodeOf g, m ∉ wl →
      (nodeTransfer m.val (expectedInOf g edgeTransfer entryInit o m)) ⊔ (o m) = (o m)
  intro res n
  refine worklistForwardEdgeOf_invariant g nodeTransfer edgeTransfer entryInit
    out0 wl0 P hinv0 ?_ ?_ _ (by grind)
  · intros o n rest hP newIn ho m hmem
    by_cases hm : m = n <;> try grind
    subst hm
    have := newIn_eq_expectedIn g edgeTransfer entryInit o m newIn
      (by simp only [dite_eq_ite, newIn])
    simpa [ll.join_comm, <- this] using ho
  · intros o n rest hP newIn newOut hneq m hmem
    let t := (o n ⊔ nodeTransfer n.val
      (if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n))
    have heexp := expectedIn_update_non_pred _ edgeTransfer o entryInit n t m
      (by grind [mem_succOf_iff_mem_succ])
    rw [heexp] at *
    by_cases hm : m = n
    · subst hm
      dsimp [newOut]
      simp [GFact.update, expectedInOf, newIn]
      grind [ll.join_comm, ll.join_assoc, ll.join_idem]
    · have ho_m : GFact.update o n (o n ⊔ nodeTransfer n.val
        (if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n)) m
        = o m := by dsimp [GFact.update]; exact if_neg hm
      rw [ho_m]
      grind [List.mem_cons.mp]

/-- Least post-fixpoint completeness, derived via the invariant combinator. -/
theorem worklistForwardEdgeOf_complete_least_postfixpoint
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (wl : List (NodeOf g))
    [ll : LatticeLike A nodeTransfer edgeTransfer]
    (post : GFact g A) (hpost : IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit post)
    (hinv : gfactLe post outF) :
    let res := worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit outF wl
    gfactLe post res := by
  let P : GFact g A → List (NodeOf g) → Prop := fun o _ => gfactLe post o
  apply worklistForwardEdgeOf_invariant g nodeTransfer edgeTransfer entryInit outF wl P
    hinv (by grind)
  intros o m rest hP newIn hlub hneq n
  by_cases hmn : m = n
  · subst hmn
    have h_nT_mono := ll.node_mono m.val _ _ (
      expectedInOf_mono g nodeTransfer edgeTransfer entryInit post o hP m
    )
    have := newIn_eq_expectedIn g edgeTransfer entryInit o m newIn rfl
    grind [GFact.update, hP m, hpost m, ll.join_comm, ll.join_assoc]
  · have : ¬(n = m) := by exact Ne.intro fun a ↦ hmn (id (Eq.symm a))
    simp only [GFact.update, this, ↓reduceIte]
    exact hP n

/-- Fixpoint soundness, derived via the invariant combinator. -/
theorem worklistForwardEdgeOf_sound_fixpoint
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : GFact g A) (wl0 : List (NodeOf g))
    [ll : LatticeLike A nodeTransfer edgeTransfer]
    (hinv0 : ∀ m : NodeOf g, m ∉ wl0 →
      Eq ((nodeTransfer m.val (expectedInOf g edgeTransfer entryInit out0 m)) ⊔ (out0 m)) (out0 m))
    (hbot : ∀ (n : NodeOf g) v, out0 n ⊔ v = v) :
    let res := worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit out0 wl0
    IsForwardFixpointOf g nodeTransfer edgeTransfer entryInit res := by
  intro res n
  have hpostres : IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit res :=
    worklistForwardEdgeOf_sound_postfixpoint g nodeTransfer edgeTransfer entryInit out0 wl0 hinv0
  have hpostT : IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit
      (fun n => nodeTransfer n.val (expectedInOf g edgeTransfer entryInit res n)) :=
    T_postfix_of_postfix g nodeTransfer edgeTransfer entryInit res hpostres
  have hbase : gfactLe (fun n => nodeTransfer n.val (expectedInOf g edgeTransfer entryInit res n))
                out0 :=
    fun n => by rw [ll.join_comm]; exact hbot n _
  have hleast : gfactLe (fun n => nodeTransfer n.val (expectedInOf g edgeTransfer entryInit res n))
                res :=
    worklistForwardEdgeOf_complete_least_postfixpoint g nodeTransfer edgeTransfer entryInit out0
      wl0 _ hpostT hbase
  grind [hleast n, hpostres n]
