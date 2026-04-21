import LeanFormalisation.LBase.LBaseCFG.AltCFG
import LeanFormalisation.LBase.LBaseCFG.Analysis

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

private lemma ite_eq_newIn
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (n : NodeOf g)
    (newIn : A)
    (hdef : Eq newIn (if _ : n.val = g.entry then entryInit
        else joinPredEdgesOf g edgeTransfer outF n)) :
    Eq (if n.val = g.entry then entryInit
        else joinPredEdgesOf g edgeTransfer outF n) newIn := by
  rw [hdef]; exact (ite_decEq_irrel _ _ _ _).symm

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
  induction out0, wl0 using worklistForwardEdgeOf.induct g nodeTransfer edgeTransfer entryInit with
  | case1 out0 =>
    simp only [worklistForwardEdgeOf]
    intros n
    exact hinv0 n List.not_mem_nil
  | case2 o n r nin nout hnout ih =>
    rw [worklistForwardEdgeOf.eq_2, if_pos (by assumption)]
    apply ih
    intros m hmem
    by_cases hm : m = n
    · subst hm
      rw [ll.join_comm, <- newIn_eq_expectedIn g edgeTransfer entryInit o m nin rfl]
      grind
    · apply hinv0 m
      grind
  | case3 o n r nin nout hnout o' wl ih =>
    rw [worklistForwardEdgeOf, if_neg (by assumption)]
    apply ih
    intros m hmem
    have hsucc : m.val ∉ g.succ n.val := by
      intro h
      have : m ∈ g.succOf n := (mem_succOf_iff_mem_succ g n m).mpr h
      exact hmem (List.mem_append_right r this)
    have hexp := expectedIn_update_non_pred g edgeTransfer o entryInit n nout m hsucc
    by_cases hmn : m = n
    · rw [hexp, hmn]
      have ho_n : o' n = nout := by
        dsimp [o', GFact.update]
        exact if_pos rfl
      rw [ho_n]
      have hnin_eq : expectedInOf g edgeTransfer entryInit o n = nin := by
        unfold expectedInOf; rfl
      rw [hnin_eq]
      have hnout_eq : nout = o n ⊔ nodeTransfer n.val nin := rfl
      rw [hnout_eq, ll.join_comm, ll.join_assoc, ll.join_idem]
    · have ho_m : o' m = o m := by
        dsimp [o', GFact.update]
        exact if_neg hmn
      rw [ho_m, hexp]
      apply hinv0
      intro h
      cases List.mem_cons.mp h with
      | inl h_eq => exact hmn h_eq
      | inr h_in => exact hmem (List.mem_append_left _ h_in)

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

/-- the result of the worklist algorithm is the least post-fixpoint greater
    than or equal to the initial facts. -/
theorem worklistForwardEdgeOf_complete_least_postfixpoint
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : GFact g A) (wl : List (NodeOf g))
    [ll : LatticeLike A nodeTransfer edgeTransfer]
    (post : GFact g A) (hpost : IsForwardPostFixpointOf g nodeTransfer edgeTransfer entryInit post)
    (hinv : gfactLe post outF) :
    let res := worklistForwardEdgeOf g nodeTransfer edgeTransfer entryInit outF wl
    gfactLe post res := by
  induction outF, wl using worklistForwardEdgeOf.induct g nodeTransfer edgeTransfer entryInit with
  | case1 o =>
    rw [worklistForwardEdgeOf]
    exact hinv
  | case2 o n r nin nout hnout ih =>
    rw [worklistForwardEdgeOf]
    have : o n ⊔ nodeTransfer n.val
      (if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n) = o n := hnout
    rw [if_pos this]
    exact ih hinv
  | case3 o n r nin nout hnout o' wl' ih =>
    rw [worklistForwardEdgeOf]
    have : ¬(o n ⊔ nodeTransfer n.val
      (if n.val = g.entry then entryInit else joinPredEdgesOf g edgeTransfer o n) = o n) := hnout
    rw [if_neg this]
    apply ih
    intro m
    by_cases hmn : m = n
    · rw [hmn]
      have h_post_ge_out : (post n) ⊔ (o n) = post n := hinv n
      have h_post_postfix :
          (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n)) ⊔ (post n)
          = post n := hpost n
      have h_exp_mono := expectedInOf_mono g nodeTransfer edgeTransfer
        entryInit post o hinv n
      have h_nT_mono :
          (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n)) ⊔
          (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit o n))
          = nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n) :=
        ll.node_mono n.val _ _ h_exp_mono
      have h_post_ge_nT_postk :
          (post n) ⊔ (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n))
          = post n := by rw [ll.join_comm]; exact h_post_postfix
      have h_post_ge_nT_exp :
          (post n) ⊔ (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit o n))
          = post n := by
        calc (post n) ⊔ (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit o n))
            = ((post n) ⊔ (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n))) ⊔
                (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit o n)) := by
                rw [h_post_ge_nT_postk]
          _ = (post n) ⊔ ((nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n)) ⊔
                (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit o n))) := by
                rw [ll.join_assoc]
          _ = (post n) ⊔
                (nodeTransfer n.val (expectedInOf g edgeTransfer entryInit post n)) := by
                rw [h_nT_mono]
          _ = post n := h_post_ge_nT_postk
      have h_newIn_eq := newIn_eq_expectedIn g edgeTransfer entryInit o n nin rfl
      have h_post_ge_nT : (post n) ⊔ (nodeTransfer n.val nin) = post n := by
        rw [h_newIn_eq]; exact h_post_ge_nT_exp
      have ho_n : o' n = nout := by
        dsimp [o', GFact.update]
        exact if_pos rfl
      rw [ho_n]
      have hnout_eq : nout = o n ⊔ nodeTransfer n.val nin := rfl
      rw [hnout_eq]
      grind [ll.join_assoc]
    · have ho_m : o' m = o m := by
        dsimp [o', GFact.update]
        exact if_neg hmn
      rw [ho_m]
      exact hinv m

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

/-- the result of the worklist algorithm is a fixpoint of the analysis equations. -/
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
  intro res
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
    worklistForwardEdgeOf_complete_least_postfixpoint g nodeTransfer edgeTransfer entryInit out0 wl0
      _ hpostT hbase
  intro n
  grind [hleast n, hpostres n]
