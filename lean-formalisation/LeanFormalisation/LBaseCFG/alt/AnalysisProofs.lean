import LeanFormalisation.LBaseCFG.alt.AltCFG
import LeanFormalisation.LBaseCFG.alt.Analysis

open LeanFormalisation.AltCFG

def IsForwardFixpoint {A : Type} [Bot A] [Max A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) : Prop :=
  (∀ n, inF n = expectedIn g edgeTransfer entryInit outF n) ∧
  (∀ n, outF n = nodeTransfer n (inF n))

def IsForwardPostFixpoint {A : Type} [Bot A] [Max A]
      (g : CFG)
      (nodeTransfer : CFGNode -> A -> A)
      (edgeTransfer : CFGEdge -> A -> A)
      (entryInit : A)
      (outF : fact A) : Prop :=
   ∀ n, (nodeTransfer n (expectedIn g edgeTransfer entryInit outF n)) ⊔ (outF n) = (outF n)

def monotoneD {A : Type} [Max A] (f : A -> A) : Prop :=
  ∀ x y, x ⊔ y = x -> (f x) ⊔ (f y) = (f x)

def factLe {A : Type} [Max A] (f g : fact A) : Prop :=
  ∀ n, (f n) ⊔ (g n) = (f n)

class WorklistReq {A : Type} [Bot A] [Max A] [FiniteHeight A]
    (g : CFG)
    (nodeTransfer : CFGNode -> A -> A)
    (edgeTransfer : CFGEdge -> A -> A) : Prop where
  join_comm : ∀ a b : A, a ⊔ b = b ⊔ a
  join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)
  join_idem : ∀ a : A, a ⊔ a = a
  bot_le : ∀ a : A, a ⊔ ⊥ = a
  node_mono : ∀ n, monotoneD (nodeTransfer n)
  edge_mono : ∀ e, monotoneD (edgeTransfer e)

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
    (entryInit : A) (outF : fact A) (n : CFGNode)
    (newIn : A)
    (hdef : Eq newIn (if h : n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) :
    Eq newIn (expectedIn g edgeTransfer entryInit outF n) := by
  rw [hdef]; simp only [expectedIn]; exact ite_decEq_irrel _ _ _ _

private lemma ite_eq_newIn
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (outF : fact A) (n : CFGNode)
    (newIn : A)
    (hdef : Eq newIn (if h : n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) :
    Eq (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n) newIn := by
  rw [hdef]; exact (ite_decEq_irrel _ _ _ _).symm

private lemma foldl_join_eT_update
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (edgeTransfer : CFGEdge -> A -> A) (outF : fact A)
    (n : CFGNode) (v : A) (edges : List CFGEdge)
    (hnoedge : ∀ e ∈ edges, e.src ≠ n) (init : A) :
    Eq (edges.foldl (fun acc e => acc ⊔ edgeTransfer e ((outF.update n v) e.src)) init)
       (edges.foldl (fun acc e => acc ⊔ edgeTransfer e (outF e.src)) init) := by
  induction edges generalizing init with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    have he : e.src ≠ n := hnoedge e (List.Mem.head _)
    simp only [fact.update, he, ↓reduceIte]
    exact ih (fun e' he' => hnoedge e' (List.mem_cons_of_mem e he')) _

private lemma joinPredEdges_update_non_pred
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A) (outF : fact A)
    (n : CFGNode) (v : A) (m : CFGNode)
    (hnoedge : ∀ e ∈ g.inEdges m, e.src ≠ n) :
    Eq (joinPredEdges g edgeTransfer (outF.update n v) m)
       (joinPredEdges g edgeTransfer outF m) := by
  unfold joinPredEdges
  exact foldl_join_eT_update edgeTransfer outF n v (g.inEdges m) hnoedge ⊥

private lemma not_succ_no_in_edge
    (g : CFG) (n m : CFGNode) (h : m ∉ g.succ n) :
    ∀ e ∈ g.inEdges m, e.src ≠ n := by
  intro e he hsrc
  apply h
  simp only [CFG.succ, CFG.outEdges, CFG.inEdges] at he ⊢
  obtain ⟨he_in, he_prop⟩ := List.mem_filter.mp he
  have he_dst : e.dst = m := of_decide_eq_true he_prop
  exact mem_of_mem_eraseDups
    (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he_in, decide_eq_true hsrc⟩, he_dst⟩)

private lemma expectedIn_update_non_pred
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A) (outF : fact A)
    (entryInit : A) (n : CFGNode) (v : A) (m : CFGNode) (h : m ∉ g.succ n) :
    Eq (expectedIn g edgeTransfer entryInit (outF.update n v) m)
       (expectedIn g edgeTransfer entryInit outF m) := by
  simp only [expectedIn]
  split
  · rfl
  · exact joinPredEdges_update_non_pred g edgeTransfer outF n v m
      (not_succ_no_in_edge g n m h)

-- ============================================================
-- Theorem 4: Fixpoint Stability
-- ============================================================

theorem worklist_complete_fixpoint_stability
    [DecidableEq CFGNode]
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    (hwl : ∀ x ∈ wl, x ∈ g.nodes)
    [wr : WorklistReq g nodeTransfer edgeTransfer]
    (hfp : IsForwardFixpoint g nodeTransfer edgeTransfer entryInit inF outF) :
    Eq (worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF wl hwl)
       (inF, outF) := by
  induction inF, outF, wl, hwl using
      worklistForwardEdge.induct g nodeTransfer edgeTransfer entryInit with
  | case1 _ _ _ => simp [worklistForwardEdge]
  | case2 inF outF n rest hwl _newIn _newOut _heq _hwl_dup ih =>
    rw [worklistForwardEdge.eq_2]
    obtain ⟨hIn, hOut⟩ := hfp
    have h1 := ite_eq_newIn g edgeTransfer entryInit outF n _newIn rfl
    have hcond : Eq (outF n ⊔ nodeTransfer n (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) (outF n) := by
      rw [h1, newIn_eq_expectedIn g edgeTransfer entryInit outF n _newIn rfl,
        ← hIn n, hOut n, wr.join_idem]
    rw [if_pos hcond]
    exact ih ⟨hIn, hOut⟩
  | case3 inF outF n rest hwl _newIn _newOut hne _inF' _outF' _wl' _hwl_dup _ih =>
    exfalso; apply hne
    obtain ⟨hIn, hOut⟩ := hfp
    show Eq (outF n ⊔ nodeTransfer n _newIn) (outF n)
    rw [newIn_eq_expectedIn g edgeTransfer entryInit outF n _newIn rfl,
      ← hIn n, hOut n, wr.join_idem]

-- ============================================================
-- Theorem 2: Post-Fixpoint Soundness
-- ============================================================

private theorem worklist_postfix_aux
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    (hwl : ∀ x ∈ wl, x ∈ g.nodes)
    [wr : WorklistReq g nodeTransfer edgeTransfer]
    (hinv : ∀ m, m ∉ wl →
      Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit outF m)) ⊔ (outF m)) (outF m)) :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF wl hwl
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res.2 := by
  induction inF, outF, wl, hwl using
      worklistForwardEdge.induct g nodeTransfer edgeTransfer entryInit with
  | case1 inF outF hwl =>
    simp only [IsForwardPostFixpoint]
    intro n; rw [worklistForwardEdge.eq_1]
    exact hinv n (by simp)
  | case2 inF outF n rest hwl _newIn _newOut heq _hwl_dup ih =>
    rw [worklistForwardEdge.eq_2]
    have h_ite := ite_eq_newIn g edgeTransfer entryInit outF n _newIn rfl
    have hcond : Eq (outF n ⊔ nodeTransfer n (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) (outF n) := by
      rw [h_ite]; exact heq
    rw [if_pos hcond]
    apply ih
    intro m hm_not_rest
    by_cases hm : m = n
    · -- m = n: the no-change condition gives post-fixpoint property
      -- After subst, n is eliminated so use m everywhere
      subst hm
      rw [wr.join_comm, ← newIn_eq_expectedIn g edgeTransfer entryInit outF m _newIn rfl]
      exact heq
    · exact hinv m (fun h => by cases List.mem_cons.mp h with
        | inl h => exact hm h
        | inr h => exact hm_not_rest h)
  | case3 inF outF n rest hwl _newIn _newOut hne _inF' _outF' _wl' _hwl_dup ih =>
    rw [worklistForwardEdge.eq_2]
    have h_ite := ite_eq_newIn g edgeTransfer entryInit outF n _newIn rfl
    have hcond_false : ¬ Eq (outF n ⊔ nodeTransfer n (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) (outF n) := by
      rw [h_ite]; exact hne
    rw [if_neg hcond_false]
    apply ih
    intro m hm_not_wl'
    have hm_not_rest : m ∉ rest := fun h => hm_not_wl' (List.mem_append.mpr (Or.inl h))
    have hm_not_succ : m ∉ g.succ n := fun h => hm_not_wl' (List.mem_append.mpr (Or.inr h))
    have hexp_eq := expectedIn_update_non_pred g edgeTransfer outF entryInit n _newOut m hm_not_succ
    by_cases hm : m = n
    · -- m = n: outF' n = _newOut = outF n ⊔ nodeTransfer n _newIn
      subst hm
      -- After subst, n is gone, use m. _outF' = outF.update m _newOut
      show Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit _outF' m)) ⊔ _outF' m) (_outF' m)
      change Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit (outF.update m _newOut) m))
        ⊔ (outF.update m _newOut) m) ((outF.update m _newOut) m)
      simp only [fact.update, ↓reduceIte]
      rw [hexp_eq]
      rw [← newIn_eq_expectedIn g edgeTransfer entryInit outF m _newIn rfl]
      -- nodeTransfer m _newIn ⊔ (outF m ⊔ nodeTransfer m _newIn) = outF m ⊔ nodeTransfer m _newIn
      rw [wr.join_comm (nodeTransfer m _newIn) (outF m ⊔ nodeTransfer m _newIn),
        wr.join_assoc (outF m) (nodeTransfer m _newIn) (nodeTransfer m _newIn),
        wr.join_idem]
    · -- m ≠ n: outF' m = outF m, expectedIn unchanged
      show Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit _outF' m)) ⊔ _outF' m) (_outF' m)
      change Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit (outF.update n _newOut) m))
        ⊔ (outF.update n _newOut) m) ((outF.update n _newOut) m)
      simp only [fact.update, show (m = n) = False from by simp [hm], ite_false]
      rw [hexp_eq]
      exact hinv m (fun h => by cases List.mem_cons.mp h with
        | inl h => exact hm h
        | inr h => exact hm_not_rest h)

theorem worklist_sound_postfixpoint
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : fact A) (wl0 : List CFGNode)
    (hwl0 : ∀ x ∈ wl0, x ∈ g.nodes)
    [wr : WorklistReq g nodeTransfer edgeTransfer]
    (hinv0 : ∀ m, m ∉ wl0 →
      Eq ((nodeTransfer m (expectedIn g edgeTransfer entryInit out0 m)) ⊔ (out0 m)) (out0 m)) :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit in0 out0 wl0 hwl0
    IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit res.2 :=
  worklist_postfix_aux g nodeTransfer edgeTransfer entryInit in0 out0 wl0 hwl0 hinv0

-- ============================================================
-- Theorem 3: Fixpoint Soundness (placeholder)
-- ============================================================

theorem worklist_sound_fixpoint
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (out0 : fact A) (wl0 : List CFGNode)
    (hwl0 : ∀ x ∈ wl0, x ∈ g.nodes)
    [WorklistReq g nodeTransfer edgeTransfer] :
    let res := runDataflow g nodeTransfer edgeTransfer entryInit out0 wl0 hwl0
    IsForwardFixpoint g nodeTransfer edgeTransfer entryInit res.1 res.2 := by
  sorry

-- ============================================================
-- Theorem 5: Least Post-Fixpoint
-- ============================================================

-- Monotonicity lemmas for joinPredEdges and expectedIn w.r.t. outF

private lemma foldl_join_eT_mono
    {A : Type} [Bot A] [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (_join_idem : ∀ a : A, a ⊔ a = a)
    (edgeTransfer : CFGEdge -> A -> A)
    (edge_mono : ∀ e, monotoneD (edgeTransfer e))
    (outF1 outF2 : fact A) (hle : factLe outF1 outF2)
    (edges : List CFGEdge) (acc1 acc2 : A) (hacc : acc1 ⊔ acc2 = acc1) :
    Eq ((edges.foldl (fun acc e => acc ⊔ edgeTransfer e (outF1 e.src)) acc1) ⊔
        (edges.foldl (fun acc e => acc ⊔ edgeTransfer e (outF2 e.src)) acc2))
       (edges.foldl (fun acc e => acc ⊔ edgeTransfer e (outF1 e.src)) acc1) := by
  induction edges generalizing acc1 acc2 with
  | nil => exact hacc
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    have h_eT : (edgeTransfer e (outF1 e.src)) ⊔ (edgeTransfer e (outF2 e.src))
              = edgeTransfer e (outF1 e.src) := edge_mono e _ _ (hle e.src)
    calc (acc1 ⊔ edgeTransfer e (outF1 e.src)) ⊔ (acc2 ⊔ edgeTransfer e (outF2 e.src))
        = ((acc1 ⊔ edgeTransfer e (outF1 e.src)) ⊔ acc2) ⊔
            edgeTransfer e (outF2 e.src) := by
            rw [← join_assoc]
      _ = (acc1 ⊔ (edgeTransfer e (outF1 e.src) ⊔ acc2)) ⊔
            edgeTransfer e (outF2 e.src) := by
            rw [join_assoc acc1]
      _ = (acc1 ⊔ (acc2 ⊔ edgeTransfer e (outF1 e.src))) ⊔
            edgeTransfer e (outF2 e.src) := by
            rw [join_comm (edgeTransfer e (outF1 e.src)) acc2]
      _ = ((acc1 ⊔ acc2) ⊔ edgeTransfer e (outF1 e.src)) ⊔
            edgeTransfer e (outF2 e.src) := by
            rw [← join_assoc acc1 acc2]
      _ = (acc1 ⊔ edgeTransfer e (outF1 e.src)) ⊔
            edgeTransfer e (outF2 e.src) := by rw [hacc]
      _ = acc1 ⊔ (edgeTransfer e (outF1 e.src) ⊔
            edgeTransfer e (outF2 e.src)) := by rw [join_assoc]
      _ = acc1 ⊔ edgeTransfer e (outF1 e.src) := by rw [h_eT]

private lemma joinPredEdges_mono
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (join_idem : ∀ a : A, a ⊔ a = a)
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A)
    (edge_mono : ∀ e, monotoneD (edgeTransfer e))
    (outF1 outF2 : fact A) (hle : factLe outF1 outF2) (n : CFGNode) :
    Eq ((joinPredEdges g edgeTransfer outF1 n) ⊔ (joinPredEdges g edgeTransfer outF2 n))
       (joinPredEdges g edgeTransfer outF1 n) := by
  unfold joinPredEdges
  exact foldl_join_eT_mono join_comm join_assoc join_idem edgeTransfer edge_mono
    outF1 outF2 hle (g.inEdges n) ⊥ ⊥ (join_idem ⊥)

private lemma expectedIn_mono
    [DecidableEq CFGNode] {A : Type} [Bot A] [Max A]
    (join_comm : ∀ a b : A, a ⊔ b = b ⊔ a)
    (join_assoc : ∀ a b c : A, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c))
    (join_idem : ∀ a : A, a ⊔ a = a)
    (g : CFG) (edgeTransfer : CFGEdge -> A -> A) (entryInit : A)
    (edge_mono : ∀ e, monotoneD (edgeTransfer e))
    (outF1 outF2 : fact A) (hle : factLe outF1 outF2) (n : CFGNode) :
    Eq ((expectedIn g edgeTransfer entryInit outF1 n) ⊔
        (expectedIn g edgeTransfer entryInit outF2 n))
       (expectedIn g edgeTransfer entryInit outF1 n) := by
  simp only [expectedIn]
  split
  · exact join_idem _
  · exact joinPredEdges_mono join_comm join_assoc join_idem g edgeTransfer edge_mono
      outF1 outF2 hle n

private lemma join_le_of_le_both {A : Type} [Max A]
    (join_assoc : ∀ x y z : A, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z))
    {a b c : A} (hab : a ⊔ b = a) (hac : a ⊔ c = a) :
    a ⊔ (b ⊔ c) = a := by
  calc a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by rw [← join_assoc]
    _ = a ⊔ c := by rw [hab]
    _ = a := hac

private theorem worklist_least_postfix_aux
    [DecidableEq CFGNode]
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (inF outF : fact A) (wl : List CFGNode)
    (hwl : ∀ x ∈ wl, x ∈ g.nodes)
    [wr : WorklistReq g nodeTransfer edgeTransfer]
    (post : fact A) (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit post)
    (hinv : factLe post outF) :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit inF outF wl hwl
    factLe post res.2 := by
  induction inF, outF, wl, hwl using
      worklistForwardEdge.induct g nodeTransfer edgeTransfer entryInit with
  | case1 inF outF hwl =>
    simp only [worklistForwardEdge, factLe] at *
    exact hinv
  | case2 inF outF n rest hwl _newIn _newOut heq _hwl_dup ih =>
    rw [worklistForwardEdge.eq_2]
    have h_ite := ite_eq_newIn g edgeTransfer entryInit outF n _newIn rfl
    have hcond : Eq (outF n ⊔ nodeTransfer n (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) (outF n) := by
      rw [h_ite]; exact heq
    rw [if_pos hcond]
    exact ih hinv
  | case3 inF outF n rest hwl _newIn _newOut hne _inF' _outF' _wl' _hwl_dup ih =>
    rw [worklistForwardEdge.eq_2]
    have h_ite := ite_eq_newIn g edgeTransfer entryInit outF n _newIn rfl
    have hcond_false : ¬ Eq (outF n ⊔ nodeTransfer n (if n = g.entry then entryInit
        else joinPredEdges g edgeTransfer outF n)) (outF n) := by
      rw [h_ite]; exact hne
    rw [if_neg hcond_false]
    apply ih
    intro k
    show (post k) ⊔ (_outF' k) = post k
    change (post k) ⊔ ((outF.update n _newOut) k) = post k
    simp only [fact.update]
    split
    · rename_i heq_kn; subst heq_kn
      have h_post_ge_out : (post k) ⊔ (outF k) = post k := hinv k
      have h_post_postfix :
          (nodeTransfer k (expectedIn g edgeTransfer entryInit post k)) ⊔ (post k)
          = post k := hpost k
      have h_exp_mono := expectedIn_mono wr.join_comm wr.join_assoc wr.join_idem
        g edgeTransfer entryInit wr.edge_mono post outF hinv k
      have h_nT_mono :
          (nodeTransfer k (expectedIn g edgeTransfer entryInit post k)) ⊔
          (nodeTransfer k (expectedIn g edgeTransfer entryInit outF k))
          = nodeTransfer k (expectedIn g edgeTransfer entryInit post k) :=
        wr.node_mono k _ _ h_exp_mono
      have h_post_ge_nT_postk :
          (post k) ⊔ (nodeTransfer k (expectedIn g edgeTransfer entryInit post k))
          = post k := by rw [wr.join_comm]; exact h_post_postfix
      have h_post_ge_nT_exp :
          (post k) ⊔ (nodeTransfer k (expectedIn g edgeTransfer entryInit outF k))
          = post k := by
        calc (post k) ⊔ (nodeTransfer k (expectedIn g edgeTransfer entryInit outF k))
            = ((post k) ⊔ (nodeTransfer k (expectedIn g edgeTransfer entryInit post k))) ⊔
                (nodeTransfer k (expectedIn g edgeTransfer entryInit outF k)) := by
                rw [h_post_ge_nT_postk]
          _ = (post k) ⊔ ((nodeTransfer k (expectedIn g edgeTransfer entryInit post k)) ⊔
                (nodeTransfer k (expectedIn g edgeTransfer entryInit outF k))) := by
                rw [wr.join_assoc]
          _ = (post k) ⊔
                (nodeTransfer k (expectedIn g edgeTransfer entryInit post k)) := by
                rw [h_nT_mono]
          _ = post k := h_post_ge_nT_postk
      have h_newIn_eq := newIn_eq_expectedIn g edgeTransfer entryInit outF k _newIn rfl
      have h_post_ge_nT : (post k) ⊔ (nodeTransfer k _newIn) = post k := by
        rw [h_newIn_eq]; exact h_post_ge_nT_exp
      exact join_le_of_le_both wr.join_assoc h_post_ge_out h_post_ge_nT
    · exact hinv k

-- Corrected statement: factLe post res.2 (post ≥ result, i.e., result is least)
-- Added hbase : factLe post out0 as the base case for the invariant.
theorem worklist_complete_least_postfixpoint
    [DecidableEq CFGNode]
    {A : Type} [Bot A] [Max A] [DecidableEq A] [FiniteHeight A]
    (g : CFG) (nodeTransfer : CFGNode -> A -> A) (edgeTransfer : CFGEdge -> A -> A)
    (entryInit : A) (in0 out0 : fact A) (wl0 : List CFGNode)
    (hwl0 : ∀ x ∈ wl0, x ∈ g.nodes)
    [wr : WorklistReq g nodeTransfer edgeTransfer]
    (post : fact A) (hpost : IsForwardPostFixpoint g nodeTransfer edgeTransfer entryInit post)
    (hbase : factLe post out0) :
    let res := worklistForwardEdge g nodeTransfer edgeTransfer entryInit in0 out0 wl0 hwl0
    factLe post res.2 :=
  worklist_least_postfix_aux g nodeTransfer edgeTransfer entryInit in0 out0 wl0 hwl0
    post hpost hbase
