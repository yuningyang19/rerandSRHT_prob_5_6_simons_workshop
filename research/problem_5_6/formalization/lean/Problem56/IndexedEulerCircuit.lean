import Problem56.GraphEven

/-!
# Euler circuits for finite indexed multigraphs

This file keeps every edge occurrence in the indexing type `ε`.  Consequently
parallel edges are never identified.  A loop has two incidences (its source and
target incidence), exactly as in `graphDegree`.

The proof infrastructure is deliberately independent of the open graph
conversion and rank interfaces.  It uses
oriented indexed edges and finite lists, so later graph-to-DAG work can choose a
cut in an exact edge permutation without quotienting parallel occurrences.
-/

namespace Problem56

/-- An occurrence of an indexed edge together with a chosen orientation.
`false` uses the declared source-to-target orientation and `true` reverses it. -/
abbrev OrientedIndexedEdge (ε : Type*) := ε × Bool

def orientedTail {ι ε : Type*} (src dst : ε → ι) : OrientedIndexedEdge ε → ι
  | (e, false) => src e
  | (e, true) => dst e

def orientedHead {ι ε : Type*} (src dst : ε → ι) : OrientedIndexedEdge ε → ι
  | (e, false) => dst e
  | (e, true) => src e

def orientFrom {ι ε : Type*} [DecidableEq ι]
    (src _dst : ε → ι) (e : ε) (v : ι) :
    OrientedIndexedEdge ε :=
  if src e = v then (e, false) else (e, true)

def orientTo {ι ε : Type*} [DecidableEq ι]
    (_src dst : ε → ι) (e : ε) (v : ι) :
    OrientedIndexedEdge ε :=
  if dst e = v then (e, false) else (e, true)

@[simp] theorem orientedTail_orientFrom {ι ε : Type*} [DecidableEq ι]
    (src dst : ε → ι) (e : ε) (v : ι)
    (hinc : src e = v ∨ dst e = v) :
    orientedTail src dst (orientFrom src dst e v) = v := by
  rcases hinc with h | h
  · simp [orientFrom, h, orientedTail]
  · by_cases hs : src e = v
    · simp [orientFrom, hs, orientedTail]
    · simp [orientFrom, hs, orientedTail, h]

@[simp] theorem orientedHead_orientTo {ι ε : Type*} [DecidableEq ι]
    (src dst : ε → ι) (e : ε) (v : ι)
    (hinc : src e = v ∨ dst e = v) :
    orientedHead src dst (orientTo src dst e v) = v := by
  rcases hinc with h | h
  · by_cases hd : dst e = v
    · simp [orientTo, hd, orientedHead]
    · simp [orientTo, hd, orientedHead, h]
  · simp [orientTo, h, orientedHead]

@[simp] theorem orientFrom_edge {ι ε : Type*} [DecidableEq ι]
    (src dst : ε → ι) (e : ε) (v : ι) :
    (orientFrom src dst e v).1 = e := by
  by_cases h : src e = v <;> simp [orientFrom, h]

@[simp] theorem orientTo_edge {ι ε : Type*} [DecidableEq ι]
    (src dst : ε → ι) (e : ε) (v : ι) :
    (orientTo src dst e v).1 = e := by
  by_cases h : dst e = v <;> simp [orientTo, h]

/-- A trail is a list of oriented indexed occurrences whose consecutive
endpoints match and whose underlying edge indices have no repetitions. -/
structure IndexedTrail {ι ε : Type*} (src dst : ε → ι) where
  steps : List (OrientedIndexedEdge ε)
  adjacent : steps.IsChain fun a b => orientedHead src dst a = orientedTail src dst b
  edge_nodup : (steps.map Prod.fst).Nodup

namespace IndexedTrail

variable {ι ε : Type*} {src dst : ε → ι}

def incidenceCount [DecidableEq ι]
    (L : List (OrientedIndexedEdge ε)) (v : ι) : ℕ :=
  (L.map fun q =>
    (if orientedTail src dst q = v then 1 else 0) +
      (if orientedHead src dst q = v then 1 else 0)).sum

def edgeIncidence [DecidableEq ι] (src dst : ε → ι) (e : ε) (v : ι) : ℕ :=
  (if src e = v then 1 else 0) + (if dst e = v then 1 else 0)

@[simp] theorem oriented_edgeIncidence [DecidableEq ι]
    (src dst : ε → ι) (q : OrientedIndexedEdge ε) (v : ι) :
    (if orientedTail src dst q = v then 1 else 0) +
      (if orientedHead src dst q = v then 1 else 0) =
        edgeIncidence src dst q.1 v := by
  rcases q with ⟨e, b⟩
  cases b <;> simp [orientedTail, orientedHead, edgeIncidence, add_comm] <;> rfl

def IsClosed (T : IndexedTrail src dst) : Prop :=
  ∀ h : T.steps ≠ [],
    orientedTail src dst (T.steps.head h) =
      orientedHead src dst (T.steps.getLast h)

def CoversEveryEdge (T : IndexedTrail src dst) : Prop :=
  ∀ e : ε, e ∈ T.steps.map Prod.fst

def Visits (T : IndexedTrail src dst) (v : ι) : Prop :=
  ∃ q ∈ T.steps,
    orientedTail src dst q = v ∨ orientedHead src dst q = v

def IsEulerCircuit (T : IndexedTrail src dst) : Prop :=
  T.IsClosed ∧ T.CoversEveryEdge

private def IsCyclicChain {α : Type*} (R : α → α → Prop) (L : List α) : Prop :=
  L.IsChain R ∧ ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, R x y

private theorem cyclicChain_rotate_split {α : Type*} {R : α → α → Prop}
    (A B : List α) (q : α)
    (h : IsCyclicChain R (A ++ q :: B)) :
    IsCyclicChain R ((q :: B) ++ A) := by
  rcases h with ⟨hchain, hcycle⟩
  cases A with
  | nil =>
      simpa only [IsCyclicChain, List.nil_append, List.append_nil] using
        And.intro hchain hcycle
  | cons a A =>
      have hpre : (a :: A).IsChain R := hchain.left_of_append
      have hsuf : (q :: B).IsChain R := hchain.right_of_append
      refine ⟨hsuf.append hpre ?_, ?_⟩
      · intro x hx y hy
        exact hcycle x (List.mem_getLast?_append_of_mem_getLast? hx)
          y (List.mem_head?_append_of_mem_head? hy)
      · intro x hx y hy
        have hxpre : x ∈ (a :: A).getLast? := by
          rw [List.getLast?_append_of_ne_nil (q :: B) (by simp)] at hx
          exact hx
        have hysuf : y ∈ (q :: B).head? := by
          rw [List.head?_append_of_ne_nil (q :: B) (by simp)] at hy
          exact hy
        exact (List.isChain_append.mp hchain).2.2 x hxpre y hysuf

def singleton (src dst : ε → ι) (q : OrientedIndexedEdge ε) :
    IndexedTrail src dst where
  steps := [q]
  adjacent := .singleton q
  edge_nodup := by simp

@[simp] theorem singleton_steps (q : OrientedIndexedEdge ε) :
    (singleton src dst q).steps = [q] := rfl

theorem length_le_card [Fintype ε] (T : IndexedTrail src dst) :
    T.steps.length ≤ Fintype.card ε := by
  rw [← List.length_map]
  exact T.edge_nodup.length_le_card

theorem incidenceCount_eq_sum_usedEdges [DecidableEq ι] [DecidableEq ε]
    (T : IndexedTrail src dst) (v : ι) :
    incidenceCount (src := src) (dst := dst) T.steps v =
      ∑ e ∈ (T.steps.map Prod.fst).toFinset, edgeIncidence src dst e v := by
  rw [incidenceCount]
  simp_rw [oriented_edgeIncidence]
  change (List.map ((edgeIncidence src dst · v) ∘ Prod.fst)
    T.steps).sum = _
  rw [← List.map_map]
  exact (List.sum_toFinset (edgeIncidence src dst · v) T.edge_nodup).symm

theorem graphDegree_eq_sum_edgeIncidence [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (v : ι) :
    graphDegree src dst v = ∑ e : ε, edgeIncidence src dst e v := by
  classical
  rw [graphDegree]
  calc
    (Finset.univ.filter fun e => src e = v).card +
        (Finset.univ.filter fun e => dst e = v).card =
        (∑ e : ε, if src e = v then 1 else 0) +
          ∑ e : ε, if dst e = v then 1 else 0 := by
            congr 1
            · rw [Finset.card_eq_sum_ones]
              simp only [Finset.sum_filter]
            · rw [Finset.card_eq_sum_ones]
              simp only [Finset.sum_filter]
    _ = ∑ e : ε, edgeIncidence src dst e v := by
      rw [← Finset.sum_add_distrib]
      rfl

theorem incidenceCount_eq_graphDegree_of_incident_used
    [Fintype ε] [DecidableEq ι] [DecidableEq ε]
    (T : IndexedTrail src dst) (v : ι)
    (hused : ∀ e : ε, src e = v ∨ dst e = v → e ∈ T.steps.map Prod.fst) :
    incidenceCount (src := src) (dst := dst) T.steps v =
      graphDegree src dst v := by
  rw [incidenceCount_eq_sum_usedEdges T v,
    graphDegree_eq_sum_edgeIncidence src dst v]
  apply Finset.sum_subset
    (show (T.steps.map Prod.fst).toFinset ⊆ (Finset.univ : Finset ε) from
      Finset.subset_univ _)
  intro e _ hnot
  have hninc : ¬(src e = v ∨ dst e = v) := by
    intro hinc
    exact hnot (List.mem_toFinset.mpr (hused e hinc))
  push Not at hninc
  simp [edgeIncidence, hninc.1, hninc.2]

/-- Exact endpoint parity bookkeeping for an indexed walk.  Internal arrivals
and departures occur in matched pairs.  No edge-distinctness is needed here. -/
theorem incidenceCount_eq_endpoints_add_twice [DecidableEq ι]
    (L : List (OrientedIndexedEdge ε))
    (hchain : L.IsChain fun a b =>
      orientedHead src dst a = orientedTail src dst b)
    (hne : L ≠ []) (v : ι) :
    ∃ k : ℕ,
      incidenceCount (src := src) (dst := dst) L v =
        (if orientedTail src dst (L.head hne) = v then 1 else 0) +
        (if orientedHead src dst (L.getLast hne) = v then 1 else 0) + 2 * k := by
  induction L using List.twoStepInduction with
  | nil => exact (hne rfl).elim
  | singleton q =>
      refine ⟨0, ?_⟩
      simp only [incidenceCount, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, List.head_cons, List.getLast_singleton, mul_zero]
      rfl
  | cons_cons q r L ih ih_cons =>
      have htail : (r :: L).IsChain fun a b =>
          orientedHead src dst a = orientedTail src dst b := hchain.tail
      have htailne : r :: L ≠ [] := by simp
      obtain ⟨k, hk⟩ := ih_cons r htail htailne
      have hqr : orientedHead src dst q = orientedTail src dst r := hchain.rel
      have hlast : (q :: r :: L).getLast hne =
          (r :: L).getLast htailne := by simp
      simp only [List.head_cons] at hk
      rw [← hlast] at hk
      refine ⟨(if orientedTail src dst r = v then 1 else 0) + k, ?_⟩
      change
        ((if orientedTail src dst q = v then 1 else 0) +
          (if orientedHead src dst q = v then 1 else 0)) +
            incidenceCount (src := src) (dst := dst) (r :: L) v = _
      rw [hk]
      simp only [List.head_cons]
      rw [hqr]
      split_ifs <;> simp_all <;> omega

theorem incidenceCount_even_of_closed [DecidableEq ι]
    (T : IndexedTrail src dst) (hclosed : T.IsClosed) (v : ι) :
    Even (incidenceCount (src := src) (dst := dst) T.steps v) := by
  by_cases hne : T.steps = []
  · simp [hne, incidenceCount]
  · obtain ⟨k, hk⟩ := incidenceCount_eq_endpoints_add_twice
      T.steps T.adjacent hne v
    have hend := hclosed hne
    by_cases hv : orientedTail src dst (T.steps.head hne) = v
    · rw [hk, if_pos hv, if_pos (hend ▸ hv)]
      exact ⟨k + 1, by omega⟩
    · rw [hk, if_neg hv, if_neg (fun h => hv (hend.trans h))]
      exact ⟨k, by omega⟩

theorem incidenceCount_odd_at_finish [DecidableEq ι]
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hopen : orientedTail src dst (T.steps.head hne) ≠
      orientedHead src dst (T.steps.getLast hne)) :
    Odd (incidenceCount (src := src) (dst := dst) T.steps
      (orientedHead src dst (T.steps.getLast hne))) := by
  let v := orientedHead src dst (T.steps.getLast hne)
  obtain ⟨k, hk⟩ := incidenceCount_eq_endpoints_add_twice
    T.steps T.adjacent hne v
  have hstart : orientedTail src dst (T.steps.head hne) ≠ v := hopen
  have hfinish : orientedHead src dst (T.steps.getLast hne) = v := rfl
  rw [hk, if_neg hstart, if_pos hfinish]
  exact ⟨k, by omega⟩

/-- Extend a nonempty indexed trail by one fresh oriented occurrence. -/
def snoc [DecidableEq ε] (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (q : OrientedIndexedEdge ε)
    (hjoin : orientedHead src dst (T.steps.getLast hne) =
      orientedTail src dst q)
    (hfresh : q.1 ∉ T.steps.map Prod.fst) : IndexedTrail src dst where
  steps := T.steps ++ [q]
  adjacent := by
    apply T.adjacent.append (.singleton q)
    intro x hx y hy
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx
    simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
    subst x
    subst y
    exact hjoin
  edge_nodup := by
    simpa using T.edge_nodup.append (by simp) (by simpa using hfresh)

@[simp] theorem snoc_steps [DecidableEq ε] (T : IndexedTrail src dst)
    (hne : T.steps ≠ []) (q : OrientedIndexedEdge ε)
    (hjoin : orientedHead src dst (T.steps.getLast hne) = orientedTail src dst q)
    (hfresh : q.1 ∉ T.steps.map Prod.fst) :
    (T.snoc hne q hjoin hfresh).steps = T.steps ++ [q] := rfl

/-- If the two ends of a finite indexed trail differ in an even-degree graph,
the terminal endpoint has a fresh incident edge and the trail extends. -/
theorem exists_strict_extension_of_not_closed
    [Fintype ε] [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (heven : ∀ v, Even (graphDegree src dst v))
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hopen : orientedTail src dst (T.steps.head hne) ≠
      orientedHead src dst (T.steps.getLast hne)) :
    ∃ T' : IndexedTrail src dst, T.steps.length < T'.steps.length := by
  let v := orientedHead src dst (T.steps.getLast hne)
  have hodd : Odd (incidenceCount (src := src) (dst := dst) T.steps v) :=
    incidenceCount_odd_at_finish T hne hopen
  have hunused : ∃ e : ε,
      (src e = v ∨ dst e = v) ∧ e ∉ T.steps.map Prod.fst := by
    by_contra hnot
    push Not at hnot
    have hused : ∀ e : ε, src e = v ∨ dst e = v →
        e ∈ T.steps.map Prod.fst := by
      intro e hinc
      exact hnot e hinc
    have heq := incidenceCount_eq_graphDegree_of_incident_used T v hused
    rcases hodd with ⟨a, ha⟩
    rcases heven v with ⟨b, hb⟩
    omega
  obtain ⟨e, hinc, hfresh⟩ := hunused
  let q := orientFrom src dst e v
  have htail : orientedTail src dst q = v :=
    orientedTail_orientFrom src dst e v hinc
  have hqfresh : q.1 ∉ T.steps.map Prod.fst := by
    simpa [q] using hfresh
  let T' := T.snoc hne q (by simpa [v, htail]) hqfresh
  refine ⟨T', ?_⟩
  simp [T']

/-- Finite indexed trails have a global maximum by length.  The bound uses
the injective edge projection rather than the doubled oriented-edge type. -/
theorem exists_length_maximal [Fintype ε] [DecidableEq ε] [Nonempty ε]
    (src dst : ε → ι) :
    ∃ T : IndexedTrail src dst,
      T.steps ≠ [] ∧
      ∀ K : IndexedTrail src dst, K.steps.length ≤ T.steps.length := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ T : IndexedTrail src dst, T.steps.length = n
  have hcard : 1 ≤ Fintype.card ε := by
    exact Fintype.card_pos_iff.mpr inferInstance
  let e : ε := Classical.choice (inferInstance : Nonempty ε)
  have hPone : P 1 := by
    refine ⟨singleton src dst (e, false), ?_⟩
    simp
  let m := Nat.findGreatest P (Fintype.card ε)
  have hPm : P m := Nat.findGreatest_spec hcard hPone
  obtain ⟨T, hlength⟩ := hPm
  have hmpos : 1 ≤ m := Nat.le_findGreatest hcard hPone
  have hne : T.steps ≠ [] := by
    intro hempty
    rw [hempty] at hlength
    simp at hlength
    omega
  refine ⟨T, hne, ?_⟩
  intro K
  rw [hlength]
  by_contra hnot
  have hlt : m < K.steps.length := by omega
  have hbound : K.steps.length ≤ Fintype.card ε := K.length_le_card
  exact (Nat.findGreatest_is_greatest (P := P) hlt hbound)
    ⟨K, rfl⟩

/-- A globally longest trail in an even-degree indexed multigraph is closed. -/
theorem length_maximal_isClosed
    [Fintype ε] [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (heven : ∀ v, Even (graphDegree src dst v))
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hmax : ∀ K : IndexedTrail src dst,
      K.steps.length ≤ T.steps.length) :
    T.IsClosed := by
  by_contra hnot
  unfold IsClosed at hnot
  push Not at hnot
  obtain ⟨hne', hopen'⟩ := hnot
  have hopen : orientedTail src dst (T.steps.head hne) ≠
      orientedHead src dst (T.steps.getLast hne) := by
    simpa only using hopen'
  obtain ⟨T', hlong⟩ :=
    exists_strict_extension_of_not_closed src dst heven T hne hopen
  exact (Nat.not_lt_of_ge (hmax T')) hlong

private theorem isCyclicChain_of_isClosed
    (T : IndexedTrail src dst) (hclosed : T.IsClosed) :
    IsCyclicChain
      (fun a b => orientedHead src dst a = orientedTail src dst b) T.steps := by
  refine ⟨T.adjacent, ?_⟩
  intro x hx y hy
  obtain ⟨hne, hx⟩ := List.mem_getLast?_eq_getLast hx
  have hy' : y = T.steps.head hne := by
    exact (List.head_of_mem_head? hy).symm
  rw [hx, hy']
  exact (hclosed hne).symm

private theorem isClosed_of_isCyclicChain
    (L : List (OrientedIndexedEdge ε))
    (hcycle : IsCyclicChain
      (fun a b => orientedHead src dst a = orientedTail src dst b) L) :
    ∀ hne : L ≠ [],
      orientedTail src dst (L.head hne) =
        orientedHead src dst (L.getLast hne) := by
  intro hne
  exact (hcycle.2 _ (List.getLast_mem_getLast? hne)
    _ (List.head_mem_head? hne)).symm

/-- Rotate a nonempty closed trail so that a chosen occurrence is first.  This
is the exact list-level splice primitive used by Hierholzer's argument. -/
theorem exists_rotation_starting_with [DecidableEq ε]
    (T : IndexedTrail src dst) (hclosed : T.IsClosed)
    (q : OrientedIndexedEdge ε) (hq : q ∈ T.steps) :
    ∃ R : IndexedTrail src dst,
      ∃ hne : R.steps ≠ [],
        R.steps.head hne = q ∧
        R.steps.length = T.steps.length ∧
        R.IsClosed ∧
        ∀ e : ε, e ∈ R.steps.map Prod.fst ↔ e ∈ T.steps.map Prod.fst := by
  obtain ⟨A, B, hsplit⟩ := List.mem_iff_append.mp hq
  have hcyc : IsCyclicChain
      (fun a b => orientedHead src dst a = orientedTail src dst b)
      (A ++ q :: B) := by
    rw [← hsplit]
    exact isCyclicChain_of_isClosed T hclosed
  have hcycRot := cyclicChain_rotate_split A B q hcyc
  have hnodupOrig : ((A ++ q :: B).map Prod.fst).Nodup := by
    rw [← hsplit]
    exact T.edge_nodup
  have hnodupRot : (((q :: B) ++ A).map Prod.fst).Nodup := by
    simp only [List.map_append] at hnodupOrig ⊢
    exact List.nodup_append_comm.mp hnodupOrig
  let R : IndexedTrail src dst :=
    { steps := (q :: B) ++ A
      adjacent := hcycRot.1
      edge_nodup := hnodupRot }
  have hRne : R.steps ≠ [] := by simp [R]
  refine ⟨R, hRne, ?_, ?_, ?_, ?_⟩
  · simp [R]
  · rw [hsplit]
    simp [R, Nat.add_comm, Nat.add_assoc]
  · exact isClosed_of_isCyclicChain R.steps hcycRot
  · intro e
    simp only [R, List.map_append, List.map_cons, List.mem_append,
      List.mem_cons, hsplit]
    tauto

theorem visits_src_of_edge_mem (T : IndexedTrail src dst) (e : ε)
    (he : e ∈ T.steps.map Prod.fst) : T.Visits (src e) := by
  rcases List.mem_map.mp he with ⟨q, hq, hqe⟩
  rcases q with ⟨e', b⟩
  simp only at hqe
  subst e'
  cases b
  · exact ⟨(e, false), hq, Or.inl rfl⟩
  · exact ⟨(e, true), hq, Or.inr rfl⟩

theorem visits_dst_of_edge_mem (T : IndexedTrail src dst) (e : ε)
    (he : e ∈ T.steps.map Prod.fst) : T.Visits (dst e) := by
  rcases List.mem_map.mp he with ⟨q, hq, hqe⟩
  rcases q with ⟨e', b⟩
  simp only at hqe
  subst e'
  cases b
  · exact ⟨(e, false), hq, Or.inr rfl⟩
  · exact ⟨(e, true), hq, Or.inl rfl⟩

theorem visits_all_of_connected
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hconn : GraphConnected src dst)
    (hincident : ∀ v, T.Visits v → ∀ e,
      src e = v ∨ dst e = v → e ∈ T.steps.map Prod.fst) :
    ∀ v, T.Visits v := by
  let s := orientedTail src dst (T.steps.head hne)
  have hs : T.Visits s := by
    exact ⟨T.steps.head hne, List.head_mem hne, Or.inl rfl⟩
  have hstep : ∀ a b, graphAdjacent src dst a b →
      T.Visits a → T.Visits b := by
    intro a b hab hva
    rcases hab with ⟨e, h | h⟩
    · have he : e ∈ T.steps.map Prod.fst :=
        hincident a hva e (Or.inl h.1)
      simpa [h.2] using T.visits_dst_of_edge_mem e he
    · have he : e ∈ T.steps.map Prod.fst :=
        hincident a hva e (Or.inr h.2)
      simpa [h.1] using T.visits_src_of_edge_mem e he
  intro v
  induction hconn s v with
  | refl => exact hs
  | tail hab hbc ih => exact hstep _ _ hbc ih

theorem exists_unused_incident_visited_of_not_cover
    [DecidableEq ι] (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hconn : GraphConnected src dst) (hnot : ¬T.CoversEveryEdge) :
    ∃ v e, T.Visits v ∧ (src e = v ∨ dst e = v) ∧
      e ∉ T.steps.map Prod.fst := by
  unfold CoversEveryEdge at hnot
  push Not at hnot
  obtain ⟨e, he⟩ := hnot
  by_contra hnone
  push Not at hnone
  have hincident : ∀ v, T.Visits v → ∀ e,
      src e = v ∨ dst e = v → e ∈ T.steps.map Prod.fst := by
    intro v hv e' hinc
    exact hnone v e' hv hinc
  have hall := T.visits_all_of_connected hne hconn hincident
  exact he (hincident (src e) (hall (src e)) e (Or.inl rfl))

theorem exists_tail_step_of_visits
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hclosed : T.IsClosed) (v : ι) (hv : T.Visits v) :
    ∃ q ∈ T.steps, orientedTail src dst q = v := by
  rcases hv with ⟨q, hq, htail | hhead⟩
  · exact ⟨q, hq, htail⟩
  · obtain ⟨A, B, hsplit⟩ := List.mem_iff_append.mp hq
    cases B with
    | nil =>
        let first := T.steps.head hne
        have hfirst : first ∈ T.steps := List.head_mem hne
        have hlast : T.steps.getLast hne = q := by
          have hsne : A ++ [q] ≠ [] := by simp
          calc
            T.steps.getLast hne = (A ++ [q]).getLast hsne :=
              List.getLast_congr hne hsne hsplit
            _ = q := by simp
        refine ⟨first, hfirst, ?_⟩
        have hc := hclosed hne
        rw [hlast] at hc
        exact hc.trans hhead
    | cons r B =>
        have hsuf : (q :: r :: B).IsChain fun a b =>
            orientedHead src dst a = orientedTail src dst b := by
          have hall : (A ++ q :: r :: B).IsChain fun a b =>
              orientedHead src dst a = orientedTail src dst b := by
            rw [← hsplit]
            exact T.adjacent
          exact hall.right_of_append
        refine ⟨r, ?_, ?_⟩
        · rw [hsplit]
          simp
        · exact hsuf.rel ▸ hhead

/-- A closed globally longest trail in a connected graph covers every indexed
edge occurrence.  Otherwise connectivity finds a fresh edge at a visited
vertex; rotation followed by `snoc` makes a longer trail. -/
theorem length_maximal_coversEveryEdge
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (T : IndexedTrail src dst) (hne : T.steps ≠ [])
    (hclosed : T.IsClosed)
    (hmax : ∀ K : IndexedTrail src dst,
      K.steps.length ≤ T.steps.length) :
    T.CoversEveryEdge := by
  by_contra hnot
  obtain ⟨v, e, hv, hinc, hfresh⟩ :=
    T.exists_unused_incident_visited_of_not_cover hne hconn hnot
  obtain ⟨q₀, hq₀, htail₀⟩ :=
    T.exists_tail_step_of_visits hne hclosed v hv
  obtain ⟨R, hRne, hRhead, hRlength, hRclosed, hRmem⟩ :=
    T.exists_rotation_starting_with hclosed q₀ hq₀
  let q := orientFrom src dst e v
  have hqtail : orientedTail src dst q = v :=
    orientedTail_orientFrom src dst e v hinc
  have hqfresh : q.1 ∉ R.steps.map Prod.fst := by
    intro heR
    have heT : e ∈ T.steps.map Prod.fst := (hRmem e).mp (by simpa [q] using heR)
    exact hfresh heT
  have hRend : orientedHead src dst (R.steps.getLast hRne) = v := by
    have hc := hRclosed hRne
    rw [hRhead] at hc
    exact hc.symm.trans htail₀
  let K := R.snoc hRne q (hRend.trans hqtail.symm) hqfresh
  have hlong : T.steps.length < K.steps.length := by
    simp [K, hRlength]
  exact (Nat.not_lt_of_ge (hmax K)) hlong

/-- Nonempty connected finite indexed multigraphs of even degree possess a
closed trail that uses every edge index exactly once. -/
theorem exists_nonempty_indexed_euler_trail
    [Fintype ε] [DecidableEq ι] [DecidableEq ε] [Nonempty ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) :
    ∃ T : IndexedTrail src dst,
      T.steps ≠ [] ∧ T.IsEulerCircuit := by
  obtain ⟨T, hne, hmax⟩ := exists_length_maximal src dst
  have hclosed := length_maximal_isClosed src dst heven T hne hmax
  have hcovers := length_maximal_coversEveryEdge src dst hconn T hne hclosed hmax
  exact ⟨T, hne, hclosed, hcovers⟩

end IndexedTrail

/-- Fully packaged Euler-circuit witness.  The underlying list carries
adjacency and no-duplication; `covers` makes its edge projection an exact
permutation of the finite edge-index type.  Empty graphs use the supplied
inhabited vertex as their closed endpoint. -/
structure IndexedEulerCircuit {ι ε : Type*} (src dst : ε → ι) where
  anchor : ι
  trail : IndexedTrail src dst
  begins_at : ∀ hne : trail.steps ≠ [],
    orientedTail src dst (trail.steps.head hne) = anchor
  ends_at : ∀ hne : trail.steps ≠ [],
    orientedHead src dst (trail.steps.getLast hne) = anchor
  covers : trail.CoversEveryEdge

namespace IndexedEulerCircuit

variable {ι ε : Type*} {src dst : ε → ι}

theorem edgeProjection_toFinset_eq_univ [Fintype ε] [DecidableEq ε]
    (C : IndexedEulerCircuit src dst) :
    (C.trail.steps.map Prod.fst).toFinset = Finset.univ := by
  ext e
  constructor
  · intro _
    exact Finset.mem_univ e
  · intro _
    exact List.mem_toFinset.mpr (C.covers e)

theorem edgeProjection_perm_univ_toList [Fintype ε] [DecidableEq ε]
    (C : IndexedEulerCircuit src dst) :
    (C.trail.steps.map Prod.fst).Perm (Finset.univ : Finset ε).toList := by
  have hp := (List.toFinset_toList C.trail.edge_nodup).symm
  rw [C.edgeProjection_toFinset_eq_univ] at hp
  exact hp

theorem edgeProjection_length_eq_card [Fintype ε] [DecidableEq ε]
    (C : IndexedEulerCircuit src dst) :
    C.trail.steps.length = Fintype.card ε := by
  calc
    C.trail.steps.length = (C.trail.steps.map Prod.fst).length := by simp
    _ = (C.trail.steps.map Prod.fst).toFinset.card :=
      (List.toFinset_card_of_nodup C.trail.edge_nodup).symm
    _ = Finset.univ.card := by rw [C.edgeProjection_toFinset_eq_univ]
    _ = Fintype.card ε := Finset.card_univ

end IndexedEulerCircuit

/-- Euler's circuit theorem for arbitrary finite indexed multigraphs.  The
vertex type is inhabited only to name the endpoint of the empty circuit. -/
theorem exists_indexed_euler_circuit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε] [Nonempty ι]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) :
    Nonempty (IndexedEulerCircuit src dst) := by
  classical
  rcases isEmpty_or_nonempty ε with hε | hε
  · letI : IsEmpty ε := hε
    let T : IndexedTrail src dst :=
      { steps := []
        adjacent := .nil
        edge_nodup := by simp }
    let v₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    refine ⟨{
      anchor := v₀
      trail := T
      begins_at := ?_
      ends_at := ?_
      covers := ?_ }⟩
    · intro hne
      exact (hne (by simp [T])).elim
    · intro hne
      exact (hne (by simp [T])).elim
    · intro e
      exact isEmptyElim e
  · letI : Nonempty ε := hε
    obtain ⟨T, hne, hclosed, hcover⟩ :=
      IndexedTrail.exists_nonempty_indexed_euler_trail src dst hconn heven
    let v₀ := orientedTail src dst (T.steps.head hne)
    refine ⟨{
      anchor := v₀
      trail := T
      begins_at := ?_
      ends_at := ?_
      covers := hcover }⟩
    · intro hne'
      simpa only [v₀]
    · intro hne'
      have hc := hclosed hne'
      exact hc.symm

/-- Positive degree at a designated endpoint yields a nonempty packaged
Euler circuit, without requiring a separate `Nonempty ι` instance. -/
theorem exists_nonempty_indexed_euler_circuit_of_positive_degree
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v))
    (v : ι) (hpositive : 0 < graphDegree src dst v) :
    ∃ C : IndexedEulerCircuit src dst, C.trail.steps ≠ [] := by
  have hedge : Nonempty ε := by
    by_contra hempty
    haveI : IsEmpty ε := ⟨fun e => hempty ⟨e⟩⟩
    have hz : graphDegree src dst v = 0 := by simp [graphDegree]
    omega
  letI : Nonempty ε := hedge
  obtain ⟨T, hne, hclosed, hcover⟩ :=
    IndexedTrail.exists_nonempty_indexed_euler_trail src dst hconn heven
  let v₀ := orientedTail src dst (T.steps.head hne)
  refine ⟨{
    anchor := v₀
    trail := T
    begins_at := ?_
    ends_at := ?_
    covers := hcover }, hne⟩
  · intro hne'
    simpa only [v₀]
  · intro hne'
    exact (hclosed hne').symm

#print axioms IndexedTrail.incidenceCount_eq_endpoints_add_twice
#print axioms IndexedTrail.exists_strict_extension_of_not_closed
#print axioms IndexedTrail.length_maximal_coversEveryEdge
#print axioms exists_indexed_euler_circuit
#print axioms exists_nonempty_indexed_euler_circuit_of_positive_degree

end Problem56
