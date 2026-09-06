import Problem56.GraphOperatorL2

/-!
Kernel-clean combinatorial infrastructure for the adjacent endpoint-aware
rank-cut factorization.  This module deliberately keeps the carried and
entering coordinates indexed by actual edges, so parallel edges and unequal
vertex dimensions are preserved.
-/

open scoped BigOperators Matrix

namespace Problem56

/-- In an admissible source-to-sink DAG, the source is the unique vertex on
rank level zero. -/
theorem MingoAdmissibleDAG.mingoDAGRank_eq_zero_iff
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) (v : ι) :
    mingoDAGRank src dst v = 0 ↔ v = input := by
  constructor
  · intro hv
    by_contra hvi
    have hlt : mingoDAGRank src dst input < mingoDAGRank src dst v := by
      apply finiteDAGRank_lt_of_transGen (directedAdjacent src dst) hdag.1
      rcases hdag.2.1 v with h | h
      · exact (hvi h).elim
      · exact h
    rw [hdag.input_rank_eq_zero src dst input output, hv] at hlt
    omega
  · intro hv
    subst v
    exact hdag.input_rank_eq_zero src dst input output

/-- At the first cut, the processed-label assignment is just the source
coordinate.  The dependent equivalence remains valid for arbitrary source
dimension. -/
noncomputable def mingoProcessedLabelsOneEquiv
    {ι ε : Type*} [Fintype ι]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    RankCutProcessedLabels dim (mingoDAGRank src dst) 1 ≃ Fin (dim input) := by
  classical
  let rank := mingoDAGRank src dst
  have hinput : input ∈ rankProcessedVertices rank 1 := by
    simp only [mem_rankProcessedVertices, rank]
    rw [hdag.input_rank_eq_zero src dst input output]
    omega
  let base : {v // v ∈ rankProcessedVertices rank 1} := ⟨input, hinput⟩
  have hsub : Subsingleton {v // v ∈ rankProcessedVertices rank 1} := by
    constructor
    intro u v
    apply Subtype.ext
    have hu0 : rank u.1 = 0 := by
      have hu := (mem_rankProcessedVertices rank 1 u.1).1 u.2
      omega
    have hv0 : rank v.1 = 0 := by
      have hv := (mem_rankProcessedVertices rank 1 v.1).1 v.2
      omega
    have hu : u.1 = input :=
      (hdag.mingoDAGRank_eq_zero_iff src dst input output u.1).1 hu0
    have hv : v.1 = input :=
      (hdag.mingoDAGRank_eq_zero_iff src dst input output v.1).1 hv0
    exact hu.trans hv.symm
  exact piSubsingletonEquiv
    (fun v ↦ Fin (dim v.1)) base hsub

/-- An edge entering at rank zero is genuinely an edge out of the source.
This statement retains the edge identifier and therefore does not collapse
parallel edges. -/
theorem MingoAdmissibleDAG.src_eq_input_of_mem_rankEnteringEdges_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {e : ε}
    (he : e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0) :
    src e = input := by
  apply (hdag.mingoDAGRank_eq_zero_iff src dst input output (src e)).1
  exact (mem_rankEnteringEdges (mingoDAGRank src dst) src 0 e).1 he

/-- No edge can be completed after the first rank step. -/
theorem rankCompletedEdges_one_eq_empty
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) :
    rankCompletedEdges rank dst 1 = ∅ := by
  classical
  ext e
  simp only [mem_rankCompletedEdges, Finset.notMem_empty, iff_false]
  exact fun hdst ↦ by have := hedge e; omega

/-- The first active cut consists exactly of edges entering at level zero. -/
theorem rankActiveEdges_one_eq_entering_zero
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) :
    rankActiveEdges rank src dst 1 = rankEnteringEdges rank src 0 := by
  classical
  ext e
  simp only [mem_rankActiveEdges, mem_rankEnteringEdges]
  constructor
  · rintro ⟨hsrc, _⟩
    omega
  · intro hsrc
    have hdst := hedge e
    omega

/-- Type-level reindexing of the first active cut by its entering edges. -/
def rankActiveEdgesOneEquivEnteringZero
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) :
    {e // e ∈ rankActiveEdges rank src dst 1} ≃
      {e // e ∈ rankEnteringEdges rank src 0} where
  toFun e := ⟨e.1, by
    rw [← rankActiveEdges_one_eq_entering_zero rank src dst hedge]
    exact e.2⟩
  invFun e := ⟨e.1, by
    rw [rankActiveEdges_one_eq_entering_zero rank src dst hedge]
    exact e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- Completed edges at an adjacent cut split into the already-completed edges
and the edges whose target lies on the current level. -/
theorem rankCompletedEdges_succ
    {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) :
    rankCompletedEdges rank dst (k + 1) =
      rankCompletedEdges rank dst k ∪ rankLeavingEdges rank dst k := by
  classical
  ext e
  simp only [mem_rankCompletedEdges, Finset.mem_union, mem_rankLeavingEdges]
  omega

theorem rankCompletedEdges_disjoint_leaving
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) :
    Disjoint (rankCompletedEdges rank dst k)
      (rankLeavingEdges rank dst k) := by
  classical
  rw [Finset.disjoint_left]
  intro e hcompleted hleaving
  simp only [mem_rankCompletedEdges] at hcompleted
  simp only [mem_rankLeavingEdges] at hleaving
  omega

/-- Expand the edge-list action using the actual entering-edge subtype rather
than list positions. -/
theorem edgeListAction_rankEntering_eq_sum_prod
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (k : ℕ)
    (f : EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList rank src k) → ℝ)
    (y : EdgeListTuple (fun e ↦ dim (dst e))
      (rankEnteringEdgeList rank src k)) :
    edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList rank src k) f y =
      ∑ xs, f xs *
        ∏ e : {e // e ∈ rankEnteringEdges rank src k},
          M e.1
            ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
            ((rankEnteringEdgeTupleEquiv dim rank src dst k y) e) := by
  classical
  rw [edgeListAction_eq_sum_prod_subtype _ _ _ _
    (rankEnteringEdgeList_nodup rank src k)]
  apply Finset.sum_congr rfl
  intro xs _
  congr 1
  apply Fintype.prod_equiv
    (rankEnteringEdgeListSubtypeEquiv rank src k)
  intro e
  rfl

/-- The target coordinate extracted by `post` is exactly the corresponding
new-cut edge port. -/
theorem endpointAwareSuccBoundaryPost_entering_apply
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (e : {e // e ∈ rankEnteringEdges rank src k}) :
    (rankEnteringEdgeTupleEquiv dim rank src dst k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).2) e =
      boundary ⟨RankCutPort.edge e.1, by
        simp only [rankCutPortActive]
        have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
        have hlt := hedge e.1
        omega⟩ := by
  simp only [endpointAwareSuccBoundaryPost, Equiv.apply_symm_apply,
    endpointAwareSuccBoundaryToEntering]
  congr 1

/-- Reconstruct a new-cut boundary from its stable carried ports and the
target coordinates of the entering edges. -/
noncomputable def endpointAwareSuccBoundaryOfPost
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (_hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (dst e))
        (rankEnteringEdgeList rank src k)) :
    EndpointAwareRankCutIndex dim rank src dst input output (k + 1) := by
  classical
  intro p
  rcases p with ⟨p, hp⟩
  cases p with
  | input =>
      simp only [rankCutPortActive] at hp
      omega
  | output =>
      exact q.1 ⟨RankCutPort.output, hp⟩
  | edge e =>
      by_cases he : rank (src e) = k
      · exact (rankEnteringEdgeTupleEquiv dim rank src dst k q.2)
          ⟨e, by simpa only [mem_rankEnteringEdges] using he⟩
      · exact q.1 ⟨RankCutPort.edge e, by
          refine ⟨hp, ?_⟩
          simp only [rankCutPortActive] at hp
          omega⟩

/-- Reconstruction is a left inverse of the concrete post map. -/
theorem endpointAwareSuccBoundaryOfPost_post
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hinput : rank input = 0)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
    endpointAwareSuccBoundaryOfPost dim rank src dst hedge input output k
        hinput (endpointAwareSuccBoundaryPost dim rank src dst hedge
          input output k boundary) = boundary := by
  classical
  funext p
  rcases p with ⟨p, hp⟩
  cases p with
  | input =>
      simp only [rankCutPortActive] at hp
      omega
  | output =>
      rfl
  | edge e =>
      by_cases he : rank (src e) = k
      · simp only [endpointAwareSuccBoundaryOfPost, he, ↓reduceDIte,
          endpointAwareSuccBoundaryPost, Equiv.apply_symm_apply,
          endpointAwareSuccBoundaryToEntering]
      · simp only [endpointAwareSuccBoundaryOfPost, he, ↓reduceDIte,
          endpointAwareSuccBoundaryPost, endpointAwareSuccBoundaryToCarried]

/-- The concrete post map is also recovered after reconstructing its two
factors. -/
theorem endpointAwareSuccBoundaryPost_ofPost
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (dst e))
        (rankEnteringEdgeList rank src k)) :
    endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        (endpointAwareSuccBoundaryOfPost dim rank src dst hedge input output k
          hinput q) = q := by
  classical
  apply Prod.ext
  · funext p
    rcases p with ⟨p, hp⟩
    cases p with
    | input =>
        have hactive :=
          rankCutCarriedPortActive.active rank src dst input output k hp
        simp only [rankCutPortActive] at hactive
        omega
    | output =>
        rfl
    | edge e =>
        have he : rank (src e) ≠ k := by
          exact ne_of_lt hp.2
        simp only [endpointAwareSuccBoundaryPost,
          endpointAwareSuccBoundaryToCarried,
          endpointAwareSuccBoundaryOfPost, he, ↓reduceDIte]
  · apply (rankEnteringEdgeTupleEquiv dim rank src dst k).injective
    funext e
    have he : rank (src e.1) = k :=
      (mem_rankEnteringEdges rank src k e.1).1 e.2
    simp only [endpointAwareSuccBoundaryPost, Equiv.apply_symm_apply,
      endpointAwareSuccBoundaryToEntering, endpointAwareSuccBoundaryOfPost,
      he, ↓reduceDIte]

/-- The new endpoint-aware cut is exactly the product of stable carried ports
and entering-edge target coordinates. -/
noncomputable def endpointAwareSuccBoundaryEquiv
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hinput : rank input = 0) :
    EndpointAwareRankCutIndex dim rank src dst input output (k + 1) ≃
      EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
        EdgeListTuple (fun e ↦ dim (dst e))
          (rankEnteringEdgeList rank src k) where
  toFun := endpointAwareSuccBoundaryPost dim rank src dst hedge
    input output k
  invFun := endpointAwareSuccBoundaryOfPost dim rank src dst hedge
    input output k hinput
  left_inv := endpointAwareSuccBoundaryOfPost_post dim rank src dst hedge
    input output k hinput
  right_inv := endpointAwareSuccBoundaryPost_ofPost dim rank src dst hedge
    input output k hinput

/-- A type-level version of the completed-edge successor partition, suitable
for exact `Fintype.prod_equiv` reindexing. -/
noncomputable def rankCompletedEdgesSuccEquiv
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) :
    {e // e ∈ rankCompletedEdges rank dst (k + 1)} ≃
      Sum {e // e ∈ rankCompletedEdges rank dst k}
        {e // e ∈ rankLeavingEdges rank dst k} := by
  classical
  refine
    { toFun := fun e ↦ if h : rank (dst e.1) < k then
          Sum.inl ⟨e.1, by simpa only [mem_rankCompletedEdges] using h⟩
        else
          Sum.inr ⟨e.1, by
            rw [mem_rankLeavingEdges]
            have he := (mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2
            omega⟩
      invFun := fun e ↦ match e with
        | Sum.inl e => ⟨e.1, by
            rw [mem_rankCompletedEdges]
            have he := (mem_rankCompletedEdges rank dst k e.1).1 e.2
            omega⟩
        | Sum.inr e => ⟨e.1, by
            rw [mem_rankCompletedEdges]
            have he := (mem_rankLeavingEdges rank dst k e.1).1 e.2
            omega⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases h : rank (dst e.1) < k
    · simp only [h, ↓reduceDIte]
    · simp only [h, ↓reduceDIte]
  · intro e
    cases e with
    | inl e =>
        have h : rank (dst e.1) < k :=
          (mem_rankCompletedEdges rank dst k e.1).1 e.2
        simp only [h, ↓reduceDIte]
    | inr e =>
        have h : ¬rank (dst e.1) < k := by
          have he := (mem_rankLeavingEdges rank dst k e.1).1 e.2
          omega
        simp only [h, ↓reduceDIte]

/-- A concrete edge port at the first new cut for each level-zero entering
edge. -/
def rankEnteringZeroNewPort
    {ι ε : Type*} [Fintype ε]
    (_dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι)
    (e : {e // e ∈ rankEnteringEdges rank src 0}) :
    {p // rankCutPortActive rank src dst input output 1 p} :=
  ⟨RankCutPort.edge e.1, by
    simp only [rankCutPortActive]
    have he := (mem_rankEnteringEdges rank src 0 e.1).1 e.2
    have hlt := hedge e.1
    omega⟩

set_option maxHeartbeats 800000 in
/-- First-step endpoint-aware state, normalized to one source-label sum.  In
particular, the product is over actual entering edges; unequal target
dimensions and indexed parallel edges are retained exactly. -/
theorem endpointAwareRankCutState_one_eq_entering_sum
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim (mingoDAGRank src dst)
      src dst input output 1) :
    endpointAwareRankCutState dim (mingoDAGRank src dst) src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output 1 x boundary =
      ∑ a : Fin (dim input), x a *
        ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
          M e.1
            (Fin.cast (congrArg dim
              (hdag.src_eq_input_of_mem_rankEnteringEdges_zero
                src dst input output e.2).symm) a)
            (boundary (rankEnteringZeroNewPort dim (mingoDAGRank src dst)
              src dst (fun e ↦ hdag.edge_rank_lt src dst input output e)
              input output e)) := by
  classical
  let rank := mingoDAGRank src dst
  let hedge : ∀ e, rank (src e) < rank (dst e) :=
    fun e ↦ hdag.edge_rank_lt src dst input output e
  have hinput : rank input = 0 := hdag.input_rank_eq_zero src dst input output
  have houtput0 : rank output ≠ 0 := by
    intro hout
    exact hio ((hdag.mingoDAGRank_eq_zero_iff src dst input output output).1 hout).symm
  have hcompleted : IsEmpty {e // e ∈ rankCompletedEdges rank dst 1} := by
    rw [rankCompletedEdges_one_eq_empty rank src dst hedge]
    infer_instance
  let _ : IsEmpty {e // e ∈ rankCompletedEdges rank dst 1} := hcompleted
  rw [endpointAwareRankCutState]
  apply Fintype.sum_equiv
    (mingoProcessedLabelsOneEquiv dim src dst input output hdag)
  intro labels
  have hi : rank input < 1 := by omega
  have ho : ¬rank output < 1 := by omega
  have hi' : mingoDAGRank src dst input < 1 := by
    simpa only [rank] using hi
  have ho' : ¬mingoDAGRank src dst output < 1 := by
    simpa only [rank] using ho
  simp only [hi', ho', ↓reduceDIte, Fintype.prod_empty]
  have hlabel_input :
      labels ⟨input, by simpa only [mem_rankProcessedVertices] using hi⟩ =
        mingoProcessedLabelsOneEquiv dim src dst input output hdag labels := by
    rfl
  rw [hlabel_input]
  have hprod :
      (∏ e : {e // e ∈ rankActiveEdges rank src dst 1},
          M e.1
            (labels ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact ((mem_rankActiveEdges rank src dst 1 e.1).1 e.2).1⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)) =
        ∏ e : {e // e ∈ rankEnteringEdges rank src 0},
          M e.1
            (Fin.cast (congrArg dim
              (hdag.src_eq_input_of_mem_rankEnteringEdges_zero
                src dst input output e.2).symm)
              (mingoProcessedLabelsOneEquiv dim src dst input output hdag labels))
            (boundary (rankEnteringZeroNewPort dim rank src dst hedge
              input output e)) := by
    apply Fintype.prod_equiv
      (rankActiveEdgesOneEquivEnteringZero rank src dst hedge)
    intro e
    let ee := rankActiveEdgesOneEquivEnteringZero rank src dst hedge e
    have hesrc : src ee.1 = input :=
      hdag.src_eq_input_of_mem_rankEnteringEdges_zero
        src dst input output ee.2
    change M e.1 _ _ = M e.1 _ _
    apply congrArg₂ (M e.1)
    · have hsrcProcessed : src e.1 ∈ rankProcessedVertices rank 1 := by
        rw [mem_rankProcessedVertices]
        exact ((mem_rankActiveEdges rank src dst 1 e.1).1 e.2).1
      have hsub :
          (⟨src e.1, hsrcProcessed⟩ :
              {v // v ∈ rankProcessedVertices rank 1}) =
            ⟨input, by simpa only [mem_rankProcessedVertices] using hi⟩ :=
        Subtype.ext hesrc
      cases hsub
      rfl
    · rfl
  rw [hprod]
  ring

/-- The source tuple obtained by assigning one source coordinate to every
rank-zero entering edge.  Each edge occurrence receives its own (possibly
differently transported) coordinate. -/
noncomputable def rankEnteringZeroSourceTuple
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (a : Fin (dim input)) :
    EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList (mingoDAGRank src dst) src 0) :=
  (rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst) src src 0).symm
    (fun e ↦ Fin.cast (congrArg dim
      (hdag.src_eq_input_of_mem_rankEnteringEdges_zero
        src dst input output e.2).symm) a)

@[simp]
theorem rankEnteringZeroSourceTuple_apply
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (a : Fin (dim input))
    (e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0}) :
    (rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst) src src 0
      (rankEnteringZeroSourceTuple dim src dst input output hdag a)) e =
      Fin.cast (congrArg dim
        (hdag.src_eq_input_of_mem_rankEnteringEdges_zero
          src dst input output e.2).symm) a := by
  simp only [rankEnteringZeroSourceTuple, Equiv.apply_symm_apply]

theorem MingoAdmissibleDAG.input_mem_rankLevelVertices_zero
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    input ∈ rankLevelVertices (mingoDAGRank src dst) 0 := by
  rw [mem_rankLevelVertices]
  exact hdag.input_rank_eq_zero src dst input output

/-- The common level label read from a constant rank-zero source tuple is the
coordinate used to build that tuple. -/
theorem endpointAwareRankCutStepLevelLabel_zero_sourceTuple
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (c : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
      src dst input output 0)
    (a : Fin (dim input)) :
    endpointAwareRankCutStepLevelLabel dim (mingoDAGRank src dst) src dst
        input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
        (c, rankEnteringZeroSourceTuple dim src dst input output hdag a)
        ⟨input, hdag.input_mem_rankLevelVertices_zero src dst input output⟩ = a := by
  classical
  simp only [endpointAwareRankCutStepLevelLabel, hio, ↓reduceDIte]
  rw [rankEnteringZeroSourceTuple_apply]
  simp

/-- A constant source tuple lies on the consistency diagonal, including when
several distinct entering edges share the source vertex. -/
theorem endpointAwareRankCutStepConsistent_zero_sourceTuple
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (c : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
      src dst input output 0)
    (a : Fin (dim input)) :
    endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst) src dst
      input output hdag
      (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
      (c, rankEnteringZeroSourceTuple dim src dst input output hdag a) := by
  classical
  intro e
  rw [rankEnteringZeroSourceTuple_apply]
  have hesrc : src e.1 = input :=
    hdag.src_eq_input_of_mem_rankEnteringEdges_zero
      src dst input output e.2
  have hlevel : src e.1 ∈ rankLevelVertices (mingoDAGRank src dst) 0 := by
    rw [mem_rankLevelVertices]
    exact (mem_rankEnteringEdges (mingoDAGRank src dst) src 0 e.1).1 e.2
  have hsub :
      (⟨src e.1, hlevel⟩ :
          {v // v ∈ rankLevelVertices (mingoDAGRank src dst) 0}) =
        ⟨input, hdag.input_mem_rankLevelVertices_zero src dst input output⟩ :=
    Subtype.ext hesrc
  cases hsub
  rw [endpointAwareRankCutStepLevelLabel_zero_sourceTuple
    dim src dst (src e.1) output hdag hio c a]
  rfl

/-- For fixed carried coordinates, the consistent rank-zero source tuples are
equivalent to one source coordinate.  This is the finite diagonal, not a
nonlinear copying map. -/
noncomputable def endpointAwareConsistentSourceTupleZeroEquiv
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (c : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
      src dst input output 0) :
    {xs : EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList (mingoDAGRank src dst) src 0) //
      endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst) src dst
        input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 (c, xs)} ≃
      Fin (dim input) := by
  classical
  let hlevel := hdag.input_mem_rankLevelVertices_zero src dst input output
  let toCoordinate :
      {xs : EdgeListTuple (fun e ↦ dim (src e))
          (rankEnteringEdgeList (mingoDAGRank src dst) src 0) //
        endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst) src dst
          input output hdag
          (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 (c, xs)} →
        Fin (dim input) := fun q ↦
      endpointAwareRankCutStepLevelLabel dim (mingoDAGRank src dst) src dst
        input output hdag (fun e ↦ hdag.edge_rank_lt src dst input output e)
        0 (c, q.1) ⟨input, hlevel⟩
  refine
    { toFun := toCoordinate
      invFun := fun a ↦
        ⟨rankEnteringZeroSourceTuple dim src dst input output hdag a,
          endpointAwareRankCutStepConsistent_zero_sourceTuple
            dim src dst input output hdag hio c a⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    apply Subtype.ext
    apply (rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst) src src 0).injective
    funext e
    rw [rankEnteringZeroSourceTuple_apply]
    have hesrc : src e.1 = input :=
      hdag.src_eq_input_of_mem_rankEnteringEdges_zero
        src dst input output e.2
    have hlevelSrc : src e.1 ∈
        rankLevelVertices (mingoDAGRank src dst) 0 := by
      rw [mem_rankLevelVertices]
      exact (mem_rankEnteringEdges (mingoDAGRank src dst) src 0 e.1).1 e.2
    have hsub :
        (⟨src e.1, hlevelSrc⟩ :
            {v // v ∈ rankLevelVertices (mingoDAGRank src dst) 0}) =
          ⟨input, hlevel⟩ := Subtype.ext hesrc
    have hconsistent := q.2 e
    cases hsub
    simpa only [toCoordinate, Fin.cast_eq_self] using hconsistent.symm
  · intro a
    exact endpointAwareRankCutStepLevelLabel_zero_sourceTuple
      dim src dst input output hdag hio c a

/-- Rewrite a finitely supported dependent `if` sum as a subtype sum. -/
theorem sum_dite_eq_subtype {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (f : {a // P a} → ℝ) :
    (∑ a, if h : P a then f ⟨a, h⟩ else 0) = ∑ a : {a // P a}, f a := by
  classical
  let g : α → ℝ := fun a ↦ if h : P a then f ⟨a, h⟩ else 0
  calc
    (∑ a, if h : P a then f ⟨a, h⟩ else 0) = ∑ a, g a := rfl
    _ = ∑ a ∈ (Finset.univ.filter P), g a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P a <;> simp [g, ha]
    _ = ∑ a : {a // P a}, g a.1 := by
      exact Finset.sum_subtype _ (by simp) g
    _ = ∑ a : {a // P a}, f a := by
      apply Finset.sum_congr rfl
      intro a _
      simp [g, a.2]

/-- On the rank-zero consistency diagonal, the prepared coefficient is the
source vector evaluated at the common source label. -/
theorem endpointAwareRankCutStepPrepared_zero_of_consistent
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (x : Fin (dim input) → ℝ)
    (q : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
        src dst input output 0 ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList (mingoDAGRank src dst) src 0))
    (hq : endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst)
      src dst input output hdag
      (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 q) :
    endpointAwareRankCutStepPrepared dim (mingoDAGRank src dst) src dst M
        input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
        (hdag.input_rank_eq_zero src dst input output) x q =
      x (endpointAwareRankCutStepLevelLabel dim (mingoDAGRank src dst)
        src dst input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 q
        ⟨input, hdag.input_mem_rankLevelVertices_zero src dst input output⟩) := by
  classical
  simp only [endpointAwareRankCutStepPrepared, hq, ↓reduceDIte]
  rw [endpointAwareRankCutState_zero]
  congr 1

/-- Off the rank-zero consistency diagonal, the prepared coefficient
vanishes. -/
theorem endpointAwareRankCutStepPrepared_zero_of_not_consistent
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (x : Fin (dim input) → ℝ)
    (q : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
        src dst input output 0 ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList (mingoDAGRank src dst) src 0))
    (hq : ¬endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst)
      src dst input output hdag
      (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 q) :
    endpointAwareRankCutStepPrepared dim (mingoDAGRank src dst) src dst M
        input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
        (hdag.input_rank_eq_zero src dst input output) x q = 0 := by
  classical
  simp only [endpointAwareRankCutStepPrepared, hq, ↓reduceDIte]

set_option maxHeartbeats 800000 in
/-- Summing the prepared array against arbitrary entering-edge factors keeps
exactly the one-coordinate diagonal.  This is the first-step coefficient
identity before substituting the new boundary target coordinates. -/
theorem endpointAwarePrepared_zero_diagonal_sum
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (x : Fin (dim input) → ℝ)
    (c : EndpointAwareRankCutCarriedIndex dim (mingoDAGRank src dst)
      src dst input output 0)
    (y : RankEnteringEdgeIndex dim (mingoDAGRank src dst) src dst 0) :
    (∑ xs,
        endpointAwareRankCutStepPrepared dim (mingoDAGRank src dst) src dst M
            input output hdag
            (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
            (hdag.input_rank_eq_zero src dst input output) x (c, xs) *
          ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
            M e.1
              ((rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst)
                src src 0 xs) e) (y e)) =
      ∑ a : Fin (dim input), x a *
        ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
          M e.1
            (Fin.cast (congrArg dim
              (hdag.src_eq_input_of_mem_rankEnteringEdges_zero
                src dst input output e.2).symm) a)
            (y e) := by
  classical
  let P := fun xs : EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList (mingoDAGRank src dst) src 0) ↦
    endpointAwareRankCutStepConsistent dim (mingoDAGRank src dst) src dst
      input output hdag
      (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 (c, xs)
  let levelLabel := fun xs : EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList (mingoDAGRank src dst) src 0) ↦
    endpointAwareRankCutStepLevelLabel dim (mingoDAGRank src dst) src dst
      input output hdag
      (fun e ↦ hdag.edge_rank_lt src dst input output e) 0 (c, xs)
      ⟨input, hdag.input_mem_rankLevelVertices_zero src dst input output⟩
  have hrewrite :
      (∑ xs,
          endpointAwareRankCutStepPrepared dim (mingoDAGRank src dst) src dst M
              input output hdag
              (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
              (hdag.input_rank_eq_zero src dst input output) x (c, xs) *
            ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
              M e.1
                ((rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst)
                  src src 0 xs) e) (y e)) =
        ∑ xs, if hxs : P xs then
          x (levelLabel xs) *
            ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
              M e.1
                ((rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst)
                  src src 0 xs) e) (y e)
        else 0 := by
    apply Finset.sum_congr rfl
    intro xs _
    by_cases hxs : P xs
    · simp only [hxs, ↓reduceDIte]
      rw [endpointAwareRankCutStepPrepared_zero_of_consistent
        dim src dst M input output hdag x (c, xs) hxs]
    · simp only [hxs, ↓reduceDIte]
      rw [endpointAwareRankCutStepPrepared_zero_of_not_consistent
        dim src dst M input output hdag x (c, xs) hxs]
      simp
  rw [hrewrite]
  rw [sum_dite_eq_subtype P (fun q ↦
    x (levelLabel q.1) *
      ∏ e : {e // e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0},
        M e.1
          ((rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst)
            src src 0 q.1) e) (y e))]
  apply Fintype.sum_equiv
    (endpointAwareConsistentSourceTupleZeroEquiv
      dim src dst input output hdag hio c)
  intro q
  have hequiv :
      endpointAwareConsistentSourceTupleZeroEquiv
          dim src dst input output hdag hio c q = levelLabel q.1 := rfl
  rw [hequiv]
  congr 1
  apply Fintype.prod_congr
  intro e
  congr 1
  have hesrc : src e.1 = input :=
    hdag.src_eq_input_of_mem_rankEnteringEdges_zero
      src dst input output e.2
  have hlevelSrc : src e.1 ∈
      rankLevelVertices (mingoDAGRank src dst) 0 := by
    rw [mem_rankLevelVertices]
    exact (mem_rankEnteringEdges (mingoDAGRank src dst) src 0 e.1).1 e.2
  let hlevel := hdag.input_mem_rankLevelVertices_zero src dst input output
  have hsub :
      (⟨src e.1, hlevelSrc⟩ :
          {v // v ∈ rankLevelVertices (mingoDAGRank src dst) 0}) =
        ⟨input, hlevel⟩ := Subtype.ext hesrc
  have hconsistent := q.2 e
  cases hsub
  simpa only [levelLabel, Fin.cast_eq_self] using hconsistent

/-- For an arbitrary adjacent cut, expand the exact right-hand side of
`state_factor` into the finite source-coordinate sum.  All target coordinates
are rewritten back to the actual new boundary. -/
theorem endpointAwareRankCutStepAction_eq_expanded
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
    edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList rank src k)
        (fun xs ↦ endpointAwareRankCutStepPrepared dim rank src dst M
          input output hdag hedge k hinput x
          ((endpointAwareSuccBoundaryPost dim rank src dst hedge
            input output k boundary).1, xs))
        (endpointAwareSuccBoundaryPost dim rank src dst hedge
          input output k boundary).2 =
      ∑ xs,
        endpointAwareRankCutStepPrepared dim rank src dst M input output
            hdag hedge k hinput x
            ((endpointAwareSuccBoundaryPost dim rank src dst hedge
              input output k boundary).1, xs) *
          ∏ e : {e // e ∈ rankEnteringEdges rank src k},
            M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
              (boundary ⟨RankCutPort.edge e.1, by
                simp only [rankCutPortActive]
                have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                have hlt := hedge e.1
                omega⟩) := by
  classical
  rw [edgeListAction_rankEntering_eq_sum_prod]
  apply Finset.sum_congr rfl
  intro xs _
  congr 1
  apply Fintype.prod_congr
  intro e
  rw [endpointAwareSuccBoundaryPost_entering_apply]

/-- Assemble the full adjacent-cut certificate from the remaining explicit
coefficient identity.  The hypothesis displayed here is the exact general
`k` combinatorial goal: all carried/entering reconstruction and analytic
energy obligations have already been discharged. -/
noncomputable def endpointAwareRankCutStepFactorization_of_expanded_identity
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hio : input ≠ output)
    (x : Fin (dim input) → ℝ)
    (hcoefficient : ∀ boundary,
      endpointAwareRankCutState dim rank src dst M hedge input output (k + 1)
          x boundary =
        ∑ xs,
          endpointAwareRankCutStepPrepared dim rank src dst M input output
              hdag hedge k hinput x
              ((endpointAwareSuccBoundaryPost dim rank src dst hedge
                input output k boundary).1, xs) *
            ∏ e : {e // e ∈ rankEnteringEdges rank src k},
              M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
                (boundary ⟨RankCutPort.edge e.1, by
                  simp only [rankCutPortActive]
                  have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                  have hlt := hedge e.1
                  omega⟩)) :
    EndpointAwareRankCutStepFactorization dim rank src dst M hedge
      input output k x :=
  endpointAwareRankCutStepFactorization_of_state_factor dim rank src dst M
    input output hdag hedge k hinput hio x fun boundary ↦ by
      rw [endpointAwareRankCutStepAction_eq_expanded]
      exact hcoefficient boundary

set_option maxHeartbeats 800000 in
/-- The genuine adjacent-cut coefficient factorization at the first rank
step.  This simultaneously covers forks, indexed parallel entering edges,
and arbitrary unequal vertex dimensions. -/
theorem endpointAwareRankCutState_factor_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim (mingoDAGRank src dst)
      src dst input output 1) :
    endpointAwareRankCutState dim (mingoDAGRank src dst) src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output 1 x boundary =
      edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList (mingoDAGRank src dst) src 0)
        (fun xs ↦ endpointAwareRankCutStepPrepared dim
          (mingoDAGRank src dst) src dst M input output hdag
          (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
          (hdag.input_rank_eq_zero src dst input output) x
          ((endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
            (fun e ↦ hdag.edge_rank_lt src dst input output e)
            input output 0 boundary).1, xs))
        (endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
          (fun e ↦ hdag.edge_rank_lt src dst input output e)
          input output 0 boundary).2 := by
  classical
  rw [endpointAwareRankCutState_one_eq_entering_sum
    dim src dst M input output hdag hio x boundary]
  rw [edgeListAction_rankEntering_eq_sum_prod]
  rw [endpointAwarePrepared_zero_diagonal_sum
    dim src dst M input output hdag hio x
    (endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
      (fun e ↦ hdag.edge_rank_lt src dst input output e)
      input output 0 boundary).1
    (rankEnteringEdgeTupleEquiv dim (mingoDAGRank src dst) src dst 0
      (endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output 0 boundary).2)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Fintype.prod_congr
  intro e
  rw [endpointAwareSuccBoundaryPost_entering_apply]
  congr 1

/-- Concrete first-step certificate for the distinct-endpoint branch.  No
positivity hypothesis is needed at this step; hence this specializes directly
to the positive-dimension branch required by I04. -/
noncomputable def endpointAwareRankCutStepFactorization_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (x : Fin (dim input) → ℝ) :
    EndpointAwareRankCutStepFactorization dim (mingoDAGRank src dst)
      src dst M (fun e ↦ hdag.edge_rank_lt src dst input output e)
      input output 0 x :=
  endpointAwareRankCutStepFactorization_of_state_factor dim
    (mingoDAGRank src dst) src dst M input output hdag
    (fun e ↦ hdag.edge_rank_lt src dst input output e) 0
    (hdag.input_rank_eq_zero src dst input output) hio x
    (endpointAwareRankCutState_factor_zero
      dim src dst M input output hdag hio x)

/-- The analytic first-step contraction follows from the explicit coefficient
certificate above. -/
theorem endpointAwareRankCutEnergy_one_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output)
    (x : Fin (dim input) → ℝ) :
    endpointAwareRankCutEnergy dim (mingoDAGRank src dst) src dst
        input output 1
        (endpointAwareRankCutState dim (mingoDAGRank src dst) src dst M
          (fun e ↦ hdag.edge_rank_lt src dst input output e)
          input output 1 x) ≤
      (∏ e ∈ rankEnteringEdges (mingoDAGRank src dst) src 0,
          euclideanOperatorNorm (M e) ^ 2) *
        endpointAwareRankCutEnergy dim (mingoDAGRank src dst) src dst
          input output 0
          (endpointAwareRankCutState dim (mingoDAGRank src dst) src dst M
            (fun e ↦ hdag.edge_rank_lt src dst input output e)
            input output 0 x) := by
  simpa only [Nat.zero_add] using
    endpointAwareRankCutEnergy_succ_le_of_factorization dim
      (mingoDAGRank src dst) src dst M
      (fun e ↦ hdag.edge_rank_lt src dst input output e)
      input output 0 x
      (endpointAwareRankCutStepFactorization_zero
        dim src dst M input output hdag hio x)

end Problem56
