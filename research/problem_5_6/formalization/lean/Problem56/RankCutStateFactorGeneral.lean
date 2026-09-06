import Problem56.RankCutFactorization

/-!
General finite reindexing for the remaining adjacent rank-cut coefficient
identity.  The source coordinates of all edges entering at one rank level are
the diagonal image of one label per level vertex.  If the output lies on the
current level, its label is fixed by the newly active output port.
-/

open scoped BigOperators Matrix

namespace Problem56

/-- One label for every vertex on rank level `k`. -/
abbrev RankCutLevelLabels {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ) :=
  (v : {v // v ∈ rankLevelVertices rank k}) → Fin (dim v.1)

/-- Transporting the value of a dependent finite-coordinate assignment along
an equality of its base indices agrees with evaluating at the transported
subtype index. -/
theorem dependentFin_cast_apply
    {ι : Type*} (dim : ι → ℕ) (P : ι → Prop)
    (level : (v : {v // P v}) → Fin (dim v.1))
    {a b : ι} (ha : P a) (hb : P b) (h : a = b) :
    Fin.cast (congrArg dim h) (level ⟨a, ha⟩) = level ⟨b, hb⟩ := by
  subst b
  rfl

/-- If the output is processed at this step, its level label is fixed by the
new output port, which is part of the carried index. -/
def endpointAwareLevelLabelsOutputCompatible
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (level : RankCutLevelLabels dim rank k) : Prop :=
  ∀ hout : output ∈ rankLevelVertices rank k,
    level ⟨output, hout⟩ =
      c ⟨RankCutPort.output, by
        simp only [rankCutCarriedPortActive, rankCutPortActive]
        have houtRank := (mem_rankLevelVertices rank k output).1 hout
        omega⟩

noncomputable instance endpointAwareLevelLabelsOutputCompatibleDecidable
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (level : RankCutLevelLabels dim rank k) :
    Decidable (endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k c level) :=
  Classical.propDecidable _

/-- Turn one level label per vertex into the repeated source-coordinate tuple
seen by the entering-edge action. -/
noncomputable def rankEnteringSourceTupleOfLevelLabels
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ)
    (level : RankCutLevelLabels dim rank k) :
    EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList rank src k) :=
  (rankEnteringEdgeTupleEquiv dim rank src src k).symm
    (fun e ↦ level ⟨src e.1, by
      rw [mem_rankLevelVertices]
      exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)

@[simp]
theorem rankEnteringSourceTupleOfLevelLabels_apply
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ)
    (level : RankCutLevelLabels dim rank k)
    (e : {e // e ∈ rankEnteringEdges rank src k}) :
    (rankEnteringEdgeTupleEquiv dim rank src src k
      (rankEnteringSourceTupleOfLevelLabels dim rank src dst k level)) e =
      level ⟨src e.1, by
        rw [mem_rankLevelVertices]
        exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩ := by
  simp only [rankEnteringSourceTupleOfLevelLabels, Equiv.apply_symm_apply]

/-- The anchor-based level-label reader recovers the labels used to build the
repeated entering-source tuple. -/
theorem endpointAwareRankCutStepLevelLabel_sourceTuple
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k c level)
    (v : {v // v ∈ rankLevelVertices rank k}) :
    endpointAwareRankCutStepLevelLabel dim rank src dst input output hdag
        hedge k
        (c, rankEnteringSourceTupleOfLevelLabels dim rank src dst k level) v =
      level v := by
  classical
  rcases v with ⟨v, hv⟩
  by_cases hvo : v = output
  · subst v
    rw [endpointAwareRankCutStepLevelLabel_output dim rank src dst input output
      hdag hedge k]
    exact (hcompat hv).symm
  · simp only [endpointAwareRankCutStepLevelLabel, hvo, ↓reduceDIte]
    let vLevel : {v // v ∈ rankLevelVertices rank k} := ⟨v, hv⟩
    let e := mingoOutgoingRankAnchor
      rank src dst input output hdag hedge vLevel hvo
    have hesrc : src e = v :=
      mingoOutgoingRankAnchor_src
        rank src dst input output hdag hedge vLevel hvo
    have heIn : e ∈ rankEnteringEdges rank src k := by
      rw [mem_rankEnteringEdges, hesrc]
      exact (mem_rankLevelVertices rank k v).1 hv
    rw [rankEnteringSourceTupleOfLevelLabels_apply]
    apply dependentFin_cast_apply dim
    exact hesrc

/-- The tuple built from compatible level labels lies on the consistency
diagonal. -/
theorem endpointAwareRankCutStepConsistent_sourceTuple
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k c level) :
    endpointAwareRankCutStepConsistent dim rank src dst input output hdag
      hedge k
      (c, rankEnteringSourceTupleOfLevelLabels dim rank src dst k level) := by
  classical
  intro e
  rw [rankEnteringSourceTupleOfLevelLabels_apply]
  exact (endpointAwareRankCutStepLevelLabel_sourceTuple dim rank src dst
    input output hdag hedge k c level hcompat
    ⟨src e.1, by
      rw [mem_rankLevelVertices]
      exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩).symm

/-- For fixed carried coordinates, consistent repeated source tuples are
equivalent to level-label assignments satisfying the output-port constraint. -/
noncomputable def endpointAwareConsistentSourceTupleEquivLevelLabels
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k) :
    {xs : EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k) //
      endpointAwareRankCutStepConsistent dim rank src dst input output hdag
        hedge k (c, xs)} ≃
      {level : RankCutLevelLabels dim rank k //
        endpointAwareLevelLabelsOutputCompatible dim rank src dst
          input output k c level} := by
  classical
  refine
    { toFun := fun q ↦
        ⟨fun v ↦ endpointAwareRankCutStepLevelLabel dim rank src dst
            input output hdag hedge k (c, q.1) v,
          fun hout ↦ endpointAwareRankCutStepLevelLabel_output
            dim rank src dst input output hdag hedge k (c, q.1) hout⟩
      invFun := fun level ↦
        ⟨rankEnteringSourceTupleOfLevelLabels dim rank src dst k level.1,
          endpointAwareRankCutStepConsistent_sourceTuple
            dim rank src dst input output hdag hedge k c level.1 level.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    apply Subtype.ext
    apply (rankEnteringEdgeTupleEquiv dim rank src src k).injective
    funext e
    rw [rankEnteringSourceTupleOfLevelLabels_apply]
    exact (q.2 e).symm
  · intro level
    apply Subtype.ext
    funext v
    exact endpointAwareRankCutStepLevelLabel_sourceTuple dim rank src dst
      input output hdag hedge k c level.1 level.2 v

set_option maxHeartbeats 800000 in
/-- For fixed carried coordinates, summing the prepared array against the
entering matrices is exactly a sum over compatible one-label-per-level-vertex
assignments. -/
theorem endpointAwarePrepared_diagonal_sum
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (x : Fin (dim input) → ℝ)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (y : RankEnteringEdgeIndex dim rank src dst k) :
    (∑ xs,
        endpointAwareRankCutStepPrepared dim rank src dst M input output
            hdag hedge k hinput x (c, xs) *
          ∏ e : {e // e ∈ rankEnteringEdges rank src k},
            M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
              (y e)) =
      ∑ level : {level : RankCutLevelLabels dim rank k //
          endpointAwareLevelLabelsOutputCompatible dim rank src dst
            input output k c level},
        endpointAwareRankCutState dim rank src dst M hedge input output k x
            (endpointAwareOldBoundaryOfPrepared dim rank src dst input output
              hdag hedge k hinput
              ⟨(c, rankEnteringSourceTupleOfLevelLabels
                    dim rank src dst k level.1),
                endpointAwareRankCutStepConsistent_sourceTuple
                  dim rank src dst input output hdag hedge k c
                  level.1 level.2⟩) *
          ∏ e : {e // e ∈ rankEnteringEdges rank src k},
            M e.1 (level.1 ⟨src e.1, by
              rw [mem_rankLevelVertices]
              exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩) (y e) := by
  classical
  let P := fun xs : EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList rank src k) ↦
    endpointAwareRankCutStepConsistent dim rank src dst input output hdag
      hedge k (c, xs)
  let oldState := endpointAwareRankCutState dim rank src dst M hedge
    input output k x
  let oldBoundary := endpointAwareOldBoundaryOfPrepared dim rank src dst
    input output hdag hedge k hinput
  have hrewrite :
      (∑ xs,
          endpointAwareRankCutStepPrepared dim rank src dst M input output
              hdag hedge k hinput x (c, xs) *
            ∏ e : {e // e ∈ rankEnteringEdges rank src k},
              M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
                (y e)) =
        ∑ xs, if hxs : P xs then
          oldState (oldBoundary ⟨(c, xs), hxs⟩) *
            ∏ e : {e // e ∈ rankEnteringEdges rank src k},
              M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k xs) e)
                (y e)
        else 0 := by
    apply Finset.sum_congr rfl
    intro xs _
    by_cases hxs : P xs
    · simp only [endpointAwareRankCutStepPrepared, P, hxs, ↓reduceDIte,
        oldState, oldBoundary]
    · simp only [endpointAwareRankCutStepPrepared, P, hxs, ↓reduceDIte,
        zero_mul]
  rw [hrewrite]
  rw [sum_dite_eq_subtype P (fun q ↦
    oldState (oldBoundary ⟨(c, q.1), q.2⟩) *
      ∏ e : {e // e ∈ rankEnteringEdges rank src k},
        M e.1 ((rankEnteringEdgeTupleEquiv dim rank src src k q.1) e)
          (y e))]
  let E := endpointAwareConsistentSourceTupleEquivLevelLabels dim rank src dst
    input output hdag hedge k c
  let embed : {xs // P xs} →
      EndpointAwareConsistentPreparedIndex dim rank src dst input output
        hdag hedge k := fun q ↦ ⟨(c, q.1), q.2⟩
  apply Fintype.sum_equiv E
  intro q
  apply congrArg₂ (· * ·)
  · change oldState (oldBoundary (embed q)) =
      oldState (oldBoundary (embed (E.symm (E q))))
    exact congrArg (fun z ↦ oldState (oldBoundary (embed z)))
      (E.left_inv q).symm
  · apply Fintype.prod_congr
    intro e
    congr 1
    exact q.2 e

/-! ### Exact edge partitions used by the coefficient identity -/

/-- Old active edges which remain active after the current level is
processed. -/
noncomputable def rankPersistentEdges
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact rankActiveEdges rank src dst k \ rankLeavingEdges rank dst k

@[simp]
theorem mem_rankPersistentEdges
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankPersistentEdges rank src dst k ↔
      rank (src e) < k ∧ k < rank (dst e) := by
  classical
  simp only [rankPersistentEdges, Finset.mem_sdiff, mem_rankActiveEdges,
    mem_rankLeavingEdges]
  omega

/-- The old active cut is the disjoint union of disappearing edges and
persistent edges. -/
noncomputable def rankActiveEdgesEquivLeavingPersistent
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :
    {e // e ∈ rankActiveEdges rank src dst k} ≃
      Sum {e // e ∈ rankLeavingEdges rank dst k}
        {e // e ∈ rankPersistentEdges rank src dst k} := by
  classical
  refine
    { toFun := fun e ↦ if h : rank (dst e.1) = k then
          Sum.inl ⟨e.1, by simpa only [mem_rankLeavingEdges] using h⟩
        else
          Sum.inr ⟨e.1, by
            rw [mem_rankPersistentEdges]
            have he := (mem_rankActiveEdges rank src dst k e.1).1 e.2
            omega⟩
      invFun := fun e ↦ match e with
        | Sum.inl e => ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankLeavingEdges rank dst k e.1).1 e.2
            have hlt := hedge e.1
            exact ⟨by omega, by omega⟩⟩
        | Sum.inr e => ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
            exact ⟨he.1, Nat.le_of_lt he.2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases h : rank (dst e.1) = k <;> simp only [h, ↓reduceDIte]
  · intro e
    cases e with
    | inl e =>
        have h : rank (dst e.1) = k :=
          (mem_rankLeavingEdges rank dst k e.1).1 e.2
        simp only [h, ↓reduceDIte]
    | inr e =>
        have h : rank (dst e.1) ≠ k := by
          have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
          omega
        simp only [h, ↓reduceDIte]

/-- The new active cut is the disjoint union of persistent old edges and
newly entering edges. -/
noncomputable def rankActiveEdgesSuccEquivPersistentEntering
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :
    {e // e ∈ rankActiveEdges rank src dst (k + 1)} ≃
      Sum {e // e ∈ rankPersistentEdges rank src dst k}
        {e // e ∈ rankEnteringEdges rank src k} := by
  classical
  refine
    { toFun := fun e ↦ if h : rank (src e.1) = k then
          Sum.inr ⟨e.1, by simpa only [mem_rankEnteringEdges] using h⟩
        else
          Sum.inl ⟨e.1, by
            rw [mem_rankPersistentEdges]
            have he := (mem_rankActiveEdges rank src dst (k + 1) e.1).1 e.2
            omega⟩
      invFun := fun e ↦ match e with
        | Sum.inl e => ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
            exact ⟨by omega, by omega⟩⟩
        | Sum.inr e => ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankEnteringEdges rank src k e.1).1 e.2
            have hlt := hedge e.1
            exact ⟨by omega, by omega⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases h : rank (src e.1) = k <;> simp only [h, ↓reduceDIte]
  · intro e
    cases e with
    | inl e =>
        have h : rank (src e.1) ≠ k := by
          have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
          omega
        simp only [h, ↓reduceDIte]
    | inr e =>
        have h : rank (src e.1) = k :=
          (mem_rankEnteringEdges rank src k e.1).1 e.2
        simp only [h, ↓reduceDIte]

/-! ### Processed-label coordinate reductions -/

@[simp]
theorem rankProcessedLabelsSuccEquiv_symm_old_apply
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (v : {v // v ∈ rankProcessedVertices rank k})
    (hvSucc : v.1 ∈ rankProcessedVertices rank (k + 1)) :
    (rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
        ⟨v.1, hvSucc⟩ = old v := by
  classical
  simp only [rankProcessedLabelsSuccEquiv, Equiv.coe_fn_symm_mk]
  have hv := (mem_rankProcessedVertices rank k v.1).1 v.2
  simp only [hv, ↓reduceDIte]

@[simp]
theorem rankProcessedLabelsSuccEquiv_symm_level_apply
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (v : {v // v ∈ rankLevelVertices rank k})
    (hvSucc : v.1 ∈ rankProcessedVertices rank (k + 1)) :
    (rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
        ⟨v.1, hvSucc⟩ = level v := by
  classical
  simp only [rankProcessedLabelsSuccEquiv, Equiv.coe_fn_symm_mk]
  have hv := (mem_rankLevelVertices rank k v.1).1 v.2
  have hnlt : ¬rank v.1 < k := by omega
  simp only [hnlt, ↓reduceDIte]

theorem rankProcessedLabelsSuccEquiv_symm_old_apply_base
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (v : ι) (hvOld : v ∈ rankProcessedVertices rank k)
    (hvSucc : v ∈ rankProcessedVertices rank (k + 1)) :
    (rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
        ⟨v, hvSucc⟩ = old ⟨v, hvOld⟩ :=
  rankProcessedLabelsSuccEquiv_symm_old_apply
    dim rank k old level ⟨v, hvOld⟩ hvSucc

theorem rankProcessedLabelsSuccEquiv_symm_level_apply_base
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (v : ι) (hvLevel : v ∈ rankLevelVertices rank k)
    (hvSucc : v ∈ rankProcessedVertices rank (k + 1)) :
    (rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
        ⟨v, hvSucc⟩ = level ⟨v, hvLevel⟩ :=
  rankProcessedLabelsSuccEquiv_symm_level_apply
    dim rank k old level ⟨v, hvLevel⟩ hvSucc

/-- On a disappearing old-cut edge, the reconstructed target coordinate is
the supplied label of the edge's level-`k` target. -/
theorem endpointAwareOldBoundaryOfLevelLabels_edge_leaving
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (c : EndpointAwareRankCutCarriedIndex dim rank src dst input output k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k c level)
    (e : ε)
    (hp : rankCutPortActive rank src dst input output k (RankCutPort.edge e))
    (hedst : rank (dst e) = k) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput
        ⟨(c, rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
          endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
            input output hdag hedge k c level hcompat⟩
        ⟨RankCutPort.edge e, hp⟩ =
      level ⟨dst e, by simpa only [mem_rankLevelVertices] using hedst⟩ := by
  rw [endpointAwareOldBoundaryOfPrepared_edge_leaving dim rank src dst
    input output hdag hedge k hinput _ e hp hedst]
  exact endpointAwareRankCutStepLevelLabel_sourceTuple dim rank src dst
    input output hdag hedge k c level hcompat
    ⟨dst e, by simpa only [mem_rankLevelVertices] using hedst⟩

/-! ### Rank-cut summands -/

noncomputable def endpointAwareRankCutInputFactor
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ)
    (labels : RankCutProcessedLabels dim rank k)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) : ℝ := by
  classical
  exact if hinput : rank input < k then
    x (labels ⟨input, by simpa using hinput⟩)
  else
    x (boundary ⟨RankCutPort.input, by
      simp only [rankCutPortActive]
      omega⟩)

noncomputable def endpointAwareRankCutOutputFactor
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (labels : RankCutProcessedLabels dim rank k)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) : ℝ := by
  classical
  exact if houtput : rank output < k then
    if labels ⟨output, by simpa using houtput⟩ =
        boundary ⟨RankCutPort.output, by
          simpa only [rankCutPortActive] using houtput⟩ then 1 else 0
  else 1

noncomputable def endpointAwareRankCutEdgeFactor
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ)
    (labels : RankCutProcessedLabels dim rank k)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) : ℝ :=
  (∏ e : {e // e ∈ rankCompletedEdges rank dst k},
    M e.1
      (labels ⟨src e.1, by
        rw [mem_rankProcessedVertices]
        exact (hedge e.1).trans
          ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
      (labels ⟨dst e.1, by
        rw [mem_rankProcessedVertices]
        exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)) *
  ∏ e : {e // e ∈ rankActiveEdges rank src dst k},
    M e.1
      (labels ⟨src e.1, by
        rw [mem_rankProcessedVertices]
        exact ((mem_rankActiveEdges rank src dst k e.1).1 e.2).1⟩)
      (boundary ⟨RankCutPort.edge e.1, by
        simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)

noncomputable def endpointAwareRankCutSummand
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k)
    (labels : RankCutProcessedLabels dim rank k) : ℝ :=
  endpointAwareRankCutInputFactor dim rank src dst input output k x labels
      boundary *
    endpointAwareRankCutOutputFactor dim rank src dst input output k labels
      boundary *
    endpointAwareRankCutEdgeFactor dim rank src dst M hedge input output k
      labels boundary

theorem endpointAwareRankCutState_eq_sum_summand
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) :
    endpointAwareRankCutState dim rank src dst M hedge input output k x
        boundary =
      ∑ labels, endpointAwareRankCutSummand dim rank src dst M hedge
        input output k x boundary labels := by
  classical
  rw [endpointAwareRankCutState]
  apply Finset.sum_congr rfl
  intro labels _
  simp only [endpointAwareRankCutSummand, endpointAwareRankCutInputFactor,
    endpointAwareRankCutOutputFactor, endpointAwareRankCutEdgeFactor]
  ring

theorem endpointAwareRankCutInputFactor_succ_pos
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) (hinput : rank input = 0) (hk : 0 < k)
    (x : Fin (dim input) → ℝ)
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (newBoundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (oldBoundary : EndpointAwareRankCutIndex dim rank src dst input output k) :
    endpointAwareRankCutInputFactor dim rank src dst input output (k + 1) x
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level))
        newBoundary =
      endpointAwareRankCutInputFactor dim rank src dst input output k x old
        oldBoundary := by
  classical
  have hiOld : rank input < k := by omega
  have hiNew : rank input < k + 1 := by omega
  simp only [endpointAwareRankCutInputFactor, hiOld, hiNew, ↓reduceDIte]
  congr 1
  apply rankProcessedLabelsSuccEquiv_symm_old_apply_base

theorem endpointAwareOldBoundaryOfLevelLabels_output_eq_boundary
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level)
    (hpOld : rankCutPortActive rank src dst input output k RankCutPort.output) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput
        ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
              boundary).1,
            rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
          endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
            input output hdag hedge k
            (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
              boundary).1 level hcompat⟩
        ⟨RankCutPort.output, hpOld⟩ =
      boundary ⟨RankCutPort.output, by
        simp only [rankCutPortActive] at hpOld ⊢
        omega⟩ := by
  rw [endpointAwareOldBoundaryOfPrepared_output]
  rfl

theorem endpointAwareCompatibleLevelLabel_output_eq_boundary
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level)
    (hout : output ∈ rankLevelVertices rank k) :
    level ⟨output, hout⟩ =
      boundary ⟨RankCutPort.output, by
        simp only [rankCutPortActive]
        have houtRank := (mem_rankLevelVertices rank k output).1 hout
        omega⟩ := by
  simpa only [endpointAwareSuccBoundaryPost,
    endpointAwareSuccBoundaryToCarried, rankCutPortDim] using hcompat hout

theorem endpointAwareRankCutOutputFactor_succ_of_compatible
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level) :
    endpointAwareRankCutOutputFactor dim rank src dst input output (k + 1)
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level))
        boundary =
      endpointAwareRankCutOutputFactor dim rank src dst input output k old
        (endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
          hedge k hinput
          ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                boundary).1,
              rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
            endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
              input output hdag hedge k
              (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                boundary).1 level hcompat⟩) := by
  classical
  by_cases hbefore : rank output < k
  · have hnew : rank output < k + 1 := by omega
    simp only [endpointAwareRankCutOutputFactor, hbefore, hnew,
      ↓reduceDIte]
    have hlabels := rankProcessedLabelsSuccEquiv_symm_old_apply_base
      dim rank k old level output
      ((mem_rankProcessedVertices rank k output).2 hbefore)
      ((mem_rankProcessedVertices rank (k + 1) output).2 hnew)
    have hbound := endpointAwareOldBoundaryOfLevelLabels_output_eq_boundary
      dim rank src dst input output hdag hedge k hinput boundary level hcompat
      (by simpa only [rankCutPortActive] using hbefore)
    rw [hlabels, hbound]
  · by_cases hcurrent : rank output = k
    · have hnew : rank output < k + 1 := by omega
      simp only [endpointAwareRankCutOutputFactor, hbefore, hnew,
        ↓reduceDIte]
      have hout : output ∈ rankLevelVertices rank k :=
        (mem_rankLevelVertices rank k output).2 hcurrent
      have hlabels := rankProcessedLabelsSuccEquiv_symm_level_apply_base
        dim rank k old level output hout
        ((mem_rankProcessedVertices rank (k + 1) output).2 hnew)
      have hbound := endpointAwareCompatibleLevelLabel_output_eq_boundary
        dim rank src dst input output hedge k boundary level hcompat hout
      rw [hlabels, hbound]
      split
      · rfl
      · rename_i hne
        exfalso
        apply hne
        congr 1
    · have hnew : ¬rank output < k + 1 := by omega
      simp only [endpointAwareRankCutOutputFactor, hbefore, hnew,
        ↓reduceDIte]

set_option maxHeartbeats 800000 in
/-- The completed/active edge products at adjacent cuts differ exactly by
the matrices on the newly entering edges. -/
theorem endpointAwareRankCut_edge_products_succ
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level) :
    let merged := (rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
    let q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
        hdag hedge k :=
      ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
            boundary).1,
          rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
        endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
          input output hdag hedge k
          (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
            boundary).1 level hcompat⟩
    (∏ e : {e // e ∈ rankCompletedEdges rank dst (k + 1)},
        M e.1
          (merged ⟨src e.1, by
            rw [mem_rankProcessedVertices]
            exact (hedge e.1).trans
              ((mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2)⟩)
          (merged ⟨dst e.1, by
            rw [mem_rankProcessedVertices]
            exact (mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2⟩)) *
      (∏ e : {e // e ∈ rankActiveEdges rank src dst (k + 1)},
        M e.1
          (merged ⟨src e.1, by
            rw [mem_rankProcessedVertices]
            exact ((mem_rankActiveEdges rank src dst (k + 1) e.1).1 e.2).1⟩)
          (boundary ⟨RankCutPort.edge e.1, by
            simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)) =
      ((∏ e : {e // e ∈ rankCompletedEdges rank dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact (hedge e.1).trans
                ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
            (old ⟨dst e.1, by
              rw [mem_rankProcessedVertices]
              exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)) *
        (∏ e : {e // e ∈ rankActiveEdges rank src dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact ((mem_rankActiveEdges rank src dst k e.1).1 e.2).1⟩)
            (endpointAwareOldBoundaryOfPrepared dim rank src dst input output
              hdag hedge k hinput q
              ⟨RankCutPort.edge e.1, by
                simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩))) *
        ∏ e : {e // e ∈ rankEnteringEdges rank src k},
          M e.1
            (level ⟨src e.1, by
              rw [mem_rankLevelVertices]
              exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩) := by
  classical
  dsimp only
  have hcompleted :
      (∏ e : {e // e ∈ rankCompletedEdges rank dst (k + 1)},
          M e.1
            ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
              ⟨src e.1, by
                rw [mem_rankProcessedVertices]
                exact (hedge e.1).trans
                  ((mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2)⟩)
            ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
              ⟨dst e.1, by
                rw [mem_rankProcessedVertices]
                exact (mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2⟩)) =
        (∏ e : {e // e ∈ rankCompletedEdges rank dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact (hedge e.1).trans
                ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
            (old ⟨dst e.1, by
              rw [mem_rankProcessedVertices]
              exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)) *
        ∏ e : {e // e ∈ rankLeavingEdges rank dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              have heq := (mem_rankLeavingEdges rank dst k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩)
            (level ⟨dst e.1, by
              simpa only [mem_rankLevelVertices] using
                (mem_rankLeavingEdges rank dst k e.1).1 e.2⟩) := by
    let newF : {e // e ∈ rankCompletedEdges rank dst (k + 1)} → ℝ :=
      fun e ↦ M e.1
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
          ⟨src e.1, by
            rw [mem_rankProcessedVertices]
            exact (hedge e.1).trans
              ((mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2)⟩)
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
          ⟨dst e.1, by
            rw [mem_rankProcessedVertices]
            exact (mem_rankCompletedEdges rank dst (k + 1) e.1).1 e.2⟩)
    let oldF : {e // e ∈ rankCompletedEdges rank dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          exact (hedge e.1).trans
            ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
        (old ⟨dst e.1, by
          rw [mem_rankProcessedVertices]
          exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)
    let leavingF : {e // e ∈ rankLeavingEdges rank dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          have heq := (mem_rankLeavingEdges rank dst k e.1).1 e.2
          have hlt := hedge e.1
          omega⟩)
        (level ⟨dst e.1, by
          simpa only [mem_rankLevelVertices] using
            (mem_rankLeavingEdges rank dst k e.1).1 e.2⟩)
    change (∏ e, newF e) = (∏ e, oldF e) * ∏ e, leavingF e
    calc
      (∏ e, newF e) =
          ∏ s : Sum {e // e ∈ rankCompletedEdges rank dst k}
            {e // e ∈ rankLeavingEdges rank dst k},
              Sum.elim oldF leavingF s := by
        symm
        apply Fintype.prod_equiv (rankCompletedEdgesSuccEquiv rank dst k).symm
        intro s
        cases s with
        | inl e =>
          change oldF e = newF ⟨e.1, by
            rw [mem_rankCompletedEdges]
            have he := (mem_rankCompletedEdges rank dst k e.1).1 e.2
            omega⟩
          simp only [newF, oldF]
          apply congrArg₂ (M e.1)
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_old_apply_base
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_old_apply_base
        | inr e =>
          change leavingF e = newF ⟨e.1, by
            rw [mem_rankCompletedEdges]
            have he := (mem_rankLeavingEdges rank dst k e.1).1 e.2
            omega⟩
          simp only [newF, leavingF]
          apply congrArg₂ (M e.1)
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_old_apply_base
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_level_apply_base
      _ = (∏ e, oldF e) * ∏ e, leavingF e :=
        Fintype.prod_sum_type _
  let c := (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
    boundary).1
  let q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k :=
    ⟨(c, rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
      endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
        input output hdag hedge k c level hcompat⟩
  have holdActive :
      (∏ e : {e // e ∈ rankActiveEdges rank src dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact ((mem_rankActiveEdges rank src dst k e.1).1 e.2).1⟩)
            (endpointAwareOldBoundaryOfPrepared dim rank src dst input output
              hdag hedge k hinput q
              ⟨RankCutPort.edge e.1, by
                simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)) =
        (∏ e : {e // e ∈ rankLeavingEdges rank dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              have heq := (mem_rankLeavingEdges rank dst k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩)
            (level ⟨dst e.1, by
              simpa only [mem_rankLevelVertices] using
                (mem_rankLeavingEdges rank dst k e.1).1 e.2⟩)) *
        ∏ e : {e // e ∈ rankPersistentEdges rank src dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact ((mem_rankPersistentEdges rank src dst k e.1).1 e.2).1⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
              omega⟩) := by
    let oldActiveF : {e // e ∈ rankActiveEdges rank src dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          exact ((mem_rankActiveEdges rank src dst k e.1).1 e.2).1⟩)
        (endpointAwareOldBoundaryOfPrepared dim rank src dst input output
          hdag hedge k hinput q
          ⟨RankCutPort.edge e.1, by
            simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)
    let leavingF : {e // e ∈ rankLeavingEdges rank dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          have heq := (mem_rankLeavingEdges rank dst k e.1).1 e.2
          have hlt := hedge e.1
          omega⟩)
        (level ⟨dst e.1, by
          simpa only [mem_rankLevelVertices] using
            (mem_rankLeavingEdges rank dst k e.1).1 e.2⟩)
    let persistentF : {e // e ∈ rankPersistentEdges rank src dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          exact ((mem_rankPersistentEdges rank src dst k e.1).1 e.2).1⟩)
        (boundary ⟨RankCutPort.edge e.1, by
          simp only [rankCutPortActive]
          have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
          omega⟩)
    change (∏ e, oldActiveF e) =
      (∏ e, leavingF e) * ∏ e, persistentF e
    calc
      (∏ e, oldActiveF e) =
          ∏ s : Sum {e // e ∈ rankLeavingEdges rank dst k}
            {e // e ∈ rankPersistentEdges rank src dst k},
              Sum.elim leavingF persistentF s := by
        symm
        apply Fintype.prod_equiv
          (rankActiveEdgesEquivLeavingPersistent rank src dst hedge k).symm
        intro s
        cases s with
        | inl e =>
          change leavingF e = oldActiveF ⟨e.1, by
            rw [mem_rankActiveEdges]
            have heq := (mem_rankLeavingEdges rank dst k e.1).1 e.2
            have hlt := hedge e.1
            omega⟩
          simp only [oldActiveF, leavingF]
          apply congrArg₂ (M e.1)
          · rfl
          · symm
            simpa only [q, rankCutPortDim] using
              endpointAwareOldBoundaryOfLevelLabels_edge_leaving dim rank
                src dst input output hdag hedge k hinput c level hcompat e.1
                (by
                  rw [rankCutPortActive]
                  have heq :=
                    (mem_rankLeavingEdges rank dst k e.1).1 e.2
                  have hlt := hedge e.1
                  omega)
                ((mem_rankLeavingEdges rank dst k e.1).1 e.2)
        | inr e =>
          change persistentF e = oldActiveF ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
            exact ⟨he.1, Nat.le_of_lt he.2⟩⟩
          simp only [oldActiveF, persistentF]
          apply congrArg₂ (M e.1)
          · rfl
          · rw [endpointAwareOldBoundaryOfPrepared_edge_persistent]
            rfl
            have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
            omega
      _ = (∏ e, leavingF e) * ∏ e, persistentF e :=
        Fintype.prod_sum_type _
  have hnewActive :
      (∏ e : {e // e ∈ rankActiveEdges rank src dst (k + 1)},
          M e.1
            ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
              ⟨src e.1, by
                rw [mem_rankProcessedVertices]
                exact ((mem_rankActiveEdges rank src dst (k + 1) e.1).1
                  e.2).1⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simpa only [rankCutPortActive, mem_rankActiveEdges] using
                e.2⟩)) =
        (∏ e : {e // e ∈ rankPersistentEdges rank src dst k},
          M e.1
            (old ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact ((mem_rankPersistentEdges rank src dst k e.1).1 e.2).1⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
              omega⟩)) *
        ∏ e : {e // e ∈ rankEnteringEdges rank src k},
          M e.1
            (level ⟨src e.1, by
              rw [mem_rankLevelVertices]
              exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩) := by
    let newActiveF : {e // e ∈ rankActiveEdges rank src dst (k + 1)} → ℝ :=
      fun e ↦ M e.1
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)
          ⟨src e.1, by
            rw [mem_rankProcessedVertices]
            exact ((mem_rankActiveEdges rank src dst (k + 1) e.1).1 e.2).1⟩)
        (boundary ⟨RankCutPort.edge e.1, by
          simpa only [rankCutPortActive, mem_rankActiveEdges] using e.2⟩)
    let persistentF : {e // e ∈ rankPersistentEdges rank src dst k} → ℝ :=
      fun e ↦ M e.1
        (old ⟨src e.1, by
          rw [mem_rankProcessedVertices]
          exact ((mem_rankPersistentEdges rank src dst k e.1).1 e.2).1⟩)
        (boundary ⟨RankCutPort.edge e.1, by
          simp only [rankCutPortActive]
          have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
          omega⟩)
    let enteringF : {e // e ∈ rankEnteringEdges rank src k} → ℝ :=
      fun e ↦ M e.1
        (level ⟨src e.1, by
          rw [mem_rankLevelVertices]
          exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
        (boundary ⟨RankCutPort.edge e.1, by
          simp only [rankCutPortActive]
          have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
          have hlt := hedge e.1
          omega⟩)
    change (∏ e, newActiveF e) =
      (∏ e, persistentF e) * ∏ e, enteringF e
    calc
      (∏ e, newActiveF e) =
          ∏ s : Sum {e // e ∈ rankPersistentEdges rank src dst k}
            {e // e ∈ rankEnteringEdges rank src k},
              Sum.elim persistentF enteringF s := by
        symm
        apply Fintype.prod_equiv
          (rankActiveEdgesSuccEquivPersistentEntering
            rank src dst hedge k).symm
        intro s
        cases s with
        | inl e =>
          change persistentF e = newActiveF ⟨e.1, by
            rw [mem_rankActiveEdges]
            have he := (mem_rankPersistentEdges rank src dst k e.1).1 e.2
            omega⟩
          simp only [newActiveF, persistentF]
          apply congrArg₂ (M e.1)
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_old_apply_base
          · rfl
        | inr e =>
          change enteringF e = newActiveF ⟨e.1, by
            rw [mem_rankActiveEdges]
            have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
            have hlt := hedge e.1
            omega⟩
          simp only [newActiveF, enteringF]
          apply congrArg₂ (M e.1)
          · symm
            apply rankProcessedLabelsSuccEquiv_symm_level_apply_base
          · rfl
      _ = (∏ e, persistentF e) * ∏ e, enteringF e :=
        Fintype.prod_sum_type _
  rw [hcompleted, hnewActive, holdActive]
  ring

theorem endpointAwareRankCutEdgeFactor_succ
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level) :
    endpointAwareRankCutEdgeFactor dim rank src dst M hedge input output
        (k + 1) ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level))
        boundary =
      endpointAwareRankCutEdgeFactor dim rank src dst M hedge input output k old
          (endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
            hedge k hinput
            ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                  boundary).1,
                rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
              endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
                input output hdag hedge k
                (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                  boundary).1 level hcompat⟩) *
        ∏ e : {e // e ∈ rankEnteringEdges rank src k},
          M e.1
            (level ⟨src e.1, by
              rw [mem_rankLevelVertices]
              exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩) := by
  simpa only [endpointAwareRankCutEdgeFactor] using
    endpointAwareRankCut_edge_products_succ dim rank src dst M input output
      hdag hedge k hinput boundary old level hcompat

theorem endpointAwareRankCutSummand_succ_pos
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hk : 0 < k)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k)
    (hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level) :
    endpointAwareRankCutSummand dim rank src dst M hedge input output (k + 1)
        x boundary
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)) =
      endpointAwareRankCutSummand dim rank src dst M hedge input output k x
          (endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
            hedge k hinput
            ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                  boundary).1,
                rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
              endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
                input output hdag hedge k
                (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
                  boundary).1 level hcompat⟩) old *
        ∏ e : {e // e ∈ rankEnteringEdges rank src k},
          M e.1
            (level ⟨src e.1, by
              rw [mem_rankLevelVertices]
              exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
            (boundary ⟨RankCutPort.edge e.1, by
              simp only [rankCutPortActive]
              have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
              have hlt := hedge e.1
              omega⟩) := by
  rw [endpointAwareRankCutSummand]
  rw [endpointAwareRankCutInputFactor_succ_pos dim rank src dst input output
    k hinput hk x old level]
  rw [endpointAwareRankCutOutputFactor_succ_of_compatible dim rank src dst
    input output hdag hedge k hinput boundary old level hcompat]
  rw [endpointAwareRankCutEdgeFactor_succ dim rank src dst M input output
    hdag hedge k hinput boundary old level hcompat]
  simp only [endpointAwareRankCutSummand]
  ring

theorem endpointAwareRankCutSummand_succ_pos_dite
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hk : 0 < k)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1))
    (old : RankCutProcessedLabels dim rank k)
    (level : RankCutLevelLabels dim rank k) :
    endpointAwareRankCutSummand dim rank src dst M hedge input output (k + 1)
        x boundary
        ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)) =
      if hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
          input output k
          (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
            boundary).1 level then
        endpointAwareRankCutSummand dim rank src dst M hedge input output k x
            (endpointAwareOldBoundaryOfPrepared dim rank src dst input output
              hdag hedge k hinput
              ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge
                    input output k boundary).1,
                  rankEnteringSourceTupleOfLevelLabels dim rank src dst k level),
                endpointAwareRankCutStepConsistent_sourceTuple dim rank src dst
                  input output hdag hedge k
                  (endpointAwareSuccBoundaryPost dim rank src dst hedge
                    input output k boundary).1 level hcompat⟩) old *
          ∏ e : {e // e ∈ rankEnteringEdges rank src k},
            M e.1
              (level ⟨src e.1, by
                rw [mem_rankLevelVertices]
                exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
              (boundary ⟨RankCutPort.edge e.1, by
                simp only [rankCutPortActive]
                have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                have hlt := hedge e.1
                omega⟩)
      else 0 := by
  classical
  by_cases hcompat : endpointAwareLevelLabelsOutputCompatible dim rank src dst
      input output k
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
        boundary).1 level
  · simp only [hcompat, ↓reduceDIte]
    exact endpointAwareRankCutSummand_succ_pos dim rank src dst M input output
      hdag hedge k hinput hk x boundary old level hcompat
  · simp only [hcompat, ↓reduceDIte]
    simp only [endpointAwareLevelLabelsOutputCompatible] at hcompat
    push_neg at hcompat
    rcases hcompat with ⟨hout, hne⟩
    have houtRank : rank output = k :=
      (mem_rankLevelVertices rank k output).1 hout
    have houtNew : rank output < k + 1 := by omega
    have hneBoundary :
        level ⟨output, hout⟩ ≠
          boundary ⟨RankCutPort.output, by
            simp only [rankCutPortActive]
            omega⟩ := by
      simpa only [endpointAwareSuccBoundaryPost,
        endpointAwareSuccBoundaryToCarried, rankCutPortDim] using hne
    rw [endpointAwareRankCutSummand]
    have houtputFactor :
        endpointAwareRankCutOutputFactor dim rank src dst input output
            (k + 1)
            ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level))
            boundary = 0 := by
      simp only [endpointAwareRankCutOutputFactor, houtNew, ↓reduceDIte]
      rw [rankProcessedLabelsSuccEquiv_symm_level_apply_base dim rank k old
        level output hout
        ((mem_rankProcessedVertices rank (k + 1) output).2 houtNew)]
      split
      · rename_i heq
        exact (hneBoundary heq).elim
      · rfl
    rw [houtputFactor]
    ring

set_option maxHeartbeats 1600000 in
/-- The full adjacent-cut coefficient identity at every positive rank level. -/
theorem endpointAwareRankCutState_factor_pos
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hk : 0 < k)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
    endpointAwareRankCutState dim rank src dst M hedge input output (k + 1)
        x boundary =
      edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList rank src k)
        (fun xs ↦ endpointAwareRankCutStepPrepared dim rank src dst M
          input output hdag hedge k hinput x
          ((endpointAwareSuccBoundaryPost dim rank src dst hedge
            input output k boundary).1, xs))
        (endpointAwareSuccBoundaryPost dim rank src dst hedge
          input output k boundary).2 := by
  classical
  rw [endpointAwareRankCutStepAction_eq_expanded dim rank src dst M input
    output hdag hedge k hinput x boundary]
  rw [endpointAwarePrepared_diagonal_sum dim rank src dst M input output
    hdag hedge k hinput x
    (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k
      boundary).1
    (fun e ↦ boundary ⟨RankCutPort.edge e.1, by
      simp only [rankCutPortActive]
      have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
      have hlt := hedge e.1
      omega⟩)]
  rw [endpointAwareRankCutState_eq_sum_summand]
  simp_rw [endpointAwareRankCutState_eq_sum_summand]
  simp_rw [Finset.sum_mul]
  calc
    (∑ labels : RankCutProcessedLabels dim rank (k + 1),
        endpointAwareRankCutSummand dim rank src dst M hedge input output
          (k + 1) x boundary labels) =
      ∑ pair : RankCutProcessedLabels dim rank k ×
          RankCutLevelLabels dim rank k,
        endpointAwareRankCutSummand dim rank src dst M hedge input output
          (k + 1) x boundary
          ((rankProcessedLabelsSuccEquiv dim rank k).symm pair) := by
      apply Fintype.sum_equiv (rankProcessedLabelsSuccEquiv dim rank k)
      intro labels
      rw [Equiv.symm_apply_apply]
    _ = ∑ old : RankCutProcessedLabels dim rank k,
        ∑ level : RankCutLevelLabels dim rank k,
          endpointAwareRankCutSummand dim rank src dst M hedge input output
            (k + 1) x boundary
            ((rankProcessedLabelsSuccEquiv dim rank k).symm (old, level)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ old : RankCutProcessedLabels dim rank k,
        ∑ level : RankCutLevelLabels dim rank k,
          if hcompat : endpointAwareLevelLabelsOutputCompatible dim rank
              src dst input output k
              (endpointAwareSuccBoundaryPost dim rank src dst hedge
                input output k boundary).1 level then
            endpointAwareRankCutSummand dim rank src dst M hedge input output
                k x
                (endpointAwareOldBoundaryOfPrepared dim rank src dst
                  input output hdag hedge k hinput
                  ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge
                        input output k boundary).1,
                      rankEnteringSourceTupleOfLevelLabels dim rank src dst
                        k level),
                    endpointAwareRankCutStepConsistent_sourceTuple dim rank
                      src dst input output hdag hedge k
                      (endpointAwareSuccBoundaryPost dim rank src dst hedge
                        input output k boundary).1 level hcompat⟩) old *
              ∏ e : {e // e ∈ rankEnteringEdges rank src k},
                M e.1
                  (level ⟨src e.1, by
                    rw [mem_rankLevelVertices]
                    exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
                  (boundary ⟨RankCutPort.edge e.1, by
                    simp only [rankCutPortActive]
                    have heq :=
                      (mem_rankEnteringEdges rank src k e.1).1 e.2
                    have hlt := hedge e.1
                    omega⟩)
          else 0 := by
      apply Finset.sum_congr rfl
      intro old _
      apply Finset.sum_congr rfl
      intro level _
      exact endpointAwareRankCutSummand_succ_pos_dite dim rank src dst M
        input output hdag hedge k hinput hk x boundary old level
    _ = ∑ old : RankCutProcessedLabels dim rank k,
        ∑ level : {level : RankCutLevelLabels dim rank k //
            endpointAwareLevelLabelsOutputCompatible dim rank src dst
              input output k
              (endpointAwareSuccBoundaryPost dim rank src dst hedge
                input output k boundary).1 level},
          endpointAwareRankCutSummand dim rank src dst M hedge input output
              k x
              (endpointAwareOldBoundaryOfPrepared dim rank src dst
                input output hdag hedge k hinput
                ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge
                      input output k boundary).1,
                    rankEnteringSourceTupleOfLevelLabels dim rank src dst
                      k level.1),
                  endpointAwareRankCutStepConsistent_sourceTuple dim rank
                    src dst input output hdag hedge k
                    (endpointAwareSuccBoundaryPost dim rank src dst hedge
                      input output k boundary).1 level.1 level.2⟩) old *
            ∏ e : {e // e ∈ rankEnteringEdges rank src k},
              M e.1
                (level.1 ⟨src e.1, by
                  rw [mem_rankLevelVertices]
                  exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
                (boundary ⟨RankCutPort.edge e.1, by
                  simp only [rankCutPortActive]
                  have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                  have hlt := hedge e.1
                  omega⟩) := by
      apply Finset.sum_congr rfl
      intro old _
      let P := fun level : RankCutLevelLabels dim rank k ↦
        endpointAwareLevelLabelsOutputCompatible dim rank src dst
          input output k
          (endpointAwareSuccBoundaryPost dim rank src dst hedge
            input output k boundary).1 level
      let f : {level // P level} → ℝ := fun level ↦
        endpointAwareRankCutSummand dim rank src dst M hedge input output
            k x
            (endpointAwareOldBoundaryOfPrepared dim rank src dst
              input output hdag hedge k hinput
              ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge
                    input output k boundary).1,
                  rankEnteringSourceTupleOfLevelLabels dim rank src dst
                    k level.1),
                endpointAwareRankCutStepConsistent_sourceTuple dim rank
                  src dst input output hdag hedge k
                  (endpointAwareSuccBoundaryPost dim rank src dst hedge
                    input output k boundary).1 level.1 level.2⟩) old *
          ∏ e : {e // e ∈ rankEnteringEdges rank src k},
            M e.1
              (level.1 ⟨src e.1, by
                rw [mem_rankLevelVertices]
                exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
              (boundary ⟨RankCutPort.edge e.1, by
                simp only [rankCutPortActive]
                have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                have hlt := hedge e.1
                omega⟩)
      change (∑ level, if h : P level then f ⟨level, h⟩ else 0) =
        ∑ level, f level
      exact sum_dite_eq_subtype P f
    _ = ∑ level : {level : RankCutLevelLabels dim rank k //
          endpointAwareLevelLabelsOutputCompatible dim rank src dst
            input output k
            (endpointAwareSuccBoundaryPost dim rank src dst hedge
              input output k boundary).1 level},
        ∑ old : RankCutProcessedLabels dim rank k,
          endpointAwareRankCutSummand dim rank src dst M hedge input output
              k x
              (endpointAwareOldBoundaryOfPrepared dim rank src dst
                input output hdag hedge k hinput
                ⟨((endpointAwareSuccBoundaryPost dim rank src dst hedge
                      input output k boundary).1,
                    rankEnteringSourceTupleOfLevelLabels dim rank src dst
                      k level.1),
                  endpointAwareRankCutStepConsistent_sourceTuple dim rank
                    src dst input output hdag hedge k
                    (endpointAwareSuccBoundaryPost dim rank src dst hedge
                      input output k boundary).1 level.1 level.2⟩) old *
            ∏ e : {e // e ∈ rankEnteringEdges rank src k},
              M e.1
                (level.1 ⟨src e.1, by
                  rw [mem_rankLevelVertices]
                  exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩)
                (boundary ⟨RankCutPort.edge e.1, by
                  simp only [rankCutPortActive]
                  have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
                  have hlt := hedge e.1
                  omega⟩) := by
      rw [Finset.sum_comm]

set_option maxHeartbeats 1600000 in
/-- The adjacent-cut coefficient identity for every rank level of an
admissible DAG, combining the explicit first step with the positive-level
reindexing above. -/
theorem endpointAwareRankCutState_factor_all
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output) (k : ℕ) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim (mingoDAGRank src dst)
      src dst input output (k + 1)) :
    endpointAwareRankCutState dim (mingoDAGRank src dst) src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output (k + 1) x boundary =
      edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList (mingoDAGRank src dst) src k)
        (fun xs ↦ endpointAwareRankCutStepPrepared dim
          (mingoDAGRank src dst) src dst M input output hdag
          (fun e ↦ hdag.edge_rank_lt src dst input output e) k
          (hdag.input_rank_eq_zero src dst input output) x
          ((endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
            (fun e ↦ hdag.edge_rank_lt src dst input output e)
            input output k boundary).1, xs))
        (endpointAwareSuccBoundaryPost dim (mingoDAGRank src dst) src dst
          (fun e ↦ hdag.edge_rank_lt src dst input output e)
          input output k boundary).2 := by
  cases k with
  | zero =>
      exact endpointAwareRankCutState_factor_zero dim src dst M input output
        hdag hio x boundary
  | succ k =>
      exact endpointAwareRankCutState_factor_pos dim (mingoDAGRank src dst)
        src dst M input output hdag
        (fun e ↦ hdag.edge_rank_lt src dst input output e) (k + 1)
        (hdag.input_rank_eq_zero src dst input output) (Nat.succ_pos k) x
        boundary

/-- Concrete exact adjacent-cut certificate at every rank level. -/
noncomputable def endpointAwareRankCutStepFactorization_all
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input ≠ output) (k : ℕ) (x : Fin (dim input) → ℝ) :
    EndpointAwareRankCutStepFactorization dim (mingoDAGRank src dst)
      src dst M (fun e ↦ hdag.edge_rank_lt src dst input output e)
      input output k x :=
  endpointAwareRankCutStepFactorization_of_state_factor dim
    (mingoDAGRank src dst) src dst M input output hdag
    (fun e ↦ hdag.edge_rank_lt src dst input output e) k
    (hdag.input_rank_eq_zero src dst input output) hio x
    (endpointAwareRankCutState_factor_all dim src dst M input output hdag
      hio k x)

/-- Kernel-clean completion of the frozen I04 graph-operator interface. -/
theorem mingo_speicher_graph_operator_specialization
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    euclideanOperatorNorm (graphOperator dim src dst M input output) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  classical
  by_cases hsame : input = output
  · subst output
    exact graphOperator_norm_le_edge_product_same_endpoint dim src dst M
      input hdag
  · by_cases hzero : ∃ v, dim v = 0
    · exact graphOperator_norm_le_edge_product_of_exists_zero_dim dim src dst M
        input output hzero
    · have _hdim : ∀ v, 0 < dim v :=
        all_dim_pos_of_not_exists_zero dim hzero
      exact graphOperator_norm_le_of_stepFactorizations dim src dst M
        input output hdag fun x k _hk ↦
          endpointAwareRankCutStepFactorization_all dim src dst M input output
            hdag hsame k x


end Problem56
