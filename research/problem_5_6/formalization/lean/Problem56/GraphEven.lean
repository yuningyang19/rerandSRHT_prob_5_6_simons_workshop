import Problem56.Definitions

/-!
The cut-parity argument used in `solution.tex` for connected finite multigraphs
of even degree.  Edges are an indexed family, so parallel edges remain distinct;
loops are counted once at each endpoint by `graphDegree`, hence twice in total.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

private theorem sum_graphDegree_on_finset
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (S : Finset ι) :
    (∑ v ∈ S, graphDegree src dst v) =
      ∑ e, ((if src e ∈ S then 1 else 0) + (if dst e ∈ S then 1 else 0)) := by
  classical
  simp only [graphDegree, Finset.sum_add_distrib]
  congr 1
  · calc
      (∑ v ∈ S, (Finset.univ.filter fun e ↦ src e = v).card) =
          (Finset.univ.filter fun e ↦ src e ∈ S).card := by
            exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ S src
      _ = ∑ e, if src e ∈ S then 1 else 0 := by
            rw [Finset.card_eq_sum_ones]
            simp only [Finset.sum_filter]
  · calc
      (∑ v ∈ S, (Finset.univ.filter fun e ↦ dst e = v).card) =
          (Finset.univ.filter fun e ↦ dst e ∈ S).card := by
            exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ S dst
      _ = ∑ e, if dst e ∈ S then 1 else 0 := by
            rw [Finset.card_eq_sum_ones]
            simp only [Finset.sum_filter]

private theorem deleted_edge_endpoints_reachable
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι)
    (heven : ∀ v, Even (graphDegree src dst v)) (e₀ : ε) :
    Relation.ReflTransGen
      (graphAdjacent (fun e : {e // e ≠ e₀} ↦ src e.1)
        (fun e : {e // e ≠ e₀} ↦ dst e.1))
      (src e₀) (dst e₀) := by
  classical
  let adj₀ : ι → ι → Prop :=
    graphAdjacent (fun e : {e // e ≠ e₀} ↦ src e.1)
      (fun e : {e // e ≠ e₀} ↦ dst e.1)
  by_contra hnot
  let S : Finset ι := Finset.univ.filter fun v ↦
    Relation.ReflTransGen adj₀ (src e₀) v
  have hsrc : src e₀ ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have hdst : dst e₀ ∉ S := by
    simpa [S, adj₀] using hnot
  have hedge_side : ∀ e : ε, e ≠ e₀ → (src e ∈ S ↔ dst e ∈ S) := by
    intro e he
    constructor
    · intro hs
      have hrs : Relation.ReflTransGen adj₀ (src e₀) (src e) :=
        (Finset.mem_filter.mp hs).2
      have hadj : adj₀ (src e) (dst e) := by
        exact ⟨⟨e, he⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs.tail hadj⟩
    · intro hd
      have hrd : Relation.ReflTransGen adj₀ (src e₀) (dst e) :=
        (Finset.mem_filter.mp hd).2
      have hadj : adj₀ (dst e) (src e) := by
        exact ⟨⟨e, he⟩, Or.inr ⟨rfl, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrd.tail hadj⟩
  have hsum_even : Even (∑ v ∈ S, graphDegree src dst v) := by
    apply Finset.even_sum
    intro v _
    exact heven v
  have hincidence :
      (∑ v ∈ S, graphDegree src dst v) =
        1 + 2 * ((Finset.univ.erase e₀).filter fun e ↦ src e ∈ S).card := by
    rw [sum_graphDegree_on_finset src dst S]
    calc
      (∑ e,
          ((if src e ∈ S then 1 else 0) + (if dst e ∈ S then 1 else 0))) =
          ((if src e₀ ∈ S then 1 else 0) + (if dst e₀ ∈ S then 1 else 0)) +
            ∑ e ∈ Finset.univ.erase e₀,
              ((if src e ∈ S then 1 else 0) + (if dst e ∈ S then 1 else 0)) := by
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e₀)]
      _ = 1 + ∑ e ∈ Finset.univ.erase e₀,
              (if src e ∈ S then 2 else 0) := by
            rw [if_pos hsrc, if_neg hdst]
            congr 1
            apply Finset.sum_congr rfl
            intro e he
            have hne : e ≠ e₀ := Finset.ne_of_mem_erase he
            by_cases hs : src e ∈ S
            · have hd : dst e ∈ S := (hedge_side e hne).mp hs
              simp [hs, hd]
            · have hd : dst e ∉ S := fun h ↦ hs ((hedge_side e hne).mpr h)
              simp [hs, hd]
      _ = 1 + 2 * ((Finset.univ.erase e₀).filter fun e ↦ src e ∈ S).card := by
            simp [Finset.sum_ite, mul_comm]
  rw [hincidence] at hsum_even
  rcases hsum_even with ⟨c, hc⟩
  omega

theorem connected_even_multigraph_has_no_bridge
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (hconn : GraphConnected src dst)
    (heven : ∀ v, Even (graphDegree src dst v)) :
    ∀ e₀ : ε, GraphConnected
      (fun e : {e // e ≠ e₀} ↦ src e.1)
      (fun e : {e // e ≠ e₀} ↦ dst e.1) := by
  intro e₀ u v
  let adj₀ : ι → ι → Prop :=
    graphAdjacent (fun e : {e // e ≠ e₀} ↦ src e.1)
      (fun e : {e // e ≠ e₀} ↦ dst e.1)
  have hend : Relation.ReflTransGen adj₀ (src e₀) (dst e₀) :=
    deleted_edge_endpoints_reachable src dst heven e₀
  have hadj_symm : ∀ {a b : ι}, adj₀ a b → adj₀ b a := by
    intro a b hab
    rcases hab with ⟨e, h | h⟩
    · exact ⟨e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨e, Or.inl ⟨h.1, h.2⟩⟩
  have reach_symm : ∀ {a b : ι}, Relation.ReflTransGen adj₀ a b →
      Relation.ReflTransGen adj₀ b a := by
    intro a b hab
    exact hab.trans_induction_on
      (fun _ ↦ Relation.ReflTransGen.refl)
      (fun h ↦ Relation.ReflTransGen.single (hadj_symm h))
      (fun _ _ ih₁ ih₂ ↦ ih₂.trans ih₁)
  have hstep : ∀ a b, graphAdjacent src dst a b →
      Relation.ReflTransGen adj₀ a b := by
    intro a b hab
    rcases hab with ⟨e, hab | hab⟩
    · rcases hab with ⟨rfl, rfl⟩
      by_cases he : e = e₀
      · simpa [he] using hend
      · exact Relation.ReflTransGen.single ⟨⟨e, he⟩, Or.inl ⟨rfl, rfl⟩⟩
    · rcases hab with ⟨rfl, rfl⟩
      by_cases he : e = e₀
      · subst e
        exact reach_symm hend
      · exact Relation.ReflTransGen.single ⟨⟨e, he⟩, Or.inr ⟨rfl, rfl⟩⟩
  induction hconn u v with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih => exact ih.trans (hstep _ _ hyz)

private theorem euclideanNorm_eq_norm_toLp_for_reversal
    {α : Type*} [Fintype α] (x : α → ℝ) :
    euclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem euclideanOperatorNorm_eq_l2_opNorm_for_reversal
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α β ℝ) :
    euclideanOperatorNorm A = ‖A‖ := by
  let T : EuclideanSpace ℝ β →L[ℝ] EuclideanSpace ℝ α :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := α) (n := β)).trans
      LinearMap.toContinuousLinearMap A
  rw [euclideanOperatorNorm, Matrix.l2_opNorm_def]
  change sSup {z : ℝ | ∃ x : β → ℝ, euclideanNorm x = 1 ∧
    z = euclideanNorm (A.mulVec x)} = ‖T‖
  rw [← T.sSup_sphere_eq_norm]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · simpa [Metric.mem_sphere,
        euclideanNorm_eq_norm_toLp_for_reversal] using hx
    · simp [T, euclideanNorm_eq_norm_toLp_for_reversal]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · simpa [Metric.mem_sphere,
        euclideanNorm_eq_norm_toLp_for_reversal] using hx
    · rw [euclideanNorm_eq_norm_toLp_for_reversal]
      change ‖(Matrix.toEuclideanLin A) x‖ =
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖
      exact congrArg norm (Matrix.toLpLin_apply 2 2 A x)

private theorem euclideanOperatorNorm_transpose_for_reversal
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α β ℝ) :
    euclideanOperatorNorm A.transpose = euclideanOperatorNorm A := by
  simp only [euclideanOperatorNorm_eq_l2_opNorm_for_reversal]
  have hreal : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hreal]
  exact Matrix.l2_opNorm_conjTranspose A

/-- Reversing every edge and transposing its rectangular matrix preserves both
the scalar graph contraction and the product of edge operator norms.  This is
the simultaneous-all-edges instance of the orientation-reversal operation in
the bridgeless conversion: loops remain loops, while parallel edges remain
separately indexed by `ε`. -/
theorem graphContraction_reverse_all_edges
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) :
    graphContraction dim dst src (fun e ↦ (M e).transpose) w =
        graphContraction dim src dst M w ∧
      (∏ e, euclideanOperatorNorm (M e).transpose) =
        ∏ e, euclideanOperatorNorm (M e) := by
  constructor
  · simp only [graphContraction, Matrix.transpose_apply]
  · apply Finset.prod_congr rfl
    intro e _
    exact euclideanOperatorNorm_transpose_for_reversal (M e)

end Problem56
