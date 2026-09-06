import Problem56.Definitions

/-!
Finite-dimensional `L2` operator-norm infrastructure for the graph-contraction
part of Problem 5.6.

The public statement layer uses `euclideanOperatorNorm`, defined directly as a
supremum over unit vectors.  Mathlib's rectangular-matrix norm in the
`Matrix.Norms.L2Operator` scope is the norm of the corresponding continuous
linear map between Euclidean spaces.  The first theorem below identifies these
definitions, including the zero-dimensional domain (where the unit sphere is
empty and both suprema are zero).
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

theorem euclideanNorm_eq_norm_toLp {α : Type*} [Fintype α] (x : α → ℝ) :
    euclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem euclideanOperatorNorm_eq_l2_opNorm {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) :
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
    · simpa [Metric.mem_sphere, euclideanNorm_eq_norm_toLp] using hx
    · simp [T, euclideanNorm_eq_norm_toLp]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · simpa [Metric.mem_sphere, euclideanNorm_eq_norm_toLp] using hx
    · rw [euclideanNorm_eq_norm_toLp]
      change ‖(Matrix.toEuclideanLin A) x‖ =
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖
      exact congrArg norm (Matrix.toLpLin_apply 2 2 A x)

theorem euclideanOperatorNorm_nonneg {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) :
    0 ≤ euclideanOperatorNorm A := by
  rw [euclideanOperatorNorm_eq_l2_opNorm]
  exact norm_nonneg A

theorem euclideanNorm_mulVec_le {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) (x : β → ℝ) :
    euclideanNorm (A.mulVec x) ≤
      euclideanOperatorNorm A * euclideanNorm x := by
  rw [euclideanNorm_eq_norm_toLp, euclideanOperatorNorm_eq_l2_opNorm,
    euclideanNorm_eq_norm_toLp]
  simpa using A.l2_opNorm_mulVec (WithLp.toLp 2 x)

theorem euclideanNorm_mulVec_sq_le {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) (x : β → ℝ) :
    euclideanNorm (A.mulVec x) ^ 2 ≤
      euclideanOperatorNorm A ^ 2 * euclideanNorm x ^ 2 := by
  rw [← mul_pow]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) ?_).2
  · exact euclideanNorm_mulVec_le A x
  · exact mul_nonneg (euclideanOperatorNorm_nonneg A) (Real.sqrt_nonneg _)

theorem euclideanOperatorNorm_le_of_energy_bound {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ x : β → ℝ,
      (∑ i, (A.mulVec x i) ^ 2) ≤ C ^ 2 * ∑ j, (x j) ^ 2) :
    euclideanOperatorNorm A ≤ C := by
  rw [euclideanOperatorNorm_eq_l2_opNorm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)),
    mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simpa using henergy (WithLp.ofLp x)

/-- Applying one edge matrix independently to each carried-coordinate fiber
costs at most the square of its Euclidean operator norm in total energy. -/
theorem fiberwise_mulVec_energy_le {α β ζ : Type*}
    [Fintype α] [Fintype β] [Fintype ζ]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) (f : ζ → β → ℝ) :
    (∑ z, euclideanNorm (A.mulVec (f z)) ^ 2) ≤
      euclideanOperatorNorm A ^ 2 * ∑ z, euclideanNorm (f z) ^ 2 := by
  calc
    (∑ z, euclideanNorm (A.mulVec (f z)) ^ 2) ≤
        ∑ z, euclideanOperatorNorm A ^ 2 * euclideanNorm (f z) ^ 2 :=
      Finset.sum_le_sum fun z _ ↦ euclideanNorm_mulVec_sq_le A (f z)
    _ = euclideanOperatorNorm A ^ 2 * ∑ z, euclideanNorm (f z) ^ 2 := by
      rw [Finset.mul_sum]

/-- Summing a nonnegative coordinate energy along an injective diagonal loses
no energy.  This is the finite-sum core of the copy/identification maps. -/
theorem sum_comp_injective_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (∑ j, g (e j)) ≤ ∑ i, g i := by
  let ee : κ ↪ ι := ⟨e, he⟩
  calc
    (∑ j, g (e j)) = ∑ i ∈ Finset.univ.map ee, g i := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), g i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro i _ _
        exact hg i
    _ = ∑ i, g i := rfl

/-- Rewrite a squared finite sum supported on a decidable predicate as a sum
over its subtype. -/
theorem sum_dite_sq_eq_subtype {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (f : {a // P a} → ℝ) :
    (∑ a, (if h : P a then f ⟨a, h⟩ else 0) ^ 2) =
      ∑ a : {a // P a}, (f a) ^ 2 := by
  classical
  let g : α → ℝ := fun a ↦ if h : P a then (f ⟨a, h⟩) ^ 2 else 0
  calc
    (∑ a, (if h : P a then f ⟨a, h⟩ else 0) ^ 2) = ∑ a, g a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P a <;> simp [g, ha]
    _ = ∑ a ∈ (Finset.univ.filter P), g a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P a <;> simp [g, ha]
    _ = ∑ a : {a // P a}, g a.1 := by
      exact Finset.sum_subtype _ (by simp) g
    _ = ∑ a : {a // P a}, (f a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      have ha : P a.1 := a.2
      simp [g, ha]

theorem euclideanNorm_sq_eq_sum {α : Type*} [Fintype α]
    (x : α → ℝ) : euclideanNorm x ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [euclideanNorm_eq_norm_toLp, EuclideanSpace.real_norm_sq_eq]

/-- Heterogeneous coordinate tuples carried by a list of edges.  Lists make
the repeated one-coordinate `L2` argument an ordinary structural induction;
the subsequent graph layer supplies a duplicate-free enumeration. -/
def EdgeListTuple {ε : Type*} (d : ε → ℕ) : List ε → Type
  | [] => PUnit
  | e :: es => Fin (d e) × EdgeListTuple d es

noncomputable instance edgeListTupleFintype {ε : Type*}
    (d : ε → ℕ) (es : List ε) : Fintype (EdgeListTuple d es) := by
  induction es with
  | nil =>
      simp only [EdgeListTuple]
      infer_instance
  | cons e es ih =>
      simp only [EdgeListTuple]
      infer_instance

noncomputable instance edgeListTupleDecidableEq {ε : Type*}
    (d : ε → ℕ) (es : List ε) : DecidableEq (EdgeListTuple d es) := by
  induction es with
  | nil =>
      simp only [EdgeListTuple]
      infer_instance
  | cons e es ih =>
      simp only [EdgeListTuple]
      infer_instance

/-- A heterogeneous edge-list tuple is equivalently a dependent tuple indexed
by positions in the list.  This position representation is useful for later
reindexing and does not identify parallel edges. -/
def edgeListTupleFinEquiv {ε : Type*} (d : ε → ℕ) :
    (es : List ε) →
      EdgeListTuple d es ≃ ((i : Fin es.length) → Fin (d (es.get i)))
  | [] =>
      { toFun := fun _ i ↦ Fin.elim0 i
        invFun := fun _ ↦ PUnit.unit
        left_inv := fun q ↦ by cases q; rfl
        right_inv := fun q ↦ by funext i; exact Fin.elim0 i }
  | e :: es =>
      { toFun := fun q ↦ Fin.cons q.1 (edgeListTupleFinEquiv d es q.2)
        invFun := fun q ↦
          (q 0, (edgeListTupleFinEquiv d es).symm (Fin.tail q))
        left_inv := fun q ↦ by
          rcases q with ⟨q0, qt⟩
          change (q0, (edgeListTupleFinEquiv d es).symm
            (edgeListTupleFinEquiv d es qt)) = (q0, qt)
          rw [(edgeListTupleFinEquiv d es).symm_apply_apply]
        right_inv := fun q ↦ by
          change Fin.cons (q 0)
              (edgeListTupleFinEquiv d es
                ((edgeListTupleFinEquiv d es).symm (Fin.tail q))) = q
          rw [(edgeListTupleFinEquiv d es).apply_symm_apply]
          exact Fin.cons_self_tail q }

@[simp]
theorem edgeListTupleFinEquiv_cons_zero {ε : Type*} (d : ε → ℕ)
    (e : ε) (es : List ε) (a : Fin (d e)) (xs : EdgeListTuple d es) :
    edgeListTupleFinEquiv d (e :: es) (a, xs) 0 = a := rfl

@[simp]
theorem edgeListTupleFinEquiv_cons_succ {ε : Type*} (d : ε → ℕ)
    (e : ε) (es : List ε) (a : Fin (d e)) (xs : EdgeListTuple d es)
    (i : Fin es.length) :
    edgeListTupleFinEquiv d (e :: es) (a, xs) i.succ =
      edgeListTupleFinEquiv d es xs i := rfl

/-- For a duplicate-free list, the same tuple can be indexed by the actual
listed edge subtype rather than by a numerical position. -/
noncomputable def edgeListTupleSubtypeEquiv {ε : Type*} [DecidableEq ε]
    (d : ε → ℕ) (es : List ε) (hes : es.Nodup) :
    EdgeListTuple d es ≃ ((e : {e // e ∈ es}) → Fin (d e.1)) :=
  (edgeListTupleFinEquiv d es).trans
    ((hes.getEquiv es).piCongr fun _ ↦ Equiv.refl _)

@[simp]
theorem edgeListTupleSubtypeEquiv_getEquiv {ε : Type*} [DecidableEq ε]
    (d : ε → ℕ) (es : List ε) (hes : es.Nodup)
    (q : EdgeListTuple d es) (i : Fin es.length) :
    edgeListTupleSubtypeEquiv d es hes q ((hes.getEquiv es) i) =
      edgeListTupleFinEquiv d es q i := by
  let fiber : ∀ i : Fin es.length,
      Fin (d (es.get i)) ≃ Fin (d ((hes.getEquiv es i).1)) :=
    fun _ ↦ Equiv.refl _
  change (Equiv.piCongr
      (W := fun i : Fin es.length ↦ Fin (d (es.get i)))
      (Z := fun e : {e // e ∈ es} ↦ Fin (d e.1))
      (hes.getEquiv es) fiber (edgeListTupleFinEquiv d es q))
        ((hes.getEquiv es) i) = _
  rw [Equiv.piCongr_apply_apply]
  rfl

/-- Apply the transpose-oriented edge matrices independently to the
coordinates of an edge list.  This is the source-to-sink orientation matching
the transpose of the repository's `input × output` graph operator. -/
noncomputable def edgeListAction {ε : Type*}
    (srcDim dstDim : ε → ℕ)
    (M : ∀ e, Matrix (Fin (srcDim e)) (Fin (dstDim e)) ℝ) :
    (es : List ε) →
      (EdgeListTuple srcDim es → ℝ) → EdgeListTuple dstDim es → ℝ
  | [], f, _ => f PUnit.unit
  | e :: es, f, y =>
      ∑ a, M e a y.1 *
        edgeListAction srcDim dstDim M es (fun tail ↦ f (a, tail)) y.2

/-- Repeated fiberwise application costs the product of the individual edge
operator norms.  This is the list-level analytic engine needed by a rank-cut
step; no Kronecker spectral-norm theorem is used. -/
theorem edgeListAction_energy_le {ε : Type*}
    (srcDim dstDim : ε → ℕ)
    (M : ∀ e, Matrix (Fin (srcDim e)) (Fin (dstDim e)) ℝ)
    (es : List ε) (f : EdgeListTuple srcDim es → ℝ) :
    (∑ y, (edgeListAction srcDim dstDim M es f y) ^ 2) ≤
      (es.map (fun e ↦ euclideanOperatorNorm (M e) ^ 2)).prod *
        ∑ x, (f x) ^ 2 := by
  induction es with
  | nil =>
      change (∑ _ : PUnit, f PUnit.unit ^ 2) ≤ 1 * ∑ x : PUnit, (f x) ^ 2
      simp
  | cons e es ih =>
      change (∑ y : Fin (dstDim e) × EdgeListTuple dstDim es,
          (edgeListAction srcDim dstDim M (e :: es) f y) ^ 2) ≤
        ((e :: es).map (fun q ↦ euclideanOperatorNorm (M q) ^ 2)).prod *
          ∑ x : Fin (srcDim e) × EdgeListTuple srcDim es, (f x) ^ 2
      rw [Fintype.sum_prod_type_right]
      have hone := fiberwise_mulVec_energy_le (A := (M e).transpose)
        (f := fun tail a ↦
          edgeListAction srcDim dstDim M es (fun xs ↦ f (a, xs)) tail)
      simp only [euclideanNorm_sq_eq_sum, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply] at hone
      have hnorm : euclideanOperatorNorm (M e).transpose =
          euclideanOperatorNorm (M e) := by
        simp only [euclideanOperatorNorm_eq_l2_opNorm]
        have hreal : (M e).conjTranspose = (M e).transpose := by
          ext i j
          simp [Matrix.conjTranspose_apply]
        rw [← hreal]
        exact Matrix.l2_opNorm_conjTranspose (M e)
      rw [hnorm] at hone
      have hfirst :
          (∑ tail, ∑ b,
              (edgeListAction srcDim dstDim M (e :: es) f (b, tail)) ^ 2) ≤
            euclideanOperatorNorm (M e) ^ 2 *
              ∑ tail, ∑ a,
                (edgeListAction srcDim dstDim M es
                  (fun xs ↦ f (a, xs)) tail) ^ 2 := by
        simpa only [edgeListAction] using hone
      have hsum :
          (∑ z : EdgeListTuple srcDim (e :: es), (f z) ^ 2) =
            ∑ a, ∑ xs, (f (a, xs)) ^ 2 := by
        change (∑ z : Fin (srcDim e) × EdgeListTuple srcDim es, (f z) ^ 2) =
          ∑ a, ∑ xs, (f (a, xs)) ^ 2
        exact Fintype.sum_prod_type _
      calc
        (∑ tail, ∑ b,
            (edgeListAction srcDim dstDim M (e :: es) f (b, tail)) ^ 2) ≤
            euclideanOperatorNorm (M e) ^ 2 *
              ∑ tail, ∑ a,
                (edgeListAction srcDim dstDim M es
                  (fun xs ↦ f (a, xs)) tail) ^ 2 := hfirst
        _ = euclideanOperatorNorm (M e) ^ 2 *
              ∑ a, ∑ tail,
                (edgeListAction srcDim dstDim M es
                  (fun xs ↦ f (a, xs)) tail) ^ 2 := by
            rw [Finset.sum_comm]
        _ ≤ euclideanOperatorNorm (M e) ^ 2 *
              ∑ a, (es.map (fun q ↦ euclideanOperatorNorm (M q) ^ 2)).prod *
                ∑ xs, (f (a, xs)) ^ 2 := by
            gcongr with a
            exact ih (fun xs ↦ f (a, xs))
        _ = ((e :: es).map
              (fun q ↦ euclideanOperatorNorm (M q) ^ 2)).prod *
              ∑ x, (f x) ^ 2 := by
            rw [hsum]
            simp only [List.map_cons, List.prod_cons]
            rw [Finset.mul_sum]
            conv_rhs => rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Explicit coefficient expansion of the recursive edge-list action.  The
position index is intentionally finite and duplicate-sensitive; a later
nodup equivalence reindexes it by actual entering edges. -/
theorem edgeListAction_eq_sum_prod_positions {ε : Type*}
    (srcDim dstDim : ε → ℕ)
    (M : ∀ e, Matrix (Fin (srcDim e)) (Fin (dstDim e)) ℝ)
    (es : List ε) (f : EdgeListTuple srcDim es → ℝ)
    (y : EdgeListTuple dstDim es) :
    edgeListAction srcDim dstDim M es f y =
      ∑ xs : EdgeListTuple srcDim es,
        f xs * ∏ i : Fin es.length,
          M (es.get i)
            (edgeListTupleFinEquiv srcDim es xs i)
            (edgeListTupleFinEquiv dstDim es y i) := by
  induction es with
  | nil =>
      change f PUnit.unit = ∑ xs : PUnit, f xs * 1
      rw [Fintype.sum_unique]
      simp
  | cons e es ih =>
      rcases y with ⟨b, yTail⟩
      change (∑ a, M e a b *
          edgeListAction srcDim dstDim M es
            (fun tail ↦ f (a, tail)) yTail) =
        ∑ xs : Fin (srcDim e) × EdgeListTuple srcDim es,
          f xs * ∏ i : Fin (es.length + 1),
            M ((e :: es).get i)
              (edgeListTupleFinEquiv srcDim (e :: es) xs i)
              (edgeListTupleFinEquiv dstDim (e :: es) (b, yTail) i)
      rw [Fintype.sum_prod_type]
      simp_rw [ih]
      simp only [Fin.prod_univ_succ, List.get_cons_zero,
        edgeListTupleFinEquiv_cons_zero, List.get_cons_succ',
        edgeListTupleFinEquiv_cons_succ]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro xs _
      ring

/-- Duplicate-free lists may be reindexed by their actual edge values.  This
is the form used by the rank-cut consistency predicate. -/
theorem edgeListAction_eq_sum_prod_subtype {ε : Type*} [DecidableEq ε]
    (srcDim dstDim : ε → ℕ)
    (M : ∀ e, Matrix (Fin (srcDim e)) (Fin (dstDim e)) ℝ)
    (es : List ε) (hes : es.Nodup)
    (f : EdgeListTuple srcDim es → ℝ) (y : EdgeListTuple dstDim es) :
    edgeListAction srcDim dstDim M es f y =
      ∑ xs : EdgeListTuple srcDim es,
        f xs * ∏ e : {e // e ∈ es},
          M e.1
            (edgeListTupleSubtypeEquiv srcDim es hes xs e)
            (edgeListTupleSubtypeEquiv dstDim es hes y e) := by
  rw [edgeListAction_eq_sum_prod_positions]
  apply Finset.sum_congr rfl
  intro xs _
  congr 1
  apply Fintype.prod_equiv (hes.getEquiv es)
  intro i
  simp only [edgeListTupleSubtypeEquiv_getEquiv]
  change M (es.get i)
      (edgeListTupleFinEquiv srcDim es xs i)
      (edgeListTupleFinEquiv dstDim es y i) = _
  rfl

/-- Abstract adjacent-cut contraction after the diagonal copy/identification
stage has produced `prepared`.  After all new edge matrices act independently,
`post` injects the new cut into that expanded output array. -/
theorem rankCutStepEnergy_le_of_factorization
    {ε oldIndex newIndex ζ : Type*}
    [Fintype oldIndex] [Fintype newIndex] [Fintype ζ]
    [DecidableEq oldIndex] [DecidableEq newIndex]
    (srcDim dstDim : ε → ℕ)
    (M : ∀ e, Matrix (Fin (srcDim e)) (Fin (dstDim e)) ℝ)
    (es : List ε)
    (fOld : oldIndex → ℝ) (fNew : newIndex → ℝ)
    (prepared : ζ × EdgeListTuple srcDim es → ℝ)
    (post : newIndex → ζ × EdgeListTuple dstDim es)
    (hpost : Function.Injective post)
    (hprepared : (∑ q, (prepared q) ^ 2) ≤ ∑ i, (fOld i) ^ 2)
    (hfactor : ∀ j,
      fNew j = edgeListAction srcDim dstDim M es
        (fun xs ↦ prepared ((post j).1, xs)) (post j).2) :
    (∑ j, (fNew j) ^ 2) ≤
      (es.map (fun e ↦ euclideanOperatorNorm (M e) ^ 2)).prod *
        ∑ i, (fOld i) ^ 2 := by
  classical
  let edgeFactor : ℝ :=
    (es.map (fun e ↦ euclideanOperatorNorm (M e) ^ 2)).prod
  let expanded : ζ × EdgeListTuple dstDim es → ℝ := fun q ↦
    edgeListAction srcDim dstDim M es
      (fun xs ↦ prepared (q.1, xs)) q.2
  have hrestrict : (∑ j, (fNew j) ^ 2) ≤ ∑ q, (expanded q) ^ 2 := by
    rw [show (∑ j, (fNew j) ^ 2) = ∑ j, (expanded (post j)) ^ 2 by
      apply Finset.sum_congr rfl
      intro j _
      rw [hfactor j]]
    exact sum_comp_injective_le post hpost (fun q ↦ (expanded q) ^ 2)
      fun q ↦ sq_nonneg (expanded q)
  have hedge : (∑ q, (expanded q) ^ 2) ≤
      edgeFactor * ∑ q : ζ × EdgeListTuple srcDim es, (prepared q) ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ z, ∑ y, (expanded (z, y)) ^ 2) ≤
          ∑ z, edgeFactor * ∑ xs, (prepared (z, xs)) ^ 2 := by
        apply Finset.sum_le_sum
        intro z _
        exact edgeListAction_energy_le srcDim dstDim M es
          (fun xs ↦ prepared (z, xs))
      _ = edgeFactor * ∑ z, ∑ xs, (prepared (z, xs)) ^ 2 := by
        rw [Finset.mul_sum]
  have hedgeFactor : 0 ≤ edgeFactor := by
    dsimp only [edgeFactor]
    apply List.prod_nonneg
    intro a ha
    simp only [List.mem_map] at ha
    rcases ha with ⟨e, _, rfl⟩
    exact sq_nonneg _
  calc
    (∑ j, (fNew j) ^ 2) ≤ ∑ q, (expanded q) ^ 2 := hrestrict
    _ ≤ edgeFactor *
        ∑ q : ζ × EdgeListTuple srcDim es, (prepared q) ^ 2 := hedge
    _ ≤ edgeFactor * ∑ i, (fOld i) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hprepared hedgeFactor

theorem diagonal_coordinate_energy_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e) (x : ι → ℝ) :
    (∑ j, (x (e j)) ^ 2) ≤ ∑ i, (x i) ^ 2 := by
  exact sum_comp_injective_le e he (fun i ↦ (x i) ^ 2) fun i ↦ sq_nonneg (x i)

/-- A vertex label embeds injectively into the tuple in which all incident
ports carry that same label, provided there is at least one port.  Input and
output half-edges supply the endpoint port in the level-set construction. -/
theorem constantTuple_injective {ι κ : Type*} [Nonempty κ] :
    Function.Injective (fun i : ι ↦ fun _ : κ ↦ i) := by
  intro i j h
  let k : κ := Classical.choice inferInstance
  exact congrFun h k

/-- The matrix which restricts a coefficient array to coordinates in an
injectively parametrized diagonal. -/
def coordinateRestrictionMatrix {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] (e : κ → ι) : Matrix κ ι ℝ :=
  fun j i ↦ if e j = i then 1 else 0

@[simp]
theorem coordinateRestrictionMatrix_mulVec {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    (e : κ → ι) (x : ι → ℝ) (j : κ) :
    (coordinateRestrictionMatrix e).mulVec x j = x (e j) := by
  simp [coordinateRestrictionMatrix, Matrix.mulVec, dotProduct]

theorem coordinateRestriction_energy_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e) (x : ι → ℝ) :
    euclideanNorm ((coordinateRestrictionMatrix e).mulVec x) ^ 2 ≤
      euclideanNorm x ^ 2 := by
  rw [euclideanNorm_eq_norm_toLp, euclideanNorm_eq_norm_toLp,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simpa using diagonal_coordinate_energy_le e he x

theorem coordinateRestriction_operatorNorm_le_one {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e) :
    euclideanOperatorNorm (coordinateRestrictionMatrix e) ≤ 1 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simpa using diagonal_coordinate_energy_le e he (WithLp.ofLp x)

/-- The adjoint coordinate-copy map has the same contraction bound. -/
def coordinateEmbeddingMatrix {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] (e : κ → ι) : Matrix ι κ ℝ :=
  (coordinateRestrictionMatrix e).transpose

theorem coordinateEmbedding_operatorNorm_le_one {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ → ι) (he : Function.Injective e) :
    euclideanOperatorNorm (coordinateEmbeddingMatrix e) ≤ 1 := by
  rw [coordinateEmbeddingMatrix, euclideanOperatorNorm_eq_l2_opNorm]
  have hreal : (coordinateRestrictionMatrix e).conjTranspose =
      (coordinateRestrictionMatrix e).transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hreal, Matrix.l2_opNorm_conjTranspose]
  simpa only [euclideanOperatorNorm_eq_l2_opNorm] using
    coordinateRestriction_operatorNorm_le_one e he

theorem euclideanOperatorNorm_mul_le {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ) :
    euclideanOperatorNorm (A * B) ≤
      euclideanOperatorNorm A * euclideanOperatorNorm B := by
  simp only [euclideanOperatorNorm_eq_l2_opNorm]
  exact Matrix.l2_opNorm_mul A B

theorem euclideanOperatorNorm_transpose {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) :
    euclideanOperatorNorm A.transpose = euclideanOperatorNorm A := by
  simp only [euclideanOperatorNorm_eq_l2_opNorm]
  have hreal : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hreal]
  exact Matrix.l2_opNorm_conjTranspose A

theorem euclideanOperatorNorm_eq_zero_of_isEmpty_domain {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [IsEmpty β] (A : Matrix α β ℝ) :
    euclideanOperatorNorm A = 0 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm, Matrix.l2_opNorm_def]
  simp

/-- If one vertex space is zero-dimensional, the dependent type of full graph
labels is empty, so every entry of the graph operator is an empty sum. -/
theorem graphOperator_eq_zero_of_exists_zero_dim
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hzero : ∃ v, dim v = 0) :
    graphOperator dim src dst M input output = 0 := by
  rcases hzero with ⟨v, hv⟩
  let _ : IsEmpty (∀ w, Fin (dim w)) :=
    ⟨fun labels ↦ Fin.elim0 (by simpa [hv] using labels v)⟩
  classical
  ext a b
  simp [graphOperator]

/-- The zero-dimensional branch of the graph-operator estimate is immediate.
This is kept local to the proof layer rather than added to the public I04
signature. -/
theorem graphOperator_norm_le_edge_product_of_exists_zero_dim
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hzero : ∃ v, dim v = 0) :
    euclideanOperatorNorm (graphOperator dim src dst M input output) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  rw [graphOperator_eq_zero_of_exists_zero_dim dim src dst M input output hzero]
  have hleft : euclideanOperatorNorm
      (0 : Matrix (Fin (dim input)) (Fin (dim output)) ℝ) = 0 := by
    simp only [euclideanOperatorNorm_eq_l2_opNorm, norm_zero]
  rw [hleft]
  exact Finset.prod_nonneg fun e _ ↦ euclideanOperatorNorm_nonneg (M e)

/-- Negating the zero-dimensional branch supplies inhabited positive fibers
without changing any public graph-operator hypothesis. -/
theorem all_dim_pos_of_not_exists_zero {ι : Type*} (dim : ι → ℕ)
    (hzero : ¬ ∃ v, dim v = 0) : ∀ v, 0 < dim v := by
  intro v
  have hv : dim v ≠ 0 := fun h ↦ hzero ⟨v, h⟩
  omega

theorem euclideanOperatorNorm_one_le {α : Type*}
    [Fintype α] [DecidableEq α] :
    euclideanOperatorNorm (1 : Matrix α α ℝ) ≤ 1 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm]
  rw [Matrix.cstar_norm_def]
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

/-! ### A finite topological rank for the directed graph -/

/-- The strict predecessors of `v`, measured in the transitive closure of a
finite relation. -/
noncomputable def strictPredecessors {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop) (v : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun u ↦ Relation.TransGen r u v

/-- A source-faithful level function for a finite DAG: the number of strict
predecessors.  Unlike a `Fin (card ι)` enumeration, this definition also has
the right type when `ι` is empty. -/
noncomputable def finiteDAGRank {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop) (v : ι) : ℕ :=
  (strictPredecessors r v).card

theorem finiteDAGRank_le_card {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop) (v : ι) :
    finiteDAGRank r v ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Every relation edge strictly increases the predecessor-cardinality rank.
This supplies the level structure needed by the Mingo--Speicher factorization
without importing a graph-specific topological-sort API. -/
theorem finiteDAGRank_lt_of_rel {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen r v v)
    {u v : ι} (huv : r u v) :
    finiteDAGRank r u < finiteDAGRank r v := by
  classical
  apply Finset.card_lt_card
  have hsub : strictPredecessors r u ⊆ strictPredecessors r v := by
    intro x hx
    simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans (Relation.TransGen.single huv)
  apply (Finset.ssubset_iff_of_subset hsub).2
  refine ⟨u, ?_, ?_⟩
  · simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.TransGen.single huv
  · simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hacyclic u

theorem finiteDAGRank_lt_of_transGen {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen r v v)
    {u v : ι} (huv : Relation.TransGen r u v) :
    finiteDAGRank r u < finiteDAGRank r v := by
  classical
  apply Finset.card_lt_card
  have hsub : strictPredecessors r u ⊆ strictPredecessors r v := by
    intro x hx
    simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans huv
  apply (Finset.ssubset_iff_of_subset hsub).2
  refine ⟨u, ?_, ?_⟩
  · simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact huv
  · simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hacyclic u

noncomputable def mingoDAGRank {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (v : ι) : ℕ :=
  finiteDAGRank (directedAdjacent src dst) v

theorem MingoAdmissibleDAG.edge_rank_lt
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) (e : ε) :
    mingoDAGRank src dst (src e) < mingoDAGRank src dst (dst e) := by
  apply finiteDAGRank_lt_of_rel (directedAdjacent src dst) hdag.1
  exact ⟨e, rfl, rfl⟩

theorem MingoAdmissibleDAG.input_rank_eq_zero
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output) :
    mingoDAGRank src dst input = 0 := by
  classical
  rw [mingoDAGRank, finiteDAGRank, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.2
  intro v hv
  simp only [strictPredecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hdag.2.1 v with hvEq | hiv
  · subst v
    exact hdag.1 _ hv
  · exact hdag.1 input (hiv.trans hv)

theorem MingoAdmissibleDAG.rank_lt_output_of_ne
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {v : ι} (hv : v ≠ output) :
    mingoDAGRank src dst v < mingoDAGRank src dst output := by
  apply finiteDAGRank_lt_of_transGen (directedAdjacent src dst) hdag.1
  rcases hdag.2.2 v with h | h
  · exact (hv h).elim
  · exact h

/-- Every non-input vertex has an incoming edge.  The chosen edge remains an
edge value (rather than an endpoint pair), so parallel edges are preserved. -/
theorem MingoAdmissibleDAG.exists_incoming_edge_of_ne_input
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {v : ι} (hv : v ≠ input) :
    ∃ e, dst e = v := by
  rcases hdag.2.1 v with hvi | hiv
  · exact (hv hvi).elim
  · rcases Relation.TransGen.tail'_iff.1 hiv with ⟨u, _, huv⟩
    rcases huv with ⟨e, _, hedst⟩
    exact ⟨e, hedst⟩

/-- Every non-output vertex has an outgoing edge, again retaining the actual
edge identifier in the presence of multiple edges. -/
theorem MingoAdmissibleDAG.exists_outgoing_edge_of_ne_output
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {v : ι} (hv : v ≠ output) :
    ∃ e, src e = v := by
  rcases hdag.2.2 v with hvo | hvo
  · exact (hv hvo).elim
  · rcases Relation.TransGen.head'_iff.1 hvo with ⟨w, hvw, _⟩
    rcases hvw with ⟨e, hesrc, _⟩
    exact ⟨e, hesrc⟩

/-- A level vertex other than the input has an incoming old-cut anchor whose
source lies on a strictly earlier level. -/
theorem MingoAdmissibleDAG.exists_incoming_rank_anchor
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {rank : ι → ℕ}
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {v : ι} {k : ℕ} (hvk : rank v = k) (hv : v ≠ input) :
    ∃ e, dst e = v ∧ rank (src e) < k := by
  rcases hdag.exists_incoming_edge_of_ne_input src dst input output hv with
    ⟨e, hedst⟩
  refine ⟨e, hedst, ?_⟩
  simpa [hedst, hvk] using hedge e

/-- A level vertex other than the output has a newly entering edge anchor
whose target lies on a strictly later level. -/
theorem MingoAdmissibleDAG.exists_outgoing_rank_anchor
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    {rank : ι → ℕ}
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {v : ι} {k : ℕ} (hvk : rank v = k) (hv : v ≠ output) :
    ∃ e, src e = v ∧ k < rank (dst e) := by
  rcases hdag.exists_outgoing_edge_of_ne_output src dst input output hv with
    ⟨e, hesrc⟩
  refine ⟨e, hesrc, ?_⟩
  simpa [hesrc, hvk] using hedge e

/-- No directed edge can have both endpoints on one rank level. -/
theorem no_edge_with_endpoints_on_same_rank
    {ι ε : Type*} (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (e : ε) : rank (src e) ≠ rank (dst e) := by
  exact ne_of_lt (hedge e)

/-! ### Rank cuts and edge accounting -/

noncomputable def rankProcessedVertices {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) (k : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter fun v ↦ rank v < k

noncomputable def rankLevelVertices {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) (k : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter fun v ↦ rank v = k

noncomputable def rankActiveEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact Finset.univ.filter fun e ↦ rank (src e) < k ∧ k ≤ rank (dst e)

noncomputable def rankEnteringEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact Finset.univ.filter fun e ↦ rank (src e) = k

noncomputable def rankLeavingEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact Finset.univ.filter fun e ↦ rank (dst e) = k

noncomputable def rankIntroducedEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact Finset.univ.filter fun e ↦ rank (src e) < k

noncomputable def rankCompletedEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) : Finset ε := by
  classical
  exact Finset.univ.filter fun e ↦ rank (dst e) < k

@[simp]
theorem mem_rankProcessedVertices {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) (k : ℕ) (v : ι) :
    v ∈ rankProcessedVertices rank k ↔ rank v < k := by
  classical
  simp [rankProcessedVertices]

@[simp]
theorem mem_rankLevelVertices {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) (k : ℕ) (v : ι) :
    v ∈ rankLevelVertices rank k ↔ rank v = k := by
  classical
  simp [rankLevelVertices]

@[simp]
theorem mem_rankActiveEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankActiveEdges rank src dst k ↔
      rank (src e) < k ∧ k ≤ rank (dst e) := by
  classical
  simp [rankActiveEdges]

@[simp]
theorem mem_rankEnteringEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankEnteringEdges rank src k ↔ rank (src e) = k := by
  classical
  simp [rankEnteringEdges]

@[simp]
theorem mem_rankLeavingEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankLeavingEdges rank dst k ↔ rank (dst e) = k := by
  classical
  simp [rankLeavingEdges]

@[simp]
theorem mem_rankIntroducedEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankIntroducedEdges rank src k ↔ rank (src e) < k := by
  classical
  simp [rankIntroducedEdges]

@[simp]
theorem mem_rankCompletedEdges {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (k : ℕ) (e : ε) :
    e ∈ rankCompletedEdges rank dst k ↔ rank (dst e) < k := by
  classical
  simp [rankCompletedEdges]

theorem rankProcessedVertices_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rank : ι → ℕ) (k : ℕ) :
    rankProcessedVertices rank (k + 1) =
      rankProcessedVertices rank k ∪ rankLevelVertices rank k := by
  classical
  ext v
  simp
  omega

@[simp]
theorem rankProcessedVertices_zero {ι : Type*} [Fintype ι]
    (rank : ι → ℕ) : rankProcessedVertices rank 0 = ∅ := by
  classical
  ext v
  simp

@[simp]
theorem rankActiveEdges_zero {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) :
    rankActiveEdges rank src dst 0 = ∅ := by
  classical
  ext e
  simp

@[simp]
theorem rankCompletedEdges_zero {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) :
    rankCompletedEdges rank dst 0 = ∅ := by
  classical
  ext e
  simp

theorem mem_rankActiveEdges_succ_iff {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) (e : ε)
    (hedge : rank (src e) < rank (dst e)) :
    e ∈ rankActiveEdges rank src dst (k + 1) ↔
      (e ∈ rankActiveEdges rank src dst k ∧ k < rank (dst e)) ∨
        e ∈ rankEnteringEdges rank src k := by
  simp only [mem_rankActiveEdges, mem_rankEnteringEdges]
  omega

/-- At one rank step, precisely the edges targeting this level disappear and
precisely the edges sourced at this level appear. -/
theorem rankActiveEdges_succ {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :
    rankActiveEdges rank src dst (k + 1) =
      (rankActiveEdges rank src dst k \ rankLeavingEdges rank dst k) ∪
        rankEnteringEdges rank src k := by
  classical
  ext e
  rw [mem_rankActiveEdges_succ_iff rank src dst k e (hedge e)]
  simp only [Finset.mem_union, Finset.mem_sdiff, mem_rankActiveEdges,
    mem_rankLeavingEdges, mem_rankEnteringEdges]
  omega

/-- Every introduced edge occurs exactly in one of the two factors of the
partial contraction: it is either already completed or it is carried by the
active cut. -/
theorem rankIntroducedEdges_partition {ι ε : Type*}
    [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :
    rankIntroducedEdges rank src k =
      rankCompletedEdges rank dst k ∪ rankActiveEdges rank src dst k := by
  classical
  ext e
  simp only [mem_rankIntroducedEdges, Finset.mem_union,
    mem_rankCompletedEdges, mem_rankActiveEdges]
  specialize hedge e
  omega

theorem rankCompletedEdges_disjoint_active {ι ε : Type*}
    [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) :
    Disjoint (rankCompletedEdges rank dst k)
      (rankActiveEdges rank src dst k) := by
  classical
  rw [Finset.disjoint_left]
  intro e heComplete heActive
  simp only [mem_rankCompletedEdges] at heComplete
  simp only [mem_rankActiveEdges] at heActive
  omega

theorem rankEnteringEdges_disjoint_leaving {ι ε : Type*}
    [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :
    Disjoint (rankEnteringEdges rank src k)
      (rankLeavingEdges rank dst k) := by
  classical
  rw [Finset.disjoint_left]
  intro e heIn heOut
  simp only [mem_rankEnteringEdges] at heIn
  simp only [mem_rankLeavingEdges] at heOut
  have he := hedge e
  omega

theorem edge_enters_active_cut {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (e : ε)
    (hedge : rank (src e) < rank (dst e)) :
    e ∈ rankActiveEdges rank src dst (rank (src e) + 1) := by
  simp only [mem_rankActiveEdges]
  omega

theorem edge_leaves_active_cut {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src dst : ε → ι) (e : ε)
    (hedge : rank (src e) < rank (dst e)) :
    e ∈ rankActiveEdges rank src dst (rank (dst e)) ∧
      e ∉ rankActiveEdges rank src dst (rank (dst e) + 1) := by
  simp only [mem_rankActiveEdges]
  omega

theorem edge_has_unique_entering_level {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (e : ε) :
    ∃! k, e ∈ rankEnteringEdges rank src k := by
  classical
  refine ⟨rank (src e), by simp, ?_⟩
  intro k hk
  exact ((mem_rankEnteringEdges rank src k e).1 hk).symm

theorem edge_has_unique_leaving_level {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (dst : ε → ι) (e : ε) :
    ∃! k, e ∈ rankLeavingEdges rank dst k := by
  classical
  refine ⟨rank (dst e), by simp, ?_⟩
  intro k hk
  exact ((mem_rankLeavingEdges rank dst k e).1 hk).symm

/-- The carried coefficient coordinates at a rank cut.  An active edge has
already had its matrix applied, so it carries a coordinate in its target
vertex space.  Vertex dimensions may vary and parallel edges remain distinct. -/
abbrev RankCutActiveIndex {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) :=
  (e : {e // e ∈ rankActiveEdges rank src dst k}) → Fin (dim (dst e.1))

abbrev RankCutCoefficientArray {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ) :=
  RankCutActiveIndex dim rank src dst k → ℝ

/-- Vertex labels that have actually been summed at the cut. -/
abbrev RankCutProcessedLabels {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ) :=
  (v : {v // v ∈ rankProcessedVertices rank k}) → Fin (dim v.1)

/-- Labels processed at cut `k+1` split uniquely into labels already processed
at cut `k` and labels on the current rank level. -/
noncomputable def rankProcessedLabelsSuccEquiv
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ) :
    RankCutProcessedLabels dim rank (k + 1) ≃
      RankCutProcessedLabels dim rank k ×
        ((v : {v // v ∈ rankLevelVertices rank k}) → Fin (dim v.1)) := by
  classical
  refine
    { toFun := fun labels ↦
        (fun v ↦ labels ⟨v.1, by
            rw [mem_rankProcessedVertices]
            have hv := (mem_rankProcessedVertices rank k v.1).1 v.2
            omega⟩,
          fun v ↦ labels ⟨v.1, by
            rw [mem_rankProcessedVertices]
            have hv := (mem_rankLevelVertices rank k v.1).1 v.2
            omega⟩)
      invFun := fun q v ↦ if hv : rank v.1 < k then
          q.1 ⟨v.1, by simpa only [mem_rankProcessedVertices] using hv⟩
        else
          q.2 ⟨v.1, by
            rw [mem_rankLevelVertices]
            have hvSucc := (mem_rankProcessedVertices rank (k + 1) v.1).1 v.2
            omega⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro labels
    funext v
    by_cases hv : rank v.1 < k <;>
      simp only [hv, ↓reduceDIte]
  · rintro ⟨oldLabels, levelLabels⟩
    apply Prod.ext
    · funext v
      have hv := (mem_rankProcessedVertices rank k v.1).1 v.2
      simp only [hv, ↓reduceDIte]
    · funext v
      have hv := (mem_rankLevelVertices rank k v.1).1 v.2
      have hnlt : ¬rank v.1 < k := by omega
      simp only [hnlt, ↓reduceDIte]

noncomputable def processedEndpointConstraint
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (labels : RankCutProcessedLabels dim rank k)
    (v : ι) (i : Fin (dim v)) : ℝ := by
  classical
  exact if hv : v ∈ rankProcessedVertices rank k then
    if labels ⟨v, hv⟩ = i then 1 else 0
  else 1

/-- The coefficient-array value after summing the processed vertices.  Each
completed edge contributes its full matrix entry; each active edge contributes
its matrix entry with the target coordinate supplied by the cut array.  This
is the source-faithful algebraic invariant to be related across adjacent cuts. -/
noncomputable def rankPartialContraction
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ)
    (a : Fin (dim input)) (b : Fin (dim output))
    (boundary : RankCutActiveIndex dim rank src dst k) : ℝ := by
  classical
  exact ∑ labels : RankCutProcessedLabels dim rank k,
    processedEndpointConstraint dim rank k labels input a *
    processedEndpointConstraint dim rank k labels output b *
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
        (boundary e)

theorem rankPartialContraction_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (a : Fin (dim input)) (b : Fin (dim output))
    (boundary : RankCutActiveIndex dim rank src dst 0) :
    rankPartialContraction dim rank src dst M hedge input output 0 a b boundary = 1 := by
  classical
  let _ : IsEmpty {v // v ∈ rankProcessedVertices rank 0} :=
    ⟨fun v ↦ by simpa using v.2⟩
  let _ : IsEmpty {e // e ∈ rankCompletedEdges rank dst 0} :=
    ⟨fun e ↦ by simpa using e.2⟩
  let _ : IsEmpty {e // e ∈ rankActiveEdges rank src dst 0} :=
    ⟨fun e ↦ by simpa using e.2⟩
  rw [rankPartialContraction, Fintype.sum_unique]
  simp [processedEndpointConstraint]

noncomputable def rankCutEnergy {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ)
    (f : RankCutCoefficientArray dim rank src dst k) : ℝ := by
  classical
  exact ∑ a, (f a) ^ 2

theorem rankCutEnergy_nonneg {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι) (k : ℕ)
    (f : RankCutCoefficientArray dim rank src dst k) :
    0 ≤ rankCutEnergy dim rank src dst k f := by
  classical
  rw [rankCutEnergy]
  exact Finset.sum_nonneg fun a _ ↦ sq_nonneg (f a)

/-! ### Endpoint-aware rank-cut states

The source-to-sink traversal naturally estimates the transpose of the
repository's `input × output` matrix.  The input port is present until the
input vertex is processed, active edges form the internal boundary, and the
output port is present after the output vertex is processed.  Encoding all
three cases as a dependent product avoids choosing dummy endpoint coordinates
and remains meaningful when an endpoint dimension is zero. -/

inductive RankCutPort (ε : Type*) where
  | input
  | edge (e : ε)
  | output
  deriving DecidableEq, Fintype

def rankCutPortDim {ι ε : Type*} (dim : ι → ℕ)
    (dst : ε → ι) (input output : ι) : RankCutPort ε → ℕ
  | .input => dim input
  | .edge e => dim (dst e)
  | .output => dim output

def rankCutPortActive {ι ε : Type*} (rank : ι → ℕ)
    (src dst : ε → ι) (input output : ι) (k : ℕ) :
    RankCutPort ε → Prop
  | .input => k ≤ rank input
  | .edge e => rank (src e) < k ∧ k ≤ rank (dst e)
  | .output => rank output < k

abbrev EndpointAwareRankCutIndex {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) :=
  (p : {p // rankCutPortActive rank src dst input output k p}) →
    Fin (rankCutPortDim dim dst input output p.1)

abbrev EndpointAwareRankCutArray {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) :=
  EndpointAwareRankCutIndex dim rank src dst input output k → ℝ

noncomputable def endpointAwareRankCutState
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) : ℝ := by
  classical
  exact ∑ labels : RankCutProcessedLabels dim rank k,
    (if hinput : rank input < k then
      x (labels ⟨input, by simpa using hinput⟩)
    else
      x (boundary ⟨RankCutPort.input, by
        simp only [rankCutPortActive]
        omega⟩)) *
    (if houtput : rank output < k then
      if labels ⟨output, by simpa using houtput⟩ =
          boundary ⟨RankCutPort.output, by
            simpa only [rankCutPortActive] using houtput⟩ then 1 else 0
    else 1) *
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

theorem endpointAwareRankCutState_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output 0) :
    endpointAwareRankCutState dim rank src dst M hedge input output 0 x boundary =
      x (boundary ⟨RankCutPort.input, by simp [rankCutPortActive]⟩) := by
  classical
  let _ : IsEmpty {v // v ∈ rankProcessedVertices rank 0} :=
    ⟨fun v ↦ by simpa using v.2⟩
  let _ : IsEmpty {e // e ∈ rankCompletedEdges rank dst 0} :=
    ⟨fun e ↦ by simpa using e.2⟩
  let _ : IsEmpty {e // e ∈ rankActiveEdges rank src dst 0} :=
    ⟨fun e ↦ by simpa using e.2⟩
  rw [endpointAwareRankCutState, Fintype.sum_unique]
  simp

noncomputable def endpointAwareRankCutEnergy
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (f : EndpointAwareRankCutArray dim rank src dst input output k) : ℝ := by
  classical
  exact ∑ boundary, (f boundary) ^ 2

theorem endpointAwareRankCutEnergy_nonneg
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (f : EndpointAwareRankCutArray dim rank src dst input output k) :
    0 ≤ endpointAwareRankCutEnergy dim rank src dst input output k f := by
  classical
  rw [endpointAwareRankCutEnergy]
  exact Finset.sum_nonneg fun boundary _ ↦ sq_nonneg (f boundary)

noncomputable def rankEnteringEdgeList {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) : List ε :=
  (rankEnteringEdges rank src k).toList

theorem rankEnteringEdgeList_nodup {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) :
    (rankEnteringEdgeList rank src k).Nodup := by
  classical
  exact Finset.nodup_toList _

theorem rankEnteringEdgeList_toFinset {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) :
    (rankEnteringEdgeList rank src k).toFinset =
      rankEnteringEdges rank src k := by
  classical
  exact Finset.toList_toFinset _

theorem rankEnteringEdgeList_prod {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) (f : ε → ℝ) :
    ((rankEnteringEdgeList rank src k).map f).prod =
      ∏ e ∈ rankEnteringEdges rank src k, f e := by
  classical
  rw [← List.prod_toFinset f (rankEnteringEdgeList_nodup rank src k),
    rankEnteringEdgeList_toFinset]

/-- Multiplying the factors for all entering edges level by level counts each
edge exactly once, provided the chosen terminal cut lies above every source
rank. -/
theorem prod_rankEnteringEdges_range
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (f : ε → ℝ) (K : ℕ)
    (hbound : ∀ e, rank (src e) < K) :
    (∏ k ∈ Finset.range K,
        ∏ e ∈ rankEnteringEdges rank src k, f e) = ∏ e, f e := by
  classical
  have hpartial : ∀ L : ℕ,
      (∏ k ∈ Finset.range L,
          ∏ e ∈ rankEnteringEdges rank src k, f e) =
        ∏ e ∈ Finset.univ.filter (fun e ↦ rank (src e) < L), f e := by
    intro L
    induction L with
    | zero => simp [rankEnteringEdges]
    | succ L ih =>
        rw [Finset.prod_range_succ, ih]
        have hunion :
            Finset.univ.filter (fun e ↦ rank (src e) < L + 1) =
              Finset.univ.filter (fun e ↦ rank (src e) < L) ∪
                rankEnteringEdges rank src L := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, mem_rankEnteringEdges]
          omega
        have hdisjoint : Disjoint
            (Finset.univ.filter (fun e ↦ rank (src e) < L))
            (rankEnteringEdges rank src L) := by
          rw [Finset.disjoint_left]
          intro e heLt heEq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heLt
          simp only [mem_rankEnteringEdges] at heEq
          omega
        rw [hunion, Finset.prod_union hdisjoint]
  rw [hpartial K]
  have hall : Finset.univ.filter (fun e ↦ rank (src e) < K) = Finset.univ := by
    ext e
    simp [hbound e]
  rw [hall]

/-- Ports at cut `k+1` which are not the target ports of edges entering at
level `k`.  Endpoint ports and persistent edge ports are carried unchanged. -/
def rankCutCarriedPortActive {ι ε : Type*} (rank : ι → ℕ)
    (src dst : ε → ι) (input output : ι) (k : ℕ) :
    RankCutPort ε → Prop
  | .input => rankCutPortActive rank src dst input output (k + 1) .input
  | .edge e =>
      rankCutPortActive rank src dst input output (k + 1) (.edge e) ∧
        rank (src e) < k
  | .output => rankCutPortActive rank src dst input output (k + 1) .output

theorem rankCutCarriedPortActive.active
    {ι ε : Type*} (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) {p : RankCutPort ε}
    (hp : rankCutCarriedPortActive rank src dst input output k p) :
    rankCutPortActive rank src dst input output (k + 1) p := by
  cases p with
  | input => exact hp
  | edge e => exact hp.1
  | output => exact hp

/-- Heterogeneous coordinates which persist from the old cut to the new cut,
including endpoint ports. -/
abbrev EndpointAwareRankCutCarriedIndex
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) :=
  (p : {p // rankCutCarriedPortActive rank src dst input output k p}) →
    Fin (rankCutPortDim dim dst input output p.1)

noncomputable instance endpointAwareRankCutCarriedIndexFintype
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) :
    Fintype (EndpointAwareRankCutCarriedIndex dim rank src dst input output k) := by
  classical
  exact Fintype.ofFinite _

/-- Coordinates indexed by the actual entering-edge subtype. -/
abbrev RankEnteringEdgeIndex
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src endpoint : ε → ι) (k : ℕ) :=
  (e : {e // e ∈ rankEnteringEdges rank src k}) → Fin (dim (endpoint e.1))

/-- The list membership subtype used by `EdgeListTuple` is the same finite
index set as the entering-edge finset. -/
def rankEnteringEdgeListSubtypeEquiv
    {ι ε : Type*} [Fintype ε]
    (rank : ι → ℕ) (src : ε → ι) (k : ℕ) :
    {e // e ∈ rankEnteringEdgeList rank src k} ≃
      {e // e ∈ rankEnteringEdges rank src k} := by
  classical
  exact
    { toFun := fun e ↦ ⟨e.1, by simpa [rankEnteringEdgeList] using e.2⟩
      invFun := fun e ↦ ⟨e.1, by simpa [rankEnteringEdgeList] using e.2⟩
      left_inv := fun e ↦ by cases e; rfl
      right_inv := fun e ↦ by cases e; rfl }

/-- Reindex the fixed edge-list tuple by the duplicate-free entering-edge
subtype.  This is the bridge between recursive edge action and graph ports. -/
noncomputable def rankEnteringEdgeTupleEquiv
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src endpoint : ε → ι) (k : ℕ) :
    EdgeListTuple (fun e ↦ dim (endpoint e))
        (rankEnteringEdgeList rank src k) ≃
      RankEnteringEdgeIndex dim rank src endpoint k := by
  classical
  exact
    (edgeListTupleSubtypeEquiv (fun e ↦ dim (endpoint e))
      (rankEnteringEdgeList rank src k)
      (rankEnteringEdgeList_nodup rank src k)).trans
      ((rankEnteringEdgeListSubtypeEquiv rank src k).piCongr
        fun _ ↦ Equiv.refl _)

/-- Restrict a new-cut boundary to its stable carried ports. -/
def endpointAwareSuccBoundaryToCarried
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
    EndpointAwareRankCutCarriedIndex dim rank src dst input output k :=
  fun p ↦ boundary ⟨p.1,
    rankCutCarriedPortActive.active rank src dst input output k p.2⟩

/-- Restrict a new-cut boundary to the target coordinates of entering edges. -/
def endpointAwareSuccBoundaryToEntering
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
    RankEnteringEdgeIndex dim rank src dst k :=
  fun e ↦ boundary ⟨RankCutPort.edge e.1, by
    simp only [rankCutPortActive]
    have heq := (mem_rankEnteringEdges rank src k e.1).1 e.2
    have hlt := hedge e.1
    omega⟩

/-- Concrete post-edge-action representation of a new boundary: stable ports
are retained as a dependent function, while entering targets use the recursive
edge-list tuple expected by `edgeListAction`. -/
noncomputable def endpointAwareSuccBoundaryPost
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output (k + 1)) :
      EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
        EdgeListTuple (fun e ↦ dim (dst e))
          (rankEnteringEdgeList rank src k) :=
  (endpointAwareSuccBoundaryToCarried dim rank src dst input output k boundary,
    (rankEnteringEdgeTupleEquiv dim rank src dst k).symm
      (endpointAwareSuccBoundaryToEntering
        dim rank src dst hedge input output k boundary))

/-- The concrete post representation is injective.  Each new edge port is
read either from the carried factor or from its unique entering-edge slot; the
input port is impossible after level zero. -/
theorem endpointAwareSuccBoundaryPost_injective
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hinput : rank input = 0) :
    Function.Injective
      (endpointAwareSuccBoundaryPost dim rank src dst hedge input output k) := by
  classical
  intro boundary₁ boundary₂ h
  have hcarried :
      endpointAwareSuccBoundaryToCarried dim rank src dst input output k boundary₁ =
        endpointAwareSuccBoundaryToCarried dim rank src dst input output k boundary₂ :=
    congrArg Prod.fst h
  have htuple :
      (rankEnteringEdgeTupleEquiv dim rank src dst k).symm
          (endpointAwareSuccBoundaryToEntering
            dim rank src dst hedge input output k boundary₁) =
        (rankEnteringEdgeTupleEquiv dim rank src dst k).symm
          (endpointAwareSuccBoundaryToEntering
            dim rank src dst hedge input output k boundary₂) :=
    congrArg Prod.snd h
  have hentering :
      endpointAwareSuccBoundaryToEntering
          dim rank src dst hedge input output k boundary₁ =
        endpointAwareSuccBoundaryToEntering
          dim rank src dst hedge input output k boundary₂ :=
    (rankEnteringEdgeTupleEquiv dim rank src dst k).symm.injective htuple
  funext p
  rcases p with ⟨p, hp⟩
  cases p with
  | input =>
      simp only [rankCutPortActive] at hp
      omega
  | output =>
      simpa only [endpointAwareSuccBoundaryToCarried] using
        congrFun hcarried ⟨RankCutPort.output, hp⟩
  | edge e =>
      by_cases he : rank (src e) = k
      · have hemem : e ∈ rankEnteringEdges rank src k := by
          simpa only [mem_rankEnteringEdges] using he
        simpa only [endpointAwareSuccBoundaryToEntering, rankCutPortDim] using
          congrFun hentering ⟨e, hemem⟩
      · have hlt : rank (src e) < k := by
          simp only [rankCutPortActive] at hp
          omega
        have hcarry : rankCutCarriedPortActive rank src dst input output k
            (RankCutPort.edge e) := ⟨hp, hlt⟩
        simpa only [endpointAwareSuccBoundaryToCarried] using
          congrFun hcarried ⟨RankCutPort.edge e, hcarry⟩

/-- A chosen outgoing edge from a non-output vertex on one rank level.  The
choice is proof-local infrastructure and never appears in a public signature. -/
noncomputable def mingoOutgoingRankAnchor
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ output) : ε :=
  Classical.choose (hdag.exists_outgoing_rank_anchor src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)

theorem mingoOutgoingRankAnchor_src
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ output) :
    src (mingoOutgoingRankAnchor rank src dst input output hdag hedge v hv) = v.1 :=
  (Classical.choose_spec (hdag.exists_outgoing_rank_anchor
    src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)).1

theorem mingoOutgoingRankAnchor_dst_rank
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ output) :
    k < rank (dst
      (mingoOutgoingRankAnchor rank src dst input output hdag hedge v hv)) :=
  (Classical.choose_spec (hdag.exists_outgoing_rank_anchor
    src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)).2

/-- A chosen incoming old-cut anchor for a non-input level vertex. -/
noncomputable def mingoIncomingRankAnchor
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ input) : ε :=
  Classical.choose (hdag.exists_incoming_rank_anchor src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)

theorem mingoIncomingRankAnchor_dst
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ input) :
    dst (mingoIncomingRankAnchor rank src dst input output hdag hedge v hv) = v.1 :=
  (Classical.choose_spec (hdag.exists_incoming_rank_anchor
    src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)).1

theorem mingoIncomingRankAnchor_src_rank
    {ι ε : Type*} [Fintype ι]
    (rank : ι → ℕ) (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    {k : ℕ} (v : {v // v ∈ rankLevelVertices rank k})
    (hv : v.1 ≠ input) :
    rank (src
      (mingoIncomingRankAnchor rank src dst input output hdag hedge v hv)) < k :=
  (Classical.choose_spec (hdag.exists_incoming_rank_anchor
    src dst input output hedge
    ((mem_rankLevelVertices rank k v.1).1 v.2) hv)).2

/-- Read the common label of a level-`k` vertex from a prepared index: the
new output port is the anchor for `output`, and a chosen outgoing entering edge
is the anchor for every other level vertex. -/
noncomputable def endpointAwareRankCutStepLevelLabel
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k))
    (v : {v // v ∈ rankLevelVertices rank k}) : Fin (dim v.1) := by
  classical
  by_cases hvo : v.1 = output
  · exact Fin.cast (congrArg dim hvo.symm)
      (q.1 ⟨RankCutPort.output, by
        simp only [rankCutCarriedPortActive, rankCutPortActive]
        have hvk := (mem_rankLevelVertices rank k v.1).1 v.2
        rw [hvo] at hvk
        omega⟩)
  · let e := mingoOutgoingRankAnchor
      rank src dst input output hdag hedge v hvo
    have hesrc : src e = v.1 :=
      mingoOutgoingRankAnchor_src
        rank src dst input output hdag hedge v hvo
    have heIn : e ∈ rankEnteringEdges rank src k := by
      rw [mem_rankEnteringEdges, hesrc]
      exact (mem_rankLevelVertices rank k v.1).1 v.2
    exact Fin.cast (congrArg dim hesrc)
      ((rankEnteringEdgeTupleEquiv dim rank src src k q.2) ⟨e, heIn⟩)

theorem endpointAwareRankCutStepLevelLabel_output
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k))
    (hout : output ∈ rankLevelVertices rank k) :
    endpointAwareRankCutStepLevelLabel dim rank src dst input output
        hdag hedge k q ⟨output, hout⟩ =
      q.1 ⟨RankCutPort.output, by
        simp only [rankCutCarriedPortActive, rankCutPortActive]
        have houtRank := (mem_rankLevelVertices rank k output).1 hout
        omega⟩ := by
  simp [endpointAwareRankCutStepLevelLabel]
  congr 1

/-- The prepared source tuple is consistent when every entering edge carries
the one common label of its source level vertex.  Branching is therefore a
finite diagonal restriction, not a nonlinear copy map. -/
def endpointAwareRankCutStepConsistent
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k)) : Prop :=
  ∀ e : {e // e ∈ rankEnteringEdges rank src k},
    (rankEnteringEdgeTupleEquiv dim rank src src k q.2) e =
      endpointAwareRankCutStepLevelLabel dim rank src dst input output
        hdag hedge k q ⟨src e.1, by
          rw [mem_rankLevelVertices]
          exact (mem_rankEnteringEdges rank src k e.1).1 e.2⟩

abbrev EndpointAwareConsistentPreparedIndex
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e)) (k : ℕ) :=
  {q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k) //
    endpointAwareRankCutStepConsistent dim rank src dst input output
      hdag hedge k q}

/-- Coordinate-level implementation of the old-boundary map.  Recursing on
the port before packaging its activity proof keeps later reduction lemmas free
of large subtype transports. -/
noncomputable def endpointAwareOldBoundaryPortValue
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k) :
    (p : RankCutPort ε) →
      rankCutPortActive rank src dst input output k p →
        Fin (rankCutPortDim dim dst input output p)
  | .input, hp =>
      endpointAwareRankCutStepLevelLabel dim rank src dst input output
        hdag hedge k q.1 ⟨input, by
      rw [mem_rankLevelVertices]
      simp only [rankCutPortActive] at hp
      omega⟩
  | .output, hp =>
      q.1.1 ⟨RankCutPort.output, by
        simp only [rankCutCarriedPortActive, rankCutPortActive] at hp ⊢
        omega⟩
  | .edge e, hp => by
      by_cases hedst : rank (dst e) = k
      · exact endpointAwareRankCutStepLevelLabel dim rank src dst input output
          hdag hedge k q.1 ⟨dst e, by
            simpa only [mem_rankLevelVertices] using hedst⟩
      · exact q.1.1 ⟨RankCutPort.edge e, by
          refine ⟨?_, ?_⟩
          · simp only [rankCutPortActive] at hp ⊢
            omega
          · exact hp.1⟩

/-- Map a consistent prepared index back to the old cut.  Persistent ports are
copied directly; a disappearing edge reads the label of its target level
vertex, and the first-step input port reads the input level label. -/
noncomputable def endpointAwareOldBoundaryOfPrepared
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k) :
    EndpointAwareRankCutIndex dim rank src dst input output k :=
  fun p ↦ endpointAwareOldBoundaryPortValue dim rank src dst input output hdag
    hedge k hinput q p.1 p.2

theorem endpointAwareOldBoundaryOfPrepared_input
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k)
    (hp : rankCutPortActive rank src dst input output k RankCutPort.input)
    (hlevel : input ∈ rankLevelVertices rank k) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput q ⟨RankCutPort.input, hp⟩ =
      endpointAwareRankCutStepLevelLabel dim rank src dst input output
        hdag hedge k q.1 ⟨input, hlevel⟩ := by
  simp only [endpointAwareOldBoundaryOfPrepared,
    endpointAwareOldBoundaryPortValue]
  congr 1

theorem endpointAwareOldBoundaryOfPrepared_output
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k)
    (hp : rankCutPortActive rank src dst input output k RankCutPort.output) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput q ⟨RankCutPort.output, hp⟩ =
      q.1.1 ⟨RankCutPort.output, by
        simp only [rankCutCarriedPortActive, rankCutPortActive] at hp ⊢
        omega⟩ := by
  simp only [endpointAwareOldBoundaryOfPrepared,
    endpointAwareOldBoundaryPortValue]

theorem endpointAwareOldBoundaryOfPrepared_edge_leaving
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k) (e : ε)
    (hp : rankCutPortActive rank src dst input output k (RankCutPort.edge e))
    (hedst : rank (dst e) = k) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput q ⟨RankCutPort.edge e, hp⟩ =
      endpointAwareRankCutStepLevelLabel dim rank src dst input output
        hdag hedge k q.1 ⟨dst e, by
          simpa only [mem_rankLevelVertices] using hedst⟩ := by
  simp only [endpointAwareOldBoundaryOfPrepared,
    endpointAwareOldBoundaryPortValue]
  simp only [hedst, ↓reduceDIte]
  congr 1

theorem endpointAwareOldBoundaryOfPrepared_edge_persistent
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0)
    (q : EndpointAwareConsistentPreparedIndex dim rank src dst input output
      hdag hedge k) (e : ε)
    (hp : rankCutPortActive rank src dst input output k (RankCutPort.edge e))
    (hedst : rank (dst e) ≠ k) :
    endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput q ⟨RankCutPort.edge e, hp⟩ =
      q.1.1 ⟨RankCutPort.edge e, by
        refine ⟨?_, hp.1⟩
        simp only [rankCutPortActive] at hp ⊢
        omega⟩ := by
  simp only [endpointAwareOldBoundaryOfPrepared,
    endpointAwareOldBoundaryPortValue]
  simp only [hedst, ↓reduceDIte]

/-- The diagonal restriction from consistent prepared indices to the old cut
is injective.  Old input/incoming-edge anchors recover every level label;
those labels recover all duplicated entering sources, while persistent ports
are read directly. -/
theorem endpointAwareOldBoundaryOfPrepared_injective
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hio : input ≠ output) :
    Function.Injective
      (endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput) := by
  classical
  intro q₁ q₂ hold
  have hlevel : ∀ v : {v // v ∈ rankLevelVertices rank k},
      endpointAwareRankCutStepLevelLabel dim rank src dst input output
          hdag hedge k q₁.1 v =
        endpointAwareRankCutStepLevelLabel dim rank src dst input output
          hdag hedge k q₂.1 v := by
    rintro ⟨v, hvLevel⟩
    by_cases hvi : v = input
    · subst v
      have hvk := (mem_rankLevelVertices rank k input).1 hvLevel
      have hp : rankCutPortActive rank src dst input output k
          RankCutPort.input := by
        simp only [rankCutPortActive]
        omega
      have hcoord := congrFun hold ⟨RankCutPort.input, hp⟩
      rw [endpointAwareOldBoundaryOfPrepared_input dim rank src dst input output
          hdag hedge k hinput q₁ hp hvLevel,
        endpointAwareOldBoundaryOfPrepared_input dim rank src dst input output
          hdag hedge k hinput q₂ hp hvLevel] at hcoord
      exact hcoord
    · let vLevel : {v // v ∈ rankLevelVertices rank k} := ⟨v, hvLevel⟩
      let e := mingoIncomingRankAnchor
        rank src dst input output hdag hedge vLevel hvi
      have hedst : dst e = v :=
        mingoIncomingRankAnchor_dst
          rank src dst input output hdag hedge vLevel hvi
      have hesrc : rank (src e) < k :=
        mingoIncomingRankAnchor_src_rank
          rank src dst input output hdag hedge vLevel hvi
      have hedstRank : rank (dst e) = k := by
        rw [hedst]
        exact (mem_rankLevelVertices rank k v).1 hvLevel
      have hp : rankCutPortActive rank src dst input output k
          (RankCutPort.edge e) := by
        simp only [rankCutPortActive]
        exact ⟨hesrc, by omega⟩
      have hcoord := congrFun hold ⟨RankCutPort.edge e, hp⟩
      rw [endpointAwareOldBoundaryOfPrepared_edge_leaving
          dim rank src dst input output hdag hedge k hinput q₁ e hp hedstRank,
        endpointAwareOldBoundaryOfPrepared_edge_leaving
          dim rank src dst input output hdag hedge k hinput q₂ e hp hedstRank]
        at hcoord
      let anchor : {v // v ∈ rankLevelVertices rank k} :=
        ⟨dst e, by simpa only [mem_rankLevelVertices] using hedstRank⟩
      have hvsub : anchor = ⟨v, hvLevel⟩ := Subtype.ext hedst
      exact hvsub ▸ hcoord
  apply Subtype.ext
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
        by_cases hout : rank output < k
        · have hpOld : rankCutPortActive rank src dst input output k
              RankCutPort.output := by
            simpa only [rankCutPortActive] using hout
          have hcoord := congrFun hold ⟨RankCutPort.output, hpOld⟩
          rw [endpointAwareOldBoundaryOfPrepared_output
              dim rank src dst input output hdag hedge k hinput q₁ hpOld,
            endpointAwareOldBoundaryOfPrepared_output
              dim rank src dst input output hdag hedge k hinput q₂ hpOld]
            at hcoord
          exact hcoord
        · have hactive :=
            rankCutCarriedPortActive.active rank src dst input output k hp
          have houtRank : rank output = k := by
            simp only [rankCutPortActive] at hactive
            omega
          have houtLevel : output ∈ rankLevelVertices rank k := by
            simpa only [mem_rankLevelVertices] using houtRank
          have hlabel := hlevel ⟨output, houtLevel⟩
          rw [endpointAwareRankCutStepLevelLabel_output
              dim rank src dst input output hdag hedge k q₁.1 houtLevel,
            endpointAwareRankCutStepLevelLabel_output
              dim rank src dst input output hdag hedge k q₂.1 houtLevel]
            at hlabel
          exact hlabel
    | edge e =>
        have hactive :=
          rankCutCarriedPortActive.active rank src dst input output k hp
        have hpOld : rankCutPortActive rank src dst input output k
            (RankCutPort.edge e) := by
          simp only [rankCutPortActive] at hactive ⊢
          exact ⟨hp.2, by omega⟩
        have hedst : rank (dst e) ≠ k := by
          simp only [rankCutPortActive] at hactive
          omega
        have hcoord := congrFun hold ⟨RankCutPort.edge e, hpOld⟩
        rw [endpointAwareOldBoundaryOfPrepared_edge_persistent
            dim rank src dst input output hdag hedge k hinput q₁ e hpOld hedst,
          endpointAwareOldBoundaryOfPrepared_edge_persistent
            dim rank src dst input output hdag hedge k hinput q₂ e hpOld hedst]
          at hcoord
        exact hcoord
  · apply (rankEnteringEdgeTupleEquiv dim rank src src k).injective
    funext e
    let vsrc : {v // v ∈ rankLevelVertices rank k} :=
      ⟨src e.1, (mem_rankLevelVertices rank k (src e.1)).2
        ((mem_rankEnteringEdges rank src k e.1).1 e.2)⟩
    calc
      (rankEnteringEdgeTupleEquiv dim rank src src k q₁.1.2) e =
          endpointAwareRankCutStepLevelLabel dim rank src dst input output
            hdag hedge k q₁.1 vsrc := q₁.2 e
      _ = endpointAwareRankCutStepLevelLabel dim rank src dst input output
            hdag hedge k q₂.1 vsrc := hlevel vsrc
      _ = (rankEnteringEdgeTupleEquiv dim rank src src k q₂.1.2) e :=
        (q₂.2 e).symm

/-- The prepared coefficient array is the old state on the consistent
diagonal and zero off that diagonal. -/
noncomputable def endpointAwareRankCutStepPrepared
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (x : Fin (dim input) → ℝ)
    (q : EndpointAwareRankCutCarriedIndex dim rank src dst input output k ×
      EdgeListTuple (fun e ↦ dim (src e))
        (rankEnteringEdgeList rank src k)) : ℝ := by
  classical
  exact if hq : endpointAwareRankCutStepConsistent dim rank src dst
      input output hdag hedge k q then
    endpointAwareRankCutState dim rank src dst M hedge input output k x
      (endpointAwareOldBoundaryOfPrepared dim rank src dst input output hdag
        hedge k hinput ⟨q, hq⟩)
  else 0

/- Restricting to consistent prepared indices contracts squared energy. -/
set_option maxHeartbeats 800000 in
theorem endpointAwareRankCutStepPrepared_energy_le
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hio : input ≠ output)
    (x : Fin (dim input) → ℝ) :
    (∑ q, (endpointAwareRankCutStepPrepared dim rank src dst M input output
      hdag hedge k hinput x q) ^ 2) ≤
      endpointAwareRankCutEnergy dim rank src dst input output k
        (endpointAwareRankCutState dim rank src dst M hedge input output k x) := by
  classical
  let P := endpointAwareRankCutStepConsistent dim rank src dst input output
    hdag hedge k
  let oldState := endpointAwareRankCutState dim rank src dst M hedge
    input output k x
  let oldBoundary := endpointAwareOldBoundaryOfPrepared dim rank src dst
    input output hdag hedge k hinput
  have hsum :
      (∑ q, (endpointAwareRankCutStepPrepared dim rank src dst M input output
        hdag hedge k hinput x q) ^ 2) =
        ∑ q : EndpointAwareConsistentPreparedIndex dim rank src dst
          input output hdag hedge k, (oldState (oldBoundary q)) ^ 2 := by
    simpa only [endpointAwareRankCutStepPrepared, P, oldState, oldBoundary]
      using sum_dite_sq_eq_subtype P
        (fun q ↦ oldState (oldBoundary q))
  rw [hsum, endpointAwareRankCutEnergy]
  exact sum_comp_injective_le oldBoundary
    (endpointAwareOldBoundaryOfPrepared_injective dim rank src dst input output
      hdag hedge k hinput hio)
    (fun boundary ↦ (oldState boundary) ^ 2)
    (fun boundary ↦ sq_nonneg (oldState boundary))

/-- Exact combinatorial/factorization certificate still needed at one rank
step.  Its fields say that the old cut restricts injectively to the common
level labels plus carried coordinates, the entering-edge matrices act once,
and the resulting expanded array restricts injectively to the new cut. -/
structure EndpointAwareRankCutStepFactorization
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ) where
  carried : Type*
  carriedFintype : Fintype carried
  prepared : carried × EdgeListTuple (fun e ↦ dim (src e))
      (rankEnteringEdgeList rank src k) → ℝ
  post : EndpointAwareRankCutIndex dim rank src dst input output (k + 1) →
    carried × EdgeListTuple (fun e ↦ dim (dst e))
      (rankEnteringEdgeList rank src k)
  post_injective : Function.Injective post
  prepared_energy :
    (∑ q, (prepared q) ^ 2) ≤
      endpointAwareRankCutEnergy dim rank src dst input output k
        (endpointAwareRankCutState dim rank src dst M hedge input output k x)
  state_factor : ∀ boundary,
    endpointAwareRankCutState dim rank src dst M hedge input output (k + 1)
        x boundary =
      edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
        (rankEnteringEdgeList rank src k)
        (fun xs ↦ prepared ((post boundary).1, xs))
        (post boundary).2

/-- Assemble the concrete adjacent-cut certificate once the sole remaining
coefficient identity has been proved.  All finite-index injections and the
prepared-array energy contraction are discharged by the preceding lemmas. -/
noncomputable def endpointAwareRankCutStepFactorization_of_state_factor
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (k : ℕ) (hinput : rank input = 0) (hio : input ≠ output)
    (x : Fin (dim input) → ℝ)
    (hstate : ∀ boundary,
      endpointAwareRankCutState dim rank src dst M hedge input output (k + 1)
          x boundary =
        edgeListAction (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
          (rankEnteringEdgeList rank src k)
          (fun xs ↦ endpointAwareRankCutStepPrepared dim rank src dst M
            input output hdag hedge k hinput x
              ((endpointAwareSuccBoundaryPost dim rank src dst hedge
                input output k boundary).1, xs))
          (endpointAwareSuccBoundaryPost dim rank src dst hedge
            input output k boundary).2) :
    EndpointAwareRankCutStepFactorization dim rank src dst M hedge
      input output k x := by
  classical
  exact
    { carried := EndpointAwareRankCutCarriedIndex dim rank src dst
        input output k
      carriedFintype := endpointAwareRankCutCarriedIndexFintype
        dim rank src dst input output k
      prepared := endpointAwareRankCutStepPrepared dim rank src dst M
        input output hdag hedge k hinput x
      post := endpointAwareSuccBoundaryPost dim rank src dst hedge
        input output k
      post_injective := endpointAwareSuccBoundaryPost_injective
        dim rank src dst hedge input output k hinput
      prepared_energy := endpointAwareRankCutStepPrepared_energy_le
        dim rank src dst M input output hdag hedge k hinput hio x
      state_factor := by simpa using hstate }

/-- Once the concrete cut factorization is supplied, the adjacent `L2`
contraction has exactly the desired product over edges sourced at level `k`. -/
theorem endpointAwareRankCutEnergy_succ_le_of_factorization
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (x : Fin (dim input) → ℝ)
    (F : EndpointAwareRankCutStepFactorization dim rank src dst M hedge
      input output k x) :
    endpointAwareRankCutEnergy dim rank src dst input output (k + 1)
        (endpointAwareRankCutState dim rank src dst M hedge input output
          (k + 1) x) ≤
      (∏ e ∈ rankEnteringEdges rank src k,
          euclideanOperatorNorm (M e) ^ 2) *
        endpointAwareRankCutEnergy dim rank src dst input output k
          (endpointAwareRankCutState dim rank src dst M hedge input output k x) := by
  classical
  let _ : Fintype F.carried := F.carriedFintype
  rw [endpointAwareRankCutEnergy, endpointAwareRankCutEnergy,
    ← rankEnteringEdgeList_prod rank src k]
  exact rankCutStepEnergy_le_of_factorization
    (fun e ↦ dim (src e)) (fun e ↦ dim (dst e)) M
    (rankEnteringEdgeList rank src k)
    (endpointAwareRankCutState dim rank src dst M hedge input output k x)
    (endpointAwareRankCutState dim rank src dst M hedge input output (k + 1) x)
    F.prepared F.post F.post_injective F.prepared_energy F.state_factor

/-- Iterate exact adjacent-cut certificates through a finite initial segment.
This isolates the remaining graph proof to construction of the certificates;
all analytic accumulation is handled here. -/
theorem endpointAwareRankCutEnergy_le_of_factorizations
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (x : Fin (dim input) → ℝ) (K : ℕ)
    (hfactor : ∀ k, k < K →
      EndpointAwareRankCutStepFactorization dim rank src dst M hedge
        input output k x) :
    endpointAwareRankCutEnergy dim rank src dst input output K
        (endpointAwareRankCutState dim rank src dst M hedge input output K x) ≤
      (∏ k ∈ Finset.range K,
          ∏ e ∈ rankEnteringEdges rank src k,
            euclideanOperatorNorm (M e) ^ 2) *
        endpointAwareRankCutEnergy dim rank src dst input output 0
          (endpointAwareRankCutState dim rank src dst M hedge input output 0 x) := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
      let stepFactor := hfactor K (Nat.lt_succ_self K)
      have hstep := endpointAwareRankCutEnergy_succ_le_of_factorization
        dim rank src dst M hedge input output K x stepFactor
      have hprev := ih (fun k hk ↦ hfactor k (hk.trans (Nat.lt_succ_self K)))
      have hnonneg :
          0 ≤ ∏ e ∈ rankEnteringEdges rank src K,
            euclideanOperatorNorm (M e) ^ 2 := by
        positivity
      calc
        endpointAwareRankCutEnergy dim rank src dst input output (K + 1)
            (endpointAwareRankCutState dim rank src dst M hedge input output
              (K + 1) x) ≤
            (∏ e ∈ rankEnteringEdges rank src K,
                euclideanOperatorNorm (M e) ^ 2) *
              endpointAwareRankCutEnergy dim rank src dst input output K
                (endpointAwareRankCutState dim rank src dst M hedge input output
                  K x) := hstep
        _ ≤ (∏ e ∈ rankEnteringEdges rank src K,
                euclideanOperatorNorm (M e) ^ 2) *
              ((∏ k ∈ Finset.range K,
                  ∏ e ∈ rankEnteringEdges rank src k,
                    euclideanOperatorNorm (M e) ^ 2) *
                endpointAwareRankCutEnergy dim rank src dst input output 0
                  (endpointAwareRankCutState dim rank src dst M hedge
                    input output 0 x)) :=
          mul_le_mul_of_nonneg_left hprev hnonneg
        _ = (∏ k ∈ Finset.range (K + 1),
                ∏ e ∈ rankEnteringEdges rank src k,
                  euclideanOperatorNorm (M e) ^ 2) *
              endpointAwareRankCutEnergy dim rank src dst input output 0
                (endpointAwareRankCutState dim rank src dst M hedge
                  input output 0 x) := by
          rw [Finset.prod_range_succ]
          ring

theorem rankProcessedVertices_eq_univ_of_all_lt
    {ι : Type*} [Fintype ι] (rank : ι → ℕ) (k : ℕ)
    (hall : ∀ v, rank v < k) :
    rankProcessedVertices rank k = Finset.univ := by
  classical
  ext v
  simp [hall v]

theorem rankCompletedEdges_eq_univ_of_all_lt
    {ι ε : Type*} [Fintype ε] (rank : ι → ℕ) (dst : ε → ι) (k : ℕ)
    (hall : ∀ e, rank (dst e) < k) :
    rankCompletedEdges rank dst k = Finset.univ := by
  classical
  ext e
  simp [hall e]

theorem rankActiveEdges_eq_empty_of_all_dst_lt
    {ι ε : Type*} [Fintype ε] (rank : ι → ℕ)
    (src dst : ε → ι) (k : ℕ)
    (hall : ∀ e, rank (dst e) < k) :
    rankActiveEdges rank src dst k = ∅ := by
  classical
  ext e
  simp only [mem_rankActiveEdges, Finset.notMem_empty, iff_false]
  have he := hall e
  omega

/-- Restricting a full label assignment to a cut which contains every vertex
is an equivalence. -/
def processedLabelsEquivOfAll
    {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (k : ℕ)
    (hall : ∀ v, v ∈ rankProcessedVertices rank k) :
    RankCutProcessedLabels dim rank k ≃ (∀ v, Fin (dim v)) where
  toFun labels v := labels ⟨v, hall v⟩
  invFun labels v := labels v.1
  left_inv labels := by
    funext v
    rfl
  right_inv labels := by
    funext v
    rfl

/-- A subtype cut out by a predicate true at every element is equivalent to
the original type. -/
def subtypeEquivOfForall {α : Type*} (p : α → Prop) (hall : ∀ x, p x) :
    {x // p x} ≃ α where
  toFun x := x.1
  invFun x := ⟨x, hall x⟩
  left_inv x := by rfl
  right_inv x := by rfl

/-- At any cut strictly above every vertex rank, the partial contraction is
exactly the original graph-operator entry. -/
theorem rankPartialContraction_eq_graphOperator_of_all_processed
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hall : ∀ v, rank v < k)
    (a : Fin (dim input)) (b : Fin (dim output))
    (boundary : RankCutActiveIndex dim rank src dst k) :
    rankPartialContraction dim rank src dst M hedge input output k a b boundary =
      graphOperator dim src dst M input output a b := by
  classical
  have hprocessed : ∀ v, v ∈ rankProcessedVertices rank k := by
    intro v
    simpa using hall v
  have hcompleted : ∀ e, e ∈ rankCompletedEdges rank dst k := by
    intro e
    simpa using hall (dst e)
  have hactive : IsEmpty {e // e ∈ rankActiveEdges rank src dst k} := by
    constructor
    intro e
    have he := (mem_rankActiveEdges rank src dst k e.1).1 e.2
    exact (not_lt_of_ge he.2) (hall (dst e.1))
  let _ : IsEmpty {e // e ∈ rankActiveEdges rank src dst k} := hactive
  rw [rankPartialContraction, graphOperator]
  apply Fintype.sum_equiv
    (processedLabelsEquivOfAll dim rank k hprocessed)
  intro labels
  let fullLabels : ∀ v, Fin (dim v) :=
    processedLabelsEquivOfAll dim rank k hprocessed labels
  have hprod :
      (∏ e : {e // e ∈ rankCompletedEdges rank dst k},
        M e.1
          (labels ⟨src e.1, by
            rw [mem_rankProcessedVertices]
            exact (hedge e.1).trans
              ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
          (labels ⟨dst e.1, by
            rw [mem_rankProcessedVertices]
            exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)) =
        ∏ e, M e (fullLabels (src e)) (fullLabels (dst e)) := by
    apply Fintype.prod_equiv
      (subtypeEquivOfForall
        (fun e ↦ e ∈ rankCompletedEdges rank dst k) hcompleted)
    intro e
    rfl
  rw [hprod]
  have hlabel (v : ι) (hv : v ∈ rankProcessedVertices rank k) :
      labels ⟨v, hv⟩ =
        (processedLabelsEquivOfAll dim rank k hprocessed labels) v := by
    rfl
  by_cases hin : fullLabels input = a <;>
    by_cases hout : fullLabels output = b <;>
    dsimp only [fullLabels] at hin hout ⊢ <;>
    simp [processedEndpointConstraint, hprocessed, hlabel, hin, hout]

theorem mingoDAGRank_lt_terminalCut
    {ι ε : Type*} [Fintype ι]
    (src dst : ε → ι) (v : ι) :
    mingoDAGRank src dst v < Fintype.card ι + 1 := by
  exact Nat.lt_succ_of_le (finiteDAGRank_le_card (directedAdjacent src dst) v)

theorem prod_mingoRankEnteringEdges_range
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (src dst : ε → ι) (f : ε → ℝ) :
    (∏ k ∈ Finset.range (Fintype.card ι + 1),
        ∏ e ∈ rankEnteringEdges (mingoDAGRank src dst) src k, f e) =
      ∏ e, f e := by
  exact prod_rankEnteringEdges_range (mingoDAGRank src dst) src f
    (Fintype.card ι + 1)
    (fun e ↦ mingoDAGRank_lt_terminalCut src dst (src e))

/-- The terminal value of the rank-cut invariant is the repository's
`graphOperator`; hence the remaining induction has exact endpoints. -/
theorem mingoRankPartialContraction_terminal
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (a : Fin (dim input)) (b : Fin (dim output))
    (boundary : RankCutActiveIndex dim (mingoDAGRank src dst) src dst
      (Fintype.card ι + 1)) :
    rankPartialContraction dim (mingoDAGRank src dst) src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output (Fintype.card ι + 1) a b boundary =
      graphOperator dim src dst M input output a b := by
  apply rankPartialContraction_eq_graphOperator_of_all_processed
  exact fun v ↦ mingoDAGRank_lt_terminalCut src dst v

/-- In the degenerate `input = output` case admitted by the repository
definition, reachability plus directed acyclicity forces a one-vertex graph. -/
theorem MingoAdmissibleDAG.subsingleton_of_eq_endpoints
    {ι ε : Type*} (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input = output) : Subsingleton ι := by
  constructor
  intro u v
  have hall : ∀ w : ι, w = input := by
    intro w
    rcases hdag.2.1 w with rfl | hiw
    · rfl
    rcases hdag.2.2 w with hwo | hwo
    · exact hwo.trans hio.symm
    · exfalso
      apply hdag.1 input
      exact hiw.trans (hio ▸ hwo)
  exact (hall u).trans (hall v).symm

/-- The same degenerate case has no edges: any edge would be a directed
self-cycle on the unique vertex. -/
theorem MingoAdmissibleDAG.isEmpty_edges_of_eq_endpoints
    {ι ε : Type*} (src dst : ε → ι) (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hio : input = output) : IsEmpty ε := by
  have hsub : Subsingleton ι :=
    hdag.subsingleton_of_eq_endpoints src dst input output hio
  constructor
  intro e
  apply hdag.1 (src e)
  apply Relation.TransGen.single
  exact ⟨e, rfl, hsub.elim _ _⟩

/-- Evaluation at a chosen point identifies a dependent function over a
subsingleton index type with its fiber at that point. -/
def piSubsingletonEquiv {ι : Type*} (β : ι → Sort*)
    (base : ι) (hsub : Subsingleton ι) : (∀ i, β i) ≃ β base where
  toFun f := f base
  invFun b i := cast (congrArg β (hsub.elim base i)) b
  left_inv f := by
    funext i
    cases hsub.elim i base
    rfl
  right_inv b := by
    simp

def endpointAwareZeroIndexEquiv
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) :
    EndpointAwareRankCutIndex dim rank src dst input output 0 ≃
      Fin (dim input) := by
  let base : {p // rankCutPortActive rank src dst input output 0 p} :=
    ⟨RankCutPort.input, by simp [rankCutPortActive]⟩
  have hport : ∀ p : {p // rankCutPortActive rank src dst input output 0 p},
      p.1 = RankCutPort.input := by
    rintro ⟨p, hp⟩
    cases p with
    | input => rfl
    | edge e => simp [rankCutPortActive] at hp
    | output => simp [rankCutPortActive] at hp
  have hsub : Subsingleton
      {p // rankCutPortActive rank src dst input output 0 p} := by
    constructor
    intro p q
    exact Subtype.ext ((hport p).trans (hport q).symm)
  exact piSubsingletonEquiv
    (fun p ↦ Fin (rankCutPortDim dim dst input output p.1)) base hsub

def endpointAwareTerminalIndexEquiv
    {ι ε : Type*} [Fintype ε]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (input output : ι) (k : ℕ) (hall : ∀ v, rank v < k) :
    EndpointAwareRankCutIndex dim rank src dst input output k ≃
      Fin (dim output) := by
  let base : {p // rankCutPortActive rank src dst input output k p} :=
    ⟨RankCutPort.output, by simpa [rankCutPortActive] using hall output⟩
  have hport : ∀ p : {p // rankCutPortActive rank src dst input output k p},
      p.1 = RankCutPort.output := by
    rintro ⟨p, hp⟩
    cases p with
    | input =>
        simp only [rankCutPortActive] at hp
        exact (not_lt_of_ge hp (hall input)).elim
    | edge e =>
        simp only [rankCutPortActive] at hp
        exact (not_lt_of_ge hp.2 (hall (dst e))).elim
    | output => rfl
  have hsub : Subsingleton
      {p // rankCutPortActive rank src dst input output k p} := by
    constructor
    intro p q
    exact Subtype.ext ((hport p).trans (hport q).symm)
  exact piSubsingletonEquiv
    (fun p ↦ Fin (rankCutPortDim dim dst input output p.1)) base hsub

theorem endpointAwareRankCutEnergy_zero
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (x : Fin (dim input) → ℝ) :
    endpointAwareRankCutEnergy dim rank src dst input output 0
        (endpointAwareRankCutState dim rank src dst M hedge input output 0 x) =
      ∑ i, (x i) ^ 2 := by
  classical
  rw [endpointAwareRankCutEnergy]
  apply Fintype.sum_equiv
    (endpointAwareZeroIndexEquiv dim rank src dst input output)
  intro boundary
  rw [endpointAwareRankCutState_zero]
  rfl

theorem endpointAwareRankCutState_terminal
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hall : ∀ v, rank v < k)
    (x : Fin (dim input) → ℝ)
    (boundary : EndpointAwareRankCutIndex dim rank src dst input output k) :
    endpointAwareRankCutState dim rank src dst M hedge input output k x boundary =
      (graphOperator dim src dst M input output).transpose.mulVec x
        ((endpointAwareTerminalIndexEquiv dim rank src dst input output k hall)
          boundary) := by
  classical
  let b : Fin (dim output) :=
    (endpointAwareTerminalIndexEquiv dim rank src dst input output k hall)
      boundary
  have hprocessed : ∀ v, v ∈ rankProcessedVertices rank k := by
    intro v
    simpa using hall v
  have hcompleted : ∀ e, e ∈ rankCompletedEdges rank dst k := by
    intro e
    simpa using hall (dst e)
  have hactive : IsEmpty {e // e ∈ rankActiveEdges rank src dst k} := by
    constructor
    intro e
    have he := (mem_rankActiveEdges rank src dst k e.1).1 e.2
    exact (not_lt_of_ge he.2) (hall (dst e.1))
  let _ : IsEmpty {e // e ∈ rankActiveEdges rank src dst k} := hactive
  have hboundary : boundary ⟨RankCutPort.output, by
        simpa only [rankCutPortActive] using hall output⟩ = b := by
    rfl
  have hstate :
      endpointAwareRankCutState dim rank src dst M hedge input output k x boundary =
        ∑ labels : ∀ v, Fin (dim v),
          x (labels input) *
            (if labels output = b then 1 else 0) *
            ∏ e, M e (labels (src e)) (labels (dst e)) := by
    rw [endpointAwareRankCutState]
    apply Fintype.sum_equiv
      (processedLabelsEquivOfAll dim rank k hprocessed)
    intro labels
    let fullLabels : ∀ v, Fin (dim v) :=
      processedLabelsEquivOfAll dim rank k hprocessed labels
    have hprod :
        (∏ e : {e // e ∈ rankCompletedEdges rank dst k},
          M e.1
            (labels ⟨src e.1, by
              rw [mem_rankProcessedVertices]
              exact (hedge e.1).trans
                ((mem_rankCompletedEdges rank dst k e.1).1 e.2)⟩)
            (labels ⟨dst e.1, by
              rw [mem_rankProcessedVertices]
              exact (mem_rankCompletedEdges rank dst k e.1).1 e.2⟩)) =
          ∏ e, M e (fullLabels (src e)) (fullLabels (dst e)) := by
      apply Fintype.prod_equiv
        (subtypeEquivOfForall
          (fun e ↦ e ∈ rankCompletedEdges rank dst k) hcompleted)
      intro e
      rfl
    rw [hprod]
    have hlabel (v : ι) (hv : v ∈ rankProcessedVertices rank k) :
        labels ⟨v, hv⟩ = fullLabels v := by
      rfl
    simp only [hall input, hall output, ↓reduceDIte, Fintype.prod_empty,
      mul_one]
    rw [hlabel input, hlabel output, hboundary]
    simp only [fullLabels]
    by_cases hb :
        (processedLabelsEquivOfAll dim rank k hprocessed labels) output = b <;>
      simp [hb]
  rw [hstate]
  change (∑ labels : ∀ v, Fin (dim v),
      x (labels input) * (if labels output = b then 1 else 0) *
        ∏ e, M e (labels (src e)) (labels (dst e))) =
    (graphOperator dim src dst M input output).transpose.mulVec x b
  rw [Matrix.mulVec, dotProduct]
  simp only [Matrix.transpose_apply, graphOperator]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels _
  by_cases hout : labels output = b
  · simp [hout, mul_comm]
  · simp [hout]

theorem endpointAwareRankCutEnergy_terminal
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (rank : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (hedge : ∀ e, rank (src e) < rank (dst e))
    (input output : ι) (k : ℕ) (hall : ∀ v, rank v < k)
    (x : Fin (dim input) → ℝ) :
    endpointAwareRankCutEnergy dim rank src dst input output k
        (endpointAwareRankCutState dim rank src dst M hedge input output k x) =
      ∑ b, ((graphOperator dim src dst M input output).transpose.mulVec x b) ^ 2 := by
  classical
  rw [endpointAwareRankCutEnergy]
  apply Fintype.sum_equiv
    (endpointAwareTerminalIndexEquiv dim rank src dst input output k hall)
  intro boundary
  rw [endpointAwareRankCutState_terminal dim rank src dst M hedge input output k hall]

/-- Once every adjacent rank cut has its exact finite coefficient
factorization, the remaining induction, endpoint identifications, and passage
from squared energy to the graph-operator norm are automatic. -/
theorem graphOperator_norm_le_of_stepFactorizations
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input output : ι)
    (hdag : MingoAdmissibleDAG src dst input output)
    (hfactor : ∀ (x : Fin (dim input) → ℝ) (k : ℕ),
      k < Fintype.card ι + 1 →
        EndpointAwareRankCutStepFactorization dim (mingoDAGRank src dst)
          src dst M (fun e ↦ hdag.edge_rank_lt src dst input output e)
          input output k x) :
    euclideanOperatorNorm (graphOperator dim src dst M input output) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  classical
  let rank := mingoDAGRank src dst
  let K := Fintype.card ι + 1
  let C := ∏ e, euclideanOperatorNorm (M e)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact Finset.prod_nonneg fun e _ ↦ euclideanOperatorNorm_nonneg (M e)
  have henergy : ∀ x : Fin (dim input) → ℝ,
      (∑ b,
          ((graphOperator dim src dst M input output).transpose.mulVec x b) ^ 2) ≤
        C ^ 2 * ∑ a, (x a) ^ 2 := by
    intro x
    have hcut := endpointAwareRankCutEnergy_le_of_factorizations
      dim rank src dst M
      (fun e ↦ hdag.edge_rank_lt src dst input output e)
      input output x K
      (fun k hk ↦ hfactor x k (by simpa only [K] using hk))
    have hall : ∀ v, rank v < K := by
      intro v
      exact mingoDAGRank_lt_terminalCut src dst v
    rw [endpointAwareRankCutEnergy_terminal dim rank src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output K hall x,
      endpointAwareRankCutEnergy_zero dim rank src dst M
        (fun e ↦ hdag.edge_rank_lt src dst input output e)
        input output x,
      prod_mingoRankEnteringEdges_range src dst
        (fun e ↦ euclideanOperatorNorm (M e) ^ 2)] at hcut
    change _ ≤ C ^ 2 * _
    simpa only [C, Finset.prod_pow] using hcut
  have htranspose := euclideanOperatorNorm_le_of_energy_bound
    (graphOperator dim src dst M input output).transpose C hC henergy
  rw [euclideanOperatorNorm_transpose] at htranspose
  exact htranspose

/-- The graph operator in the allowed degenerate one-vertex/no-edge case is
the identity, including zero-dimensional vertex spaces. -/
theorem graphOperator_eq_one_of_eq_endpoints
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input : ι)
    (hdag : MingoAdmissibleDAG src dst input input) :
    graphOperator dim src dst M input input = 1 := by
  have hsub : Subsingleton ι :=
    hdag.subsingleton_of_eq_endpoints src dst input input rfl
  have hedge : IsEmpty ε :=
    hdag.isEmpty_edges_of_eq_endpoints src dst input input rfl
  let _ : IsEmpty ε := hedge
  classical
  ext a b
  change (∑ labels : ∀ v, Fin (dim v),
    if labels input = a ∧ labels input = b then
      ∏ e, M e (labels (src e)) (labels (dst e))
    else 0) = (1 : Matrix (Fin (dim input)) (Fin (dim input)) ℝ) a b
  calc
    _ = ∑ i : Fin (dim input), if i = a ∧ i = b then (1 : ℝ) else 0 := by
      apply Fintype.sum_equiv
        (piSubsingletonEquiv (fun v ↦ Fin (dim v)) input hsub)
      intro labels
      change (if labels input = a ∧ labels input = b then
        ∏ e, M e (labels (src e)) (labels (dst e)) else 0) =
        if labels input = a ∧ labels input = b then (1 : ℝ) else 0
      rw [Fintype.prod_empty]
    _ = _ := by
      by_cases hab : a = b
      · subst b
        simp
      · simp [hab]

theorem graphOperator_norm_le_edge_product_same_endpoint
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (input : ι)
    (hdag : MingoAdmissibleDAG src dst input input) :
    euclideanOperatorNorm (graphOperator dim src dst M input input) ≤
      ∏ e, euclideanOperatorNorm (M e) := by
  have hedge : IsEmpty ε :=
    hdag.isEmpty_edges_of_eq_endpoints src dst input input rfl
  let _ : IsEmpty ε := hedge
  rw [graphOperator_eq_one_of_eq_endpoints dim src dst M input hdag,
    Fintype.prod_empty]
  exact euclideanOperatorNorm_one_le

end Problem56
