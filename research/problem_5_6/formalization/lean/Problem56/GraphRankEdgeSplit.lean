import Problem56.GraphRankEndpoint

/-!
Exact subdivision of one indexed edge through two new rank-dimensional
vertices.  This is the algebraic preparation for I07 and is independent of
the still-open bridgeless-to-DAG routing in I05.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56

abbrev RankEdgeSplitVertex (ι : Type*) := ι ⊕ Fin 2

inductive RankEdgeSplitLink
  | left
  | middle
  | right
  deriving DecidableEq

abbrev RankEdgeSplitEdge (ε : Type*) (e₀ : ε) :=
  {e : ε // e ≠ e₀} ⊕ RankEdgeSplitLink

def rankEdgeSplitSrc {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    RankEdgeSplitEdge ε e₀ → RankEdgeSplitVertex ι
  | Sum.inl e => Sum.inl (src e.1)
  | Sum.inr .left => Sum.inl (src e₀)
  | Sum.inr .middle => Sum.inr 0
  | Sum.inr .right => Sum.inr 1

def rankEdgeSplitDst {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    RankEdgeSplitEdge ε e₀ → RankEdgeSplitVertex ι
  | Sum.inl e => Sum.inl (dst e.1)
  | Sum.inr .left => Sum.inr 0
  | Sum.inr .middle => Sum.inr 1
  | Sum.inr .right => Sum.inl (dst e₀)

def rankEdgeSplitDim {ι : Type*} (dim : ι → ℕ) (r : ℕ) :
    RankEdgeSplitVertex ι → ℕ
  | Sum.inl v => dim v
  | Sum.inr _ => r

noncomputable def rankEdgeSplitMatrix
    {ι ε : Type*} [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ) :
    ∀ e : RankEdgeSplitEdge ε e₀,
      Matrix (Fin (rankEdgeSplitDim dim r (rankEdgeSplitSrc src dst e₀ e)))
        (Fin (rankEdgeSplitDim dim r (rankEdgeSplitDst src dst e₀ e))) ℝ
  | Sum.inl e => M e.1
  | Sum.inr .left => L
  | Sum.inr .middle => C
  | Sum.inr .right => R

def rankEdgeSplitWeight {ι : Type*} (dim : ι → ℕ) (r : ℕ)
    (w : ∀ v, Fin (dim v) → ℝ) :
    ∀ v : RankEdgeSplitVertex ι, Fin (rankEdgeSplitDim dim r v) → ℝ
  | Sum.inl v => w v
  | Sum.inr _ => fun _ => 1

noncomputable def rankEdgeSplitLabelEquiv
    {ι : Type*} (dim : ι → ℕ) (r : ℕ) :
    (∀ z : RankEdgeSplitVertex ι, Fin (rankEdgeSplitDim dim r z)) ≃
      (∀ v, Fin (dim v)) × (Fin r × Fin r) :=
  (Equiv.sumPiEquivProdPi
    (fun z : RankEdgeSplitVertex ι => Fin (rankEdgeSplitDim dim r z))).trans
      (Equiv.prodCongr (Equiv.refl _) (finTwoArrowEquiv (Fin r)))

@[simp] theorem rankEdgeSplitLabelEquiv_old
    {ι : Type*} (dim : ι → ℕ) (r : ℕ)
    (labels : ∀ z : RankEdgeSplitVertex ι,
      Fin (rankEdgeSplitDim dim r z)) (v : ι) :
    (rankEdgeSplitLabelEquiv dim r labels).1 v = labels (Sum.inl v) := rfl

@[simp] theorem rankEdgeSplitLabelEquiv_left
    {ι : Type*} (dim : ι → ℕ) (r : ℕ)
    (labels : ∀ z : RankEdgeSplitVertex ι,
      Fin (rankEdgeSplitDim dim r z)) :
    (rankEdgeSplitLabelEquiv dim r labels).2.1 = labels (Sum.inr 0) := rfl

@[simp] theorem rankEdgeSplitLabelEquiv_right
    {ι : Type*} (dim : ι → ℕ) (r : ℕ)
    (labels : ∀ z : RankEdgeSplitVertex ι,
      Fin (rankEdgeSplitDim dim r z)) :
    (rankEdgeSplitLabelEquiv dim r labels).2.2 = labels (Sum.inr 1) := rfl

@[simp] theorem rankEdgeSplitSrc_old
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) (e : {e : ε // e ≠ e₀}) :
    rankEdgeSplitSrc src dst e₀ (Sum.inl e) = Sum.inl (src e.1) := rfl

@[simp] theorem rankEdgeSplitDst_old
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) (e : {e : ε // e ≠ e₀}) :
    rankEdgeSplitDst src dst e₀ (Sum.inl e) = Sum.inl (dst e.1) := rfl

@[simp] theorem rankEdgeSplitSrc_zero
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitSrc src dst e₀ (Sum.inr .left) = Sum.inl (src e₀) := rfl

@[simp] theorem rankEdgeSplitDst_zero
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitDst src dst e₀ (Sum.inr .left) = Sum.inr 0 := rfl

@[simp] theorem rankEdgeSplitSrc_one
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitSrc src dst e₀ (Sum.inr .middle) = Sum.inr 0 := rfl

@[simp] theorem rankEdgeSplitDst_one
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitDst src dst e₀ (Sum.inr .middle) = Sum.inr 1 := rfl

@[simp] theorem rankEdgeSplitSrc_two
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitSrc src dst e₀ (Sum.inr .right) = Sum.inr 1 := rfl

@[simp] theorem rankEdgeSplitDst_two
    {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    rankEdgeSplitDst src dst e₀ (Sum.inr .right) = Sum.inl (dst e₀) := rfl

@[simp] theorem rankEdgeSplitMatrix_zero
    {ι ε : Type*} [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ) :
    rankEdgeSplitMatrix dim src dst M e₀ r L C R (Sum.inr .left) = L := rfl

@[simp] theorem rankEdgeSplitMatrix_one
    {ι ε : Type*} [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ) :
    rankEdgeSplitMatrix dim src dst M e₀ r L C R (Sum.inr .middle) = C := rfl

@[simp] theorem rankEdgeSplitMatrix_two
    {ι ε : Type*} [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ) :
    rankEdgeSplitMatrix dim src dst M e₀ r L C R (Sum.inr .right) = R := rfl

private def rankEdgeSplitLinkEquivFin3 : RankEdgeSplitLink ≃ Fin 3 where
  toFun
    | .left => 0
    | .middle => 1
    | .right => 2
  invFun := Fin.cases .left (fun k => Fin.cases .middle (fun _ => .right) k)
  left_inv := by intro k; cases k <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

private noncomputable instance : Fintype RankEdgeSplitLink :=
  Fintype.ofEquiv (Fin 3) rankEdgeSplitLinkEquivFin3.symm

private theorem prod_rankEdgeSplitLink (f : RankEdgeSplitLink → ℝ) :
    (∏ k, f k) = f .left * f .middle * f .right := by
  calc
    (∏ k, f k) = ∏ k : Fin 3, f (rankEdgeSplitLinkEquivFin3.symm k) := by
      apply Fintype.prod_equiv rankEdgeSplitLinkEquivFin3
      intro k
      simp
    _ = f .left * f .middle * f .right := by
      rw [Fin.prod_univ_three]
      rfl

private theorem sum_rankEdgeSplitLink (f : RankEdgeSplitLink → ℕ) :
    (∑ k, f k) = f .left + f .middle + f .right := by
  calc
    (∑ k, f k) = ∑ k : Fin 3, f (rankEdgeSplitLinkEquivFin3.symm k) := by
      apply Fintype.sum_equiv rankEdgeSplitLinkEquivFin3
      intro k
      simp
    _ = f .left + f .middle + f .right := by
      rw [Fin.sum_univ_three]
      rfl

private theorem prod_eq_factor_mul_prod_ne
    {ε : Type*} [Fintype ε] [DecidableEq ε]
    (e₀ : ε) (f : ε → ℝ) :
    (∏ e, f e) = f e₀ * ∏ e : {e : ε // e ≠ e₀}, f e.1 := by
  have hsub : (∏ e : {e : ε // e ≠ e₀}, f e.1) =
      ∏ e ∈ Finset.univ.erase e₀, f e := by
    exact (Finset.prod_subtype (Finset.univ.erase e₀) (by simp) f).symm
  rw [hsub]
  exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e₀)).symm

def rankEdgeSplitAnchor {ι ε : Type*} (src dst : ε → ι) (e₀ : ε) :
    RankEdgeSplitVertex ι → ι
  | Sum.inl v => v
  | Sum.inr k => Fin.cases (src e₀) (fun _ => dst e₀) k

theorem graphConnected_rankEdgeSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε) (hconn : GraphConnected src dst) :
    GraphConnected (rankEdgeSplitSrc src dst e₀)
      (rankEdgeSplitDst src dst e₀) := by
  classical
  let adj := graphAdjacent (rankEdgeSplitSrc src dst e₀)
    (rankEdgeSplitDst src dst e₀)
  have hs0 : adj (Sum.inl (src e₀)) (Sum.inr 0) :=
    ⟨Sum.inr .left, Or.inl ⟨rfl, rfl⟩⟩
  have h0s : adj (Sum.inr 0) (Sum.inl (src e₀)) :=
    ⟨Sum.inr .left, Or.inr ⟨rfl, rfl⟩⟩
  have h01 : adj (Sum.inr 0) (Sum.inr 1) :=
    ⟨Sum.inr .middle, Or.inl ⟨rfl, rfl⟩⟩
  have h10 : adj (Sum.inr 1) (Sum.inr 0) :=
    ⟨Sum.inr .middle, Or.inr ⟨rfl, rfl⟩⟩
  have h1d : adj (Sum.inr 1) (Sum.inl (dst e₀)) :=
    ⟨Sum.inr .right, Or.inl ⟨rfl, rfl⟩⟩
  have hd1 : adj (Sum.inl (dst e₀)) (Sum.inr 1) :=
    ⟨Sum.inr .right, Or.inr ⟨rfl, rfl⟩⟩
  have holdStep : ∀ {a b}, graphAdjacent src dst a b →
      Relation.ReflTransGen adj (Sum.inl a) (Sum.inl b) := by
    intro a b hab
    rcases hab with ⟨e, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      by_cases he : e = e₀
      · subst e
        exact ((Relation.ReflTransGen.single hs0).tail h01).tail h1d
      · exact Relation.ReflTransGen.single
          ⟨Sum.inl ⟨e, he⟩, Or.inl ⟨rfl, rfl⟩⟩
    · rcases h with ⟨rfl, rfl⟩
      by_cases he : e = e₀
      · subst e
        exact ((Relation.ReflTransGen.single hd1).tail h10).tail h0s
      · exact Relation.ReflTransGen.single
          ⟨Sum.inl ⟨e, he⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hold : ∀ a b,
      Relation.ReflTransGen adj (Sum.inl a) (Sum.inl b) := by
    intro a b
    induction hconn a b with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact ih.trans (holdStep hbc)
  have hto : ∀ z : RankEdgeSplitVertex ι,
      Relation.ReflTransGen adj z (Sum.inl (rankEdgeSplitAnchor src dst e₀ z)) := by
    intro z
    rcases z with v | k
    · exact Relation.ReflTransGen.refl
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact Relation.ReflTransGen.single h0s
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        exact Relation.ReflTransGen.single h1d
  have hfrom : ∀ z : RankEdgeSplitVertex ι,
      Relation.ReflTransGen adj
        (Sum.inl (rankEdgeSplitAnchor src dst e₀ z)) z := by
    intro z
    rcases z with v | k
    · exact Relation.ReflTransGen.refl
    · refine Fin.cases ?_ (fun j => ?_) k
      · exact Relation.ReflTransGen.single hs0
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        exact Relation.ReflTransGen.single hd1
  intro x y
  exact (hto x).trans ((hold _ _).trans (hfrom y))

theorem graphDegree_rankEdgeSplit_old
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε) (v : ι) :
    graphDegree (rankEdgeSplitSrc src dst e₀)
        (rankEdgeSplitDst src dst e₀) (Sum.inl v) =
      graphDegree src dst v := by
  classical
  unfold graphDegree
  have hsrc :
      (Finset.univ.filter fun e : RankEdgeSplitEdge ε e₀ =>
        rankEdgeSplitSrc src dst e₀ e = Sum.inl v).card =
      (Finset.univ.filter fun e : ε => src e = v).card := by
    simp only [Finset.card_filter, Finset.mem_univ, if_true]
    rw [Fintype.sum_sum_type, sum_rankEdgeSplitLink]
    simp only [rankEdgeSplitSrc, Sum.inl.injEq, Sum.inr_ne_inl,
      if_false, add_zero]
    rw [← Finset.add_sum_erase Finset.univ
      (fun e => if src e = v then 1 else 0) (Finset.mem_univ e₀)]
    rw [Finset.sum_subtype (p := fun e : ε => e ≠ e₀)
      (Finset.univ.erase e₀) (by simp)
      (fun e => if src e = v then 1 else 0)]
    omega
  have hdst :
      (Finset.univ.filter fun e : RankEdgeSplitEdge ε e₀ =>
        rankEdgeSplitDst src dst e₀ e = Sum.inl v).card =
      (Finset.univ.filter fun e : ε => dst e = v).card := by
    simp only [Finset.card_filter, Finset.mem_univ, if_true]
    rw [Fintype.sum_sum_type, sum_rankEdgeSplitLink]
    simp only [rankEdgeSplitDst, Sum.inl.injEq, Sum.inr_ne_inl,
      if_false, zero_add, add_zero]
    rw [← Finset.add_sum_erase Finset.univ
      (fun e => if dst e = v then 1 else 0) (Finset.mem_univ e₀)]
    rw [Finset.sum_subtype (p := fun e : ε => e ≠ e₀)
      (Finset.univ.erase e₀) (by simp)
      (fun e => if dst e = v then 1 else 0)]
    omega
  rw [hsrc, hdst]

theorem graphDegree_rankEdgeSplit_left
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε) :
    graphDegree (rankEdgeSplitSrc src dst e₀)
      (rankEdgeSplitDst src dst e₀) (Sum.inr 0) = 2 := by
  classical
  unfold graphDegree
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type, sum_rankEdgeSplitLink,
    Fintype.sum_sum_type, sum_rankEdgeSplitLink]
  simp [rankEdgeSplitSrc, rankEdgeSplitDst]

theorem graphDegree_rankEdgeSplit_right
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε) :
    graphDegree (rankEdgeSplitSrc src dst e₀)
      (rankEdgeSplitDst src dst e₀) (Sum.inr (Fin.succ 0)) = 2 := by
  classical
  unfold graphDegree
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type, sum_rankEdgeSplitLink,
    Fintype.sum_sum_type, sum_rankEdgeSplitLink]
  simp [rankEdgeSplitSrc, rankEdgeSplitDst]

theorem graphEven_rankEdgeSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε)
    (heven : ∀ v, Even (graphDegree src dst v)) :
    ∀ z, Even (graphDegree (rankEdgeSplitSrc src dst e₀)
      (rankEdgeSplitDst src dst e₀) z) := by
  intro z
  rcases z with v | k
  · rw [graphDegree_rankEdgeSplit_old]
    exact heven v
  · refine Fin.cases ?_ (fun j => ?_) k
    · rw [graphDegree_rankEdgeSplit_left]
      norm_num
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [graphDegree_rankEdgeSplit_right]
      norm_num

theorem graphPositive_rankEdgeSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (src dst : ε → ι) (e₀ : ε)
    (hpositive : ∀ v, 0 < graphDegree src dst v) :
    ∀ z, 0 < graphDegree (rankEdgeSplitSrc src dst e₀)
      (rankEdgeSplitDst src dst e₀) z := by
  intro z
  rcases z with v | k
  · rw [graphDegree_rankEdgeSplit_old]
    exact hpositive v
  · refine Fin.cases ?_ (fun j => ?_) k
    · rw [graphDegree_rankEdgeSplit_left]
      norm_num
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      rw [graphDegree_rankEdgeSplit_right]
      norm_num

theorem euclideanOperatorNorm_frame_le_one
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) (hV : OrthonormalFrame V) :
    euclideanOperatorNorm V ≤ 1 := by
  rw [euclideanOperatorNorm_eq_l2_opNorm]
  have hreal : V.conjTranspose = V.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hreal, hV] at hsq
  have hone : ‖(1 : Matrix (Fin r) (Fin r) ℝ)‖ ≤ 1 := by
    simpa only [← euclideanOperatorNorm_eq_l2_opNorm] using
      (euclideanOperatorNorm_one_le (α := Fin r))
  nlinarith [norm_nonneg V]

theorem rankEdgeSplitMatrix_norm_le_one
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ)
    (hM : ∀ e, euclideanOperatorNorm (M e) ≤ 1)
    (hL : euclideanOperatorNorm L ≤ 1)
    (hC : euclideanOperatorNorm C ≤ 1)
    (hR : euclideanOperatorNorm R ≤ 1) :
    ∀ e, euclideanOperatorNorm
      (rankEdgeSplitMatrix dim src dst M e₀ r L C R e) ≤ 1 := by
  intro e
  rcases e with e | k
  · exact hM e.1
  · rcases k with _ | _ | _
    · exact hL
    · exact hC
    · exact hR

private theorem frame_factorization_of_heq
    {a b n r : ℕ}
    (M : Matrix (Fin a) (Fin b) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ)
    (ha : a = n) (hb : b = n)
    (hV : OrthonormalFrame V) (hM : HEq M (V * V.transpose)) :
    ∃ (L : Matrix (Fin a) (Fin r) ℝ)
      (R : Matrix (Fin r) (Fin b) ℝ),
      M = L * (1 : Matrix (Fin r) (Fin r) ℝ) * R ∧
      euclideanOperatorNorm L ≤ 1 ∧ euclideanOperatorNorm R ≤ 1 := by
  subst a
  subst b
  have hMeq : M = V * V.transpose := eq_of_heq hM
  refine ⟨V, V.transpose, ?_, euclideanOperatorNorm_frame_le_one V hV, ?_⟩
  · simpa using hMeq
  · rw [euclideanOperatorNorm_transpose]
    exact euclideanOperatorNorm_frame_le_one V hV

theorem hasRankProjectionEdge_factorization
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (r : ℕ) (hrank : HasRankProjectionEdge dim src dst M r) :
    ∃ (e₀ : ε)
      (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
      (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ),
      M e₀ = L * (1 : Matrix (Fin r) (Fin r) ℝ) * R ∧
      euclideanOperatorNorm L ≤ 1 ∧ euclideanOperatorNorm R ≤ 1 := by
  rcases hrank with ⟨e₀, n, V, hsrc, hdst, hV, hM⟩
  obtain ⟨L, R, hfactor, hL, hR⟩ :=
    frame_factorization_of_heq (M e₀) V hsrc hdst hV hM
  exact ⟨e₀, L, R, hfactor, hL, hR⟩

set_option maxHeartbeats 800000 in
theorem graphContraction_rankEdgeSplit
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] [DecidableEq ε]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (e₀ : ε) (r : ℕ)
    (L : Matrix (Fin (dim (src e₀))) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (R : Matrix (Fin r) (Fin (dim (dst e₀))) ℝ)
    (hfactor : M e₀ = L * C * R) :
    graphContraction (rankEdgeSplitDim dim r)
        (rankEdgeSplitSrc src dst e₀) (rankEdgeSplitDst src dst e₀)
        (rankEdgeSplitMatrix dim src dst M e₀ r L C R)
        (rankEdgeSplitWeight dim r w) =
      graphContraction dim src dst M w := by
  classical
  simp only [graphContraction]
  rw [show (∑ labels : ∀ z : RankEdgeSplitVertex ι,
      Fin (rankEdgeSplitDim dim r z),
      (∏ e : RankEdgeSplitEdge ε e₀,
        rankEdgeSplitMatrix dim src dst M e₀ r L C R e
          (labels (rankEdgeSplitSrc src dst e₀ e))
          (labels (rankEdgeSplitDst src dst e₀ e))) *
        ∏ v, rankEdgeSplitWeight dim r w v (labels v)) =
      ∑ z : (∀ v, Fin (dim v)) × (Fin r × Fin r),
      let labels := z.1
      let a := z.2.1
      let b := z.2.2
      ((∏ e : {e : ε // e ≠ e₀},
          M e.1 (labels (src e.1)) (labels (dst e.1))) *
        (L (labels (src e₀)) a * C a b * R b (labels (dst e₀)))) *
        ∏ v, w v (labels v) by
    apply Fintype.sum_equiv (rankEdgeSplitLabelEquiv dim r)
    intro labels
    simp only
    rw [Fintype.prod_sum_type, prod_rankEdgeSplitLink,
      Fintype.prod_sum_type]
    simp [rankEdgeSplitMatrix, rankEdgeSplitWeight,
      rankEdgeSplitSrc, rankEdgeSplitDst, rankEdgeSplitDim]
    simp only [← rankEdgeSplitLabelEquiv_old dim r labels,
      ← rankEdgeSplitLabelEquiv_left dim r labels,
      ← rankEdgeSplitLabelEquiv_right dim r labels]
    rfl]
  rw [Fintype.sum_prod_type]
  simp only
  apply Finset.sum_congr rfl
  intro labels _
  rw [Fintype.sum_prod_type]
  rw [show (∑ a, ∑ b,
      ((∏ e : {e : ε // e ≠ e₀},
          M e.1 (labels (src e.1)) (labels (dst e.1))) *
        (L (labels (src e₀)) a * C a b * R b (labels (dst e₀)))) *
        ∏ v, w v (labels v)) =
      (∏ e : {e : ε // e ≠ e₀},
          M e.1 (labels (src e.1)) (labels (dst e.1))) *
        (∑ a, ∑ b, L (labels (src e₀)) a * C a b *
          R b (labels (dst e₀))) *
        ∏ v, w v (labels v) by
    let A := ∏ e : {e : ε // e ≠ e₀},
      M e.1 (labels (src e.1)) (labels (dst e.1))
    let W := ∏ v, w v (labels v)
    change (∑ a, ∑ b,
      (A * (L (labels (src e₀)) a * C a b * R b (labels (dst e₀)))) * W) =
      A * (∑ a, ∑ b, L (labels (src e₀)) a * C a b *
        R b (labels (dst e₀))) * W
    calc
      _ = ∑ a, ∑ b, (A * W) *
          (L (labels (src e₀)) a * C a b * R b (labels (dst e₀))) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ a, (A * W) * (∑ b,
          L (labels (src e₀)) a * C a b * R b (labels (dst e₀))) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = (A * W) * (∑ a, ∑ b,
          L (labels (src e₀)) a * C a b * R b (labels (dst e₀))) := by
        rw [Finset.mul_sum]
      _ = A * (∑ a, ∑ b, L (labels (src e₀)) a * C a b *
          R b (labels (dst e₀))) * W := by ring]
  rw [show (∑ a, ∑ b, L (labels (src e₀)) a * C a b *
      R b (labels (dst e₀))) = (L * C * R) (labels (src e₀))
        (labels (dst e₀)) by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul],
    ← hfactor,
    prod_eq_factor_mul_prod_ne e₀]
  ring

end Problem56

#print axioms Problem56.graphConnected_rankEdgeSplit
#print axioms Problem56.graphDegree_rankEdgeSplit_old
#print axioms Problem56.graphEven_rankEdgeSplit
#print axioms Problem56.graphPositive_rankEdgeSplit
#print axioms Problem56.euclideanOperatorNorm_frame_le_one
#print axioms Problem56.hasRankProjectionEdge_factorization
#print axioms Problem56.graphContraction_rankEdgeSplit
#print axioms Problem56.rankEdgeSplitMatrix_norm_le_one
