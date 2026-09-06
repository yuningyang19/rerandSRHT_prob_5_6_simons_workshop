import Problem56.PaperV6.GeneralBridgelessDAGSplit

namespace Problem56.PaperV6

abbrev AdjoinedEarVertex (ι : Type*) (k : ℕ) := ι ⊕ Fin k
abbrev AdjoinedEarEdge (ε : Type*) (k : ℕ) := ε ⊕ Fin (k + 1)

/-- Points on a new path with `k` fresh internal vertices. Only the two end
points are identified with vertices in the current graph. -/
def adjoinedEarPoint {ι : Type*} (x y : ι) (k : ℕ) (i : Fin (k + 2)) :
    AdjoinedEarVertex ι k :=
  if hzero : i.1 = 0 then Sum.inl x
  else if hlast : i.1 = k + 1 then Sum.inl y
  else Sum.inr ⟨i.1 - 1, by omega⟩

def adjoinedEarSrc {ι ε : Type*} (src : ε → ι) (x y : ι) (k : ℕ) :
    AdjoinedEarEdge ε k → AdjoinedEarVertex ι k
  | Sum.inl e => Sum.inl (src e)
  | Sum.inr i => adjoinedEarPoint x y k i.castSucc

def adjoinedEarDst {ι ε : Type*} (dst : ε → ι) (x y : ι) (k : ℕ) :
    AdjoinedEarEdge ε k → AdjoinedEarVertex ι k
  | Sum.inl e => Sum.inl (dst e)
  | Sum.inr i => adjoinedEarPoint x y k i.succ

@[simp] theorem adjoinedEarPoint_zero {ι : Type*} (x y : ι) (k : ℕ) :
    adjoinedEarPoint x y k 0 = Sum.inl x := by
  simp [adjoinedEarPoint]

@[simp] theorem adjoinedEarPoint_last {ι : Type*} (x y : ι) (k : ℕ) :
    adjoinedEarPoint x y k (Fin.last (k + 1)) = Sum.inl y := by
  simp [adjoinedEarPoint]

@[simp] theorem adjoinedEarPoint_internal {ι : Type*} (x y : ι) (k : ℕ)
    (i : Fin k) :
    adjoinedEarPoint x y k ⟨i.1 + 1, by omega⟩ = Sum.inr i := by
  have hi : i.1 ≠ k := by omega
  simp [adjoinedEarPoint, hi]

theorem adjoinedEar_step {ι ε : Type*} (src dst : ε → ι) (x y : ι) (k : ℕ)
    (i : Fin (k + 1)) :
    directedAdjacent (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k)
      (adjoinedEarPoint x y k i.castSucc) (adjoinedEarPoint x y k i.succ) :=
  ⟨Sum.inr i, rfl, rfl⟩

theorem adjoinedEar_from_start {ι ε : Type*} (src dst : ε → ι) (x y : ι)
    (k : ℕ) (i : Fin (k + 2)) :
    Relation.ReflTransGen
      (directedAdjacent (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k))
      (Sum.inl x) (adjoinedEarPoint x y k i) := by
  induction i using Fin.induction with
  | zero => simpa using (Relation.ReflTransGen.refl (a := Sum.inl x))
  | succ i ih => exact ih.tail (adjoinedEar_step src dst x y k i)

theorem adjoinedEar_to_end {ι ε : Type*} (src dst : ε → ι) (x y : ι)
    (k : ℕ) (i : Fin (k + 2)) :
    Relation.ReflTransGen
      (directedAdjacent (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k))
      (adjoinedEarPoint x y k i) (Sum.inl y) := by
  induction i using Fin.reverseInduction with
  | last => simpa using (Relation.ReflTransGen.refl (a := Sum.inl y))
  | cast i ih => exact ih.head (adjoinedEar_step src dst x y k i)

def adjoinedEarRank {ι : Type*} (rank : ι → ℕ) (x : ι) (k : ℕ) :
    AdjoinedEarVertex ι k → ℕ
  | Sum.inl v => rank v * (k + 1)
  | Sum.inr i => rank x * (k + 1) + i.1 + 1

theorem adjoinedEarPoint_rank_before_last {ι : Type*} (rank : ι → ℕ)
    (x y : ι) (k : ℕ) (i : Fin (k + 2)) (hi : i.1 < k + 1) :
    adjoinedEarRank rank x k (adjoinedEarPoint x y k i) =
      rank x * (k + 1) + i.1 := by
  by_cases hz : i.1 = 0
  · simp [adjoinedEarPoint, hz, adjoinedEarRank]
  · have hl : i.1 ≠ k + 1 := by omega
    simp only [adjoinedEarPoint, dif_neg hz, dif_neg hl, adjoinedEarRank]
    omega

theorem adjoinedEar_edge_rank_lt {ι ε : Type*} (src dst : ε → ι)
    (rank : ι → ℕ) (hedge : ∀ e, rank (src e) < rank (dst e))
    (x y : ι) (hxy : rank x < rank y) (k : ℕ) (e : AdjoinedEarEdge ε k) :
    adjoinedEarRank rank x k (adjoinedEarSrc src x y k e) <
      adjoinedEarRank rank x k (adjoinedEarDst dst x y k e) := by
  cases e with
  | inl e =>
    exact Nat.mul_lt_mul_of_pos_right (hedge e) (by omega)
  | inr i =>
    change adjoinedEarRank rank x k (adjoinedEarPoint x y k i.castSucc) <
      adjoinedEarRank rank x k (adjoinedEarPoint x y k i.succ)
    rw [adjoinedEarPoint_rank_before_last rank x y k i.castSucc (by exact i.2)]
    by_cases hi : i.1 < k
    · rw [adjoinedEarPoint_rank_before_last rank x y k i.succ (by simp; omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    · have hi' : i.1 = k := by omega
      have hlast : i.succ = Fin.last (k + 1) := by ext; simp; omega
      rw [hlast, adjoinedEarPoint_last]
      change rank x * (k + 1) + i.1 < rank y * (k + 1)
      rw [hi']
      nlinarith

theorem adjoinedEar_lift_old_walk {ι ε : Type*} (src dst : ε → ι)
    (x y : ι) (k : ℕ) {a b : ι}
    (h : Relation.ReflTransGen (directedAdjacent src dst) a b) :
    Relation.ReflTransGen
      (directedAdjacent (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k))
      (Sum.inl a) (Sum.inl b) := by
  apply h.lift Sum.inl
  intro a b hab
  obtain ⟨e, rfl, rfl⟩ := hab
  exact ⟨Sum.inl e, rfl, rfl⟩

/-- Insert a concrete directed path between two vertices ordered by a strict
topological rank. Its internal vertices and indexed edges are fresh. The DAG
and both prescribed boundary reachability properties are proved, not assumed
as fields of a routing object. -/
theorem adjoinedEar_mingoAdmissibleDAG {ι ε : Type*} (src dst : ε → ι)
    (input output : ι) (hdag : MingoAdmissibleDAG src dst input output)
    (rank : ι → ℕ) (hedge : ∀ e, rank (src e) < rank (dst e))
    (x y : ι) (hxy : rank x < rank y) (k : ℕ) :
    MingoAdmissibleDAG (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k)
      (Sum.inl input) (Sum.inl output) := by
  have hfrom : ∀ v, Relation.ReflTransGen (directedAdjacent src dst) input v := by
    intro v
    rcases hdag.2.1 v with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact h.to_reflTransGen
  have hto : ∀ v, Relation.ReflTransGen (directedAdjacent src dst) v output := by
    intro v
    rcases hdag.2.2 v with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact h.to_reflTransGen
  refine ⟨?_, ?_, ?_⟩
  · intro v hcycle
    exact (Nat.lt_irrefl _) (transGen_strict_rank _ _ (adjoinedEarRank rank x k)
      (adjoinedEar_edge_rank_lt src dst rank hedge x y hxy k) hcycle)
  · intro v
    apply Relation.reflTransGen_iff_eq_or_transGen.mp
    cases v with
    | inl v => exact adjoinedEar_lift_old_walk src dst x y k (hfrom v)
    | inr i =>
      have hpath := adjoinedEar_from_start src dst x y k ⟨i.1 + 1, by omega⟩
      rw [adjoinedEarPoint_internal] at hpath
      exact (adjoinedEar_lift_old_walk src dst x y k (hfrom x)).trans hpath
  · intro v
    have h : Relation.ReflTransGen
        (directedAdjacent (adjoinedEarSrc src x y k) (adjoinedEarDst dst x y k))
        v (Sum.inl output) := by
      cases v with
      | inl v => exact adjoinedEar_lift_old_walk src dst x y k (hto v)
      | inr i =>
        have hpath := adjoinedEar_to_end src dst x y k ⟨i.1 + 1, by omega⟩
        rw [adjoinedEarPoint_internal] at hpath
        exact hpath.trans (adjoinedEar_lift_old_walk src dst x y k (hto y))
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with heq | hpath
    · exact Or.inl heq.symm
    · exact Or.inr hpath

end Problem56.PaperV6
