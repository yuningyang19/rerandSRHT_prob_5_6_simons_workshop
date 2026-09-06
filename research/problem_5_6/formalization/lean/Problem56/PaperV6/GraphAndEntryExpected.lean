import Problem56.Definitions

/-!
Reviewer-owned expected propositions for the frozen v6 graph, binary, and
per-equality-pattern results. These are definitions only, not theorem claims.
Graph matrices use the manuscript's target-row/source-column convention.
The entry contribution keeps the exact fixed d,h class, with absolute values
inside both finite sums. No conclusion is included as an input hypothesis.
-/

open scoped BigOperators Matrix

namespace Problem56.PaperV6

noncomputable def paperGraphContraction {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) : ℝ :=
  ∑ labels : ∀ v, Fin (dim v),
    (∏ e, M e (labels (dst e)) (labels (src e))) *
      ∏ v, w v (labels v)

/-- The guarded full labeling sum is an explicit finite-sum representation of
summing internal labels with distinct boundary labels fixed. -/
noncomputable def paperBoundaryMatrix {ι ε : Type*}
    [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (input output : ι) : Matrix (Fin (dim output)) (Fin (dim input)) ℝ :=
  fun b a ↦ ∑ labels : ∀ v, Fin (dim v),
    if labels input = a ∧ labels output = b then
      ∏ e, M e (labels (dst e)) (labels (src e))
    else 0

/-- Explicit manuscript orientation, acyclicity and source/sink conditions. -/
def PaperInputOutput {ι ε : Type*} (src dst : ε → ι) (input output : ι) : Prop :=
  input ≠ output ∧
  (∀ v, ¬ Relation.TransGen (directedAdjacent src dst) v v) ∧
  (∀ e, dst e ≠ input) ∧ (∀ e, src e ≠ output) ∧
  (∀ v, Relation.ReflTransGen (directedAdjacent src dst) input v ∧
    Relation.ReflTransGen (directedAdjacent src dst) v output)

def PaperHasRankProjectionEdge {ι ε : Type*} [Fintype ι] [Fintype ε]
    [DecidableEq ι] (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (r : ℕ) : Prop :=
  ∃ (e₀ : ε) (n : ℕ) (V : Matrix (Fin n) (Fin r) ℝ),
    dim (src e₀) = n ∧ dim (dst e₀) = n ∧
    OrthonormalFrame V ∧ HEq (M e₀) (V * V.transpose)

def GraphOrientationExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (input output : ι),
    paperGraphContraction dim src dst M w =
      graphContraction dim src dst (fun e ↦ (M e).transpose) w ∧
    paperBoundaryMatrix dim src dst M input output =
      (graphOperator dim src dst (fun e ↦ (M e).transpose) input output).transpose ∧
    (PaperInputOutput src dst input output ↔
      input ≠ output ∧ MingoAdmissibleDAG src dst input output)

def GraphBoundaryExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (input output : ι), input ≠ output →
    paperGraphContraction dim src dst M (fun _ _ ↦ 1) =
      ∑ b, ∑ a, paperBoundaryMatrix dim src dst M input output b a

def GraphOperatorExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (input output : ι), PaperInputOutput src dst input output →
    euclideanOperatorNorm (paperBoundaryMatrix dim src dst M input output) ≤
      ∏ e, euclideanOperatorNorm (M e)

def GraphRankExpected : Prop :=
  ∀ (ι ε : Type) [Fintype ι] [Fintype ε] [DecidableEq ι]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (dst e))) (Fin (dim (src e))) ℝ)
    (w : ∀ v, Fin (dim v) → ℝ) (r : ℕ),
    GraphConnected src dst → (∀ v, Even (graphDegree src dst v)) →
    (∀ v, 0 < graphDegree src dst v) →
    (∀ e, euclideanOperatorNorm (M e) ≤ 1) →
    (∀ v i, |w v i| ≤ 1) → 1 ≤ r →
    PaperHasRankProjectionEdge dim src dst M r →
    |paperGraphContraction dim src dst M w| ≤ r

noncomputable def paperBlockCumulant {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (Q : SelectorEqualityData p s t)
    (lab : EqualityVertex Q.1 → WalshIndex m) (B : Finset (Fin (2 * p))) : ℝ :=
  jointCumulantOn (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
    (fun e : B ↦ fun signs ↦
      (randomProjection signs.1 signs.2 V - ((r : ℝ) / walshCard m) • 1)
        (lab (equalityVertexAt Q.1 e.1))
        (lab (equalityVertexAt Q.1 (cyclicSucc e.1))))

noncomputable def paperEntryCumulantProduct {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (Q : SelectorEqualityData p s t)
    (lab : EqualityVertex Q.1 → WalshIndex m)
    (P : Finpartition (Finset.univ : Finset (Fin (2 * p)))) : ℝ :=
  ∏ B ∈ P.parts, paperBlockCumulant V Q lab B

noncomputable def paperSelectorCoefficient {p s t : ℕ}
    (θ : ℝ) (Q : SelectorEqualityData p s t) : ℝ :=
  ∏ B ∈ Q.1.parts, (θ * (1 - θ) ^ B.card + (1 - θ) * (-θ) ^ B.card)

def PaperXorConstraints {m p s t : ℕ} (D : EntryCumulantPartitionData p s t)
    (lab : EqualityVertex D.selector.1 → WalshIndex m) : Prop :=
  ∀ B ∈ D.entry.parts, (∑ e ∈ B,
    (lab (equalityVertexAt D.selector.1 e) +
      lab (equalityVertexAt D.selector.1 (cyclicSucc e)))) = 0

def PaperForbiddenPairBlock {p s t : ℕ} (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))) : Prop :=
  B.card = 2 ∧ ∃ e ∈ B, ∃ f ∈ B, e ≠ f ∧
    let u := equalityVertexAt Q.1 e
    let v := equalityVertexAt Q.1 (cyclicSucc e)
    let w := equalityVertexAt Q.1 f
    let z := equalityVertexAt Q.1 (cyclicSucc f)
    ((u = v ∧ w ≠ z) ∨ (u ≠ v ∧ w = z) ∨
      (u ≠ v ∧ w ≠ z ∧
        ¬ Disjoint ({u, v} : Finset (EqualityVertex Q.1)) {w, z} ∧
        ({u, v} : Finset (EqualityVertex Q.1)) ≠ {w, z}))

def BinaryForbiddenPairExpected : Prop :=
  ∀ (m r p s t : ℕ) (V : Matrix (WalshIndex m) (Fin r) ℝ),
    OrthonormalFrame V → ∀ (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))), PaperForbiddenPairBlock Q B →
    ∀ lab : EqualityVertex Q.1 → WalshIndex m, Function.Injective lab →
      paperBlockCumulant V Q lab B = 0

def BinaryCountExpected : Prop := by
  classical
  exact ∀ (m p s t : ℕ) (D : EntryCumulantPartitionData p s t),
    Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
      PaperXorConstraints D lab} =
      walshCard m ^ (D.selector.1.parts.card - Matrix.rank (entryConstraintMatrix D)) ∧
    Fintype.card {lab : EqualityVertex D.selector.1 → WalshIndex m //
      Function.Injective lab ∧ PaperXorConstraints D lab} ≤
      walshCard m ^ (D.selector.1.parts.card - Matrix.rank (entryConstraintMatrix D))

def BinaryOddIncidenceExpected : Prop :=
  ∀ (p s t d : ℕ), 2 ≤ p → ∀ D : EntryCumulantPartitionData p s t,
    (∀ B ∈ D.entry.parts, 2 ≤ B.card) → D.entry.parts.card = p - d →
    (∀ B ∈ D.entry.parts, ¬ PaperForbiddenPairBlock D.selector B) →
    t ≤ 12 * d + 4 * Matrix.rank (entryConstraintMatrix D)

def EntryWeightedCountExpected : Prop :=
  ∀ (p s t : ℕ), 2 ≤ p → ∀ (Q : SelectorEqualityData p s t) (d h : ℕ),
    aggregateEntryPartitionCumulantSum Q d h ≤
      (3 * K₂) ^ p * (4 * p + 1) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) ∧
    (Nonempty (AggregateEntryPartition Q d h) → t ≤ 12 * d + 4 * h)

/-- The exact absolute contribution of the fixed (d,h) class. -/
noncomputable def paperEntryAbsoluteContribution {m r p s t : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ)
    (Q : SelectorEqualityData p s t) (d h : ℕ) : ℝ := by
  classical
  exact |paperSelectorCoefficient θ Q| *
    ∑ P : AggregateEntryPartition Q d h,
      ∑ lab : {lab : EqualityVertex Q.1 → WalshIndex m // Function.Injective lab},
        |paperEntryCumulantProduct V Q lab.1 P.1|

def EntryAbsoluteContributionExpected : Prop :=
  ∀ (m r p s t : ℕ), 2 ≤ p → 1 ≤ r →
    ∀ (V : Matrix (WalshIndex m) (Fin r) ℝ), OrthonormalFrame V →
    ∀ (θ : ℝ), 0 < θ → θ ≤ 1 / 2 →
    ∀ (Q : SelectorEqualityData p s t) (d h : ℕ),
    paperEntryAbsoluteContribution V θ Q d h ≤
      ((3 * K₂ : ℕ) : ℝ) ^ p *
      ((4 * p + 1 : ℕ) : ℝ) ^ (84 * d + 12 * h + 9 * s + 2 * t + 1) *
      (((r : ℝ) / walshCard m) * θ) ^ p *
      (((walshCard m : ℝ) * θ) ^ (-(s : ℤ)) *
        (r : ℝ) ^ (-(d : ℤ)) * (walshCard m : ℝ) ^ (-(h : ℤ)))

end Problem56.PaperV6
