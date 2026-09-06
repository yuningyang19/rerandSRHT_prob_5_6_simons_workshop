import Problem56.PaperV6.ExpectedTraceChecks
import Problem56.PaperV6.FixedFrame
import Problem56.PaperV6.GeneralCumulants
import Problem56.PaperV6.EntryBridges
import Problem56.PaperV6.NamedResults
import Problem56.PaperV6.GraphModifications
import Problem56.PaperV6.GeneralSamplingJoint
import Problem56.PaperV6.ExpectedFormalLogChecks
import Problem56.PaperV6.ExpectedContinuousChecks
import Problem56.PaperV6.ExpectedGraphHistoryChecks

/-!
Independent reviewer-owned source-interface checks. The additive expected
Props were frozen and independently approved before their proof generation.
These examples ask Lean to assign the actual theorem term to that separate
expected type; they do not compare a generated type manifest to itself.
Baseline named statements below instantiate the independently frozen C
inventory scopes, including their standing Walsh/real law conventions.
No broad general-bridgeless/history check is asserted before a proof exists.
-/

open scoped BigOperators Matrix
namespace Problem56.PaperV6

-- I-V6-02 and the fixed-frame reading of Theorem 1.
example : FixedFrameOSE := fixed_frame_ose

example {m r k : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    SquaredNormEdges ε V d₁ d₂ J ↔
      euclideanOperatorNorm (compressedGram V d₁ d₂ J - 1) ≤ ε :=
  squared_edges_iff_spectral_bound ε hε V hV d₁ d₂ J

example :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          ∀ V : Matrix (WalshIndex m) (Fin r) ℝ, OrthonormalFrame V →
            99 / 100 ≤ uniformProbability
              (fun ω : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
                  FixedSubset (WalshIndex m) k ↦
                SquaredNormEdges ε V ω.1 ω.2.1 ω.2.2) :=
  fixed_frame_squared_norm_success

-- All six separate general finite-moment cumulant clauses, then conjunction.
example : GeneralMomentIdentityExpected := generalMomentIdentity
example : GeneralProductIdentityExpected := generalProductIdentity
example : GeneralMultilinearityExpected := generalMultilinearity
example : GeneralMixedIndependenceExpected := generalMixedIndependence
example : GeneralShiftInvarianceExpected := generalShiftInvariance
example : GeneralOddSymmetryExpected := generalOddSymmetry
example : GeneralMomentIdentityExpected ∧ GeneralProductIdentityExpected ∧
    GeneralMultilinearityExpected ∧ GeneralMixedIndependenceExpected ∧
    GeneralShiftInvarianceExpected ∧ GeneralOddSymmetryExpected :=
  generalCumulantIdentities

-- Exact C graph orientation, boundary, DAG operator and projection contraction.
example : GraphOrientationExpected := graph_orientation
example : GraphBoundaryExpected := graph_boundary
example : GraphOperatorExpected := graph_operator
example : GraphRankExpected := graph_rank
example : FiberBoundaryExpected := graph_fiber_boundary
example : ReversalBoundaryExpected := graph_reversal_boundary

-- I-V6-11 keeps identity norm exactly one in positive coordinate dimensions.
example {n : ℕ} (hn : 0 < n) :
    euclideanOperatorNorm (weightDiagonal (fun _ : Fin n ↦ (1 : ℝ))) = 1 :=
  paper_identity_norm hn

example {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    {copy : ι → Type*} [∀ v, Fintype (copy v)] [∀ v, DecidableEq (copy v)]
    (dim : ι → ℕ) (src dst : ε → ι)
    (M : ∀ e, Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ)
    (srcCopy : ∀ e, copy (src e)) (dstCopy : ∀ e, copy (dst e))
    (rootCopy : ∀ v, copy v) (hdim : ∀ v, 0 < dim v) :
    (∏ e : FiberSplitEdge ε copy,
      euclideanOperatorNorm (fiberSplitMatrix dim src dst M srcCopy dstCopy rootCopy e)) =
      ∏ e, euclideanOperatorNorm (M e) :=
  graph_fiber_norm_product dim src dst M srcCopy dstCopy rootCopy hdim

-- Exact three-clause binary lemma and both per-class entry contribution clauses.
example : BinaryForbiddenPairExpected := binary_forbidden_pair
example : BinaryCountExpected := binary_count
example : BinaryOddIncidenceExpected := binary_odd_incidence
example : EntryWeightedCountExpected := entry_weighted_count
example : EntryAbsoluteContributionExpected := entry_absolute_contribution

-- Unique named endpoints retain every separately frozen clause.
example : BinaryForbiddenPairExpected ∧ BinaryCountExpected ∧ BinaryOddIncidenceExpected :=
  v6_binary_constraints
example : EntryWeightedCountExpected ∧ EntryAbsoluteContributionExpected :=
  v6_entry_contribution

-- Arbitrary frame law, generic independent finite law, and the exact client.
example : GeneralSamplingExpected := general_sampling
example : FiniteNoiseFailureLawExpected := finiteNoiseFailureLaw
example : GeneralSamplingJointExpected := general_sampling_joint

-- Theorem 1's supremum and quantifier order; the explicit C identity strengthens C.
example :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          spectralFailureSup m r k ε ≤ 1 / 100 :=
  main_universal_ose

-- Lemma 2: independent delta, arbitrary real projections, both conclusions.
example {α : Type*} [Fintype α] [DecidableEq α] {r p : ℕ}
    (X : Matrix α (Fin r) ℝ) (E : Matrix α α ℝ)
    (hX : OrthonormalFrame X) (hE : IsOrthogonalProjection E)
    (δ θ : ℝ) (hp : 1 ≤ p)
    (hδ : 0 < δ ∧ δ ≤ 1 / 2) (hθ : 0 < θ ∧ θ ≤ 1 / 2) :
    let A := (X * X.transpose - δ • 1) * (E - θ • 1)
    let a2 := δ * (1 - δ) * θ * (1 - θ)
    Matrix.trace (A ^ (2 * p)) ≥ -2 * r * a2 ^ p ∧
      ∀ η : ℝ, 0 < η → η < 1 → δ ≤ θ * η ^ 2 / 64 →
        (if euclideanOperatorNorm (θ⁻¹ • (X.transpose * E * X) - 1) > η
          then (θ * η / 2) ^ (2 * p) else 0) ≤
          Matrix.trace (A ^ (2 * p)) + 2 * r * a2 ^ p :=
  two_projection_spectral_transfer X E hX hE δ θ hp hδ hθ

-- Proposition 3: absolute value outside the signed expectation.
example {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (θ : ℝ) (hp : 2 ≤ p) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hκ : (r : ℝ) ≤ (walshCard m : ℝ) * θ)
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r) :
    |signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace (((randomProjection d₁ d₂ V -
          ((r : ℝ) / walshCard m) • 1) *
        (bernoulliProjection e - θ • 1)) ^ (2 * p)))| ≤
      (K₀ : ℝ) ^ p * (((r : ℝ) / walshCard m) * θ) ^ p :=
  signed_trace_proposition V hV θ hp hθ hκ hr

-- Lemma 4: exact log order and effective Bernoulli width.
example {m r : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (p : ℕ) (hp : p = Nat.ceil (Real.logb 2 (3000 * r : ℝ)))
    (hr : 2 * (4 * p + 1) ^ 1000 ≤ r)
    (η θ : ℝ) (hη : 0 < η ∧ η < 1) (hθ : 0 < θ ∧ θ ≤ 1 / 2)
    (hκ : 64 * K₀ * r / η ^ 2 ≤ (walshCard m : ℝ) * θ) :
    signPairExpectation (fun d₁ d₂ ↦ bernoulliProbability θ (fun e ↦
      euclideanOperatorNorm
        (bernoulliGram θ (transformedFrame d₁ d₂ V) e - 1) > η)) ≤ 1 / 1000 :=
  bernoulli_coordinate_sampling_corollary V hV p hp hr η θ hη hθ hκ

-- Lemma 7: normalized cumulant, XOR vanishing, exact entry mean.
example {m r q : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (i j : Fin q → WalshIndex m) (hq : 1 ≤ q) :
    |jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
      (fun f d ↦ (walshCard m : ℝ) * randomProjection d.1 d.2 V (i f) (j f))| ≤
        ((2 * q : ℕ) : ℝ) ^ (12 * q) * r ∧
    ((∑ f, (i f + j f)) ≠ 0 →
      jointCumulant (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m))
        (fun f d ↦ (walshCard m : ℝ) * randomProjection d.1 d.2 V (i f) (j f)) = 0) ∧
    (∀ a b, signPairExpectation (fun d₁ d₂ ↦ randomProjection d₁ d₂ V a b) =
      if a = b then (r : ℝ) / walshCard m else 0) :=
  joint_entry_cumulant_lemma V hV i j hq

-- Lemma 8: both loop and complete equality-partition counts.
example (p s t : ℕ) (hp : 2 ≤ p) :
    (∀ Q : SelectorEqualityData p s t,
      equalityLoopOccurrences Q.1 ≤ 4 * t + 12 * s + 2) ∧
    selectorEqualityCount p s t ≤
      8 * p * 3 ^ p * (4 * p + 1) ^ (74 * (s + t)) :=
  selector_equality_graph_count p s t hp

-- Lemma 12: the exact Frobenius second moment and selected-width success.
example {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (hV : OrthonormalFrame V)
    (hk : 1 ≤ k ∧ k ≤ walshCard m) :
    uniformExpectation
      (Ω := SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
        FixedSubset (WalshIndex m) k)
      (fun sample ↦ frobeniusNormSq
        (fixedSampleGram (transformedFrame sample.1 sample.2.1 V) sample.2.2 - 1)) ≤
      (r : ℝ) * (r + 1) / k ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → 1 ≤ r → r ≤ walshCard m →
      let k₀ := Nat.min (walshCard m)
        (Nat.ceil ((200 : ℝ) * r ^ 2 / ε ^ 2))
      frameFailureProbability (k := k₀) ε V ≤ 1 / 100) :=
  small_rank_second_moment V hV hk

end Problem56.PaperV6
