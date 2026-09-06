import Problem56.Definitions

namespace Problem56.PaperV6

/-- Width is chosen before the fixed frame, as in frozen v6 thm:main. -/
def FixedFrameOSE : Prop :=
  ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
    ∀ (m r : ℕ) (ε : ℝ),
      1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
      ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
        k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
        ∀ V : Matrix (WalshIndex m) (Fin r) ℝ,
          OrthonormalFrame V → frameFailureProbability (k := k) ε V ≤ 1 / 100

/-- One draw controls every vector of this fixed frame, with both squared edges. -/
def SquaredNormEdges {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) : Prop :=
  ∀ x : Fin r → ℝ,
    (1 - ε) * euclideanNorm (V.mulVec x) ^ 2 ≤
      euclideanNorm ((rerandomizedSRHT d₁ d₂ J).transpose.mulVec (V.mulVec x)) ^ 2 ∧
    euclideanNorm ((rerandomizedSRHT d₁ d₂ J).transpose.mulVec (V.mulVec x)) ^ 2 ≤
      (1 + ε) * euclideanNorm (V.mulVec x) ^ 2

end Problem56.PaperV6
