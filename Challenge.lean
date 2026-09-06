import Mathlib

/-!
# Rerandomized SRHT subspace embeddings

For n = 2^m, 1 ≤ r ≤ n and 0 < ε < 1, an explicit universal constant gives
one deterministic width r ≤ k ≤ min(n, ⌈Cr/ε²⌉), chosen before the frame V.
For each fixed orthonormal V, two independent uniform sign layers and an
independent uniform k-subset preserve its subspace with probability at least
99/100. The first declaration bounds the supremum of spectral failure
probabilities. The second gives both squared-norm bounds for all vectors of
the same fixed frame on one event. One random draw need not work for all V.

These are the existing certified declarations for frozen v6 Theorem 1 and its
squared-norm interpretation (paper f279b6fac180125dce81a82d824da971bb7ae715).
All definitions below are transparent copies of their certified counterparts.
Only the two theorem bodies are deliberate challenge holes. All supporting
v6 results remain in the unchanged Solution proof closure.
-/

open scoped BigOperators Matrix

namespace Problem56

/-- The binary index set of a Walsh transform of size 2^m. -/
abbrev WalshIndex (m : ℕ) := Fin m → ZMod 2

/-- One Boolean sign per coordinate; uniform sampling gives independent signs. -/
abbrev SignLayer (α : Type*) := α → Bool

/-- The ambient dimension, equal to 2^m. -/
def walshCard (m : ℕ) : ℕ := Fintype.card (WalshIndex m)

/-- The binary dot product. -/
def walshDot {m : ℕ} (a b : WalshIndex m) : ZMod 2 :=
  ∑ i, a i * b i

/-- The real Walsh character associated with the binary dot product. -/
def walshCharacter {m : ℕ} (a b : WalshIndex m) : ℝ :=
  if walshDot a b = 0 then 1 else -1

/-- The orthogonally normalized real Walsh matrix. -/
noncomputable def normalizedWalsh (m : ℕ) :
    Matrix (WalshIndex m) (WalshIndex m) ℝ :=
  fun a b ↦ walshCharacter a b / Real.sqrt (walshCard m : ℝ)

/-- A Boolean encoded as a Rademacher sign. -/
def signValue {α : Type*} (d : SignLayer α) (i : α) : ℝ :=
  if d i then -1 else 1

/-- The diagonal matrix of one sign layer. -/
def signDiagonal {α : Type*} [DecidableEq α] (d : SignLayer α) : Matrix α α ℝ :=
  Matrix.diagonal (signValue d)

/-- The finite type of k-element coordinate subsets. -/
abbrev FixedSubset (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :=
  {J : Finset α // J.card = k}

/-- The matrix selecting the coordinates of a fixed subset. -/
def sampleMatrix {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (J : FixedSubset α k) : Matrix α {i // i ∈ J.1} ℝ :=
  fun i j ↦ if i = j.1 then 1 else 0

/-- The scaled two-Walsh, two-sign transform followed by coordinate selection. -/
noncomputable def rerandomizedSRHT {m k : ℕ}
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    Matrix (WalshIndex m) {i // i ∈ J.1} ℝ :=
  Real.sqrt ((walshCard m : ℝ) / (k : ℝ)) •
    (signDiagonal d₁ * normalizedWalsh m * signDiagonal d₂ *
      normalizedWalsh m * sampleMatrix J)

/-- A real matrix whose columns are an orthonormal frame. -/
def OrthonormalFrame {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}
    (V : Matrix α (Fin r) ℝ) : Prop :=
  V.transpose * V = 1

/-- The sketch Gram matrix compressed to the target frame. -/
noncomputable def compressedGram {m r k : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) :
    Matrix (Fin r) (Fin r) ℝ :=
  let Ω := rerandomizedSRHT d₁ d₂ J
  V.transpose * Ω * Ω.transpose * V

/-- The ordinary Euclidean norm on a finite real coordinate space. -/
noncomputable def euclideanNorm {α : Type*} [Fintype α] (x : α → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- The induced Euclidean operator norm, expressed as a supremum on the unit sphere. -/
noncomputable def euclideanOperatorNorm {α β : Type*}
    [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  sSup {z : ℝ | ∃ x : β → ℝ, euclideanNorm x = 1 ∧
    z = euclideanNorm (A.mulVec x)}

/-- Uniform finite probability: event cardinality divided by sample-space cardinality. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The spectral-failure probability for a fixed frame; product sampling makes the two sign layers and the fixed-size subset independent. -/
noncomputable def frameFailureProbability {m r k : ℕ}
    (ε : ℝ) (V : Matrix (WalshIndex m) (Fin r) ℝ) : ℝ :=
  uniformProbability (Ω := SignLayer (WalshIndex m) ×
      SignLayer (WalshIndex m) × FixedSubset (WalshIndex m) k)
    (fun ω ↦ euclideanOperatorNorm
      (compressedGram V ω.1 ω.2.1 ω.2.2 - 1) > ε)

/-- The supremum over deterministic orthonormal frames, outside the probability. -/
noncomputable def spectralFailureSup (m r k : ℕ) (ε : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ V : Matrix (WalshIndex m) (Fin r) ℝ,
    OrthonormalFrame V ∧ z = frameFailureProbability (k := k) ε V}

/-- An explicit proof constant, independent of dimensions and accuracy. -/
def K₂ : ℕ := 4 ^ 24

/-- An explicit proof constant, independent of dimensions and accuracy. -/
def K₀ : ℕ := 576 * K₂

/-- The explicit rank cutoff used in the certified proof. -/
def R₀ : ℕ := 2 ^ 20000

/-- The concrete universal constant furnished by the certified proof; no sharp numerical constant is claimed. -/
def explicitUniversalConstant : ℕ := 200 * R₀ + 8196 * K₀

/-- Universal O(r/ε²) width and at most 1/100 spectral failure, uniformly over fixed frames. -/
theorem main_universal_ose :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m)
            (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          spectralFailureSup m r k ε ≤ 1 / 100 := by
  sorry

namespace PaperV6

-- The source definitions start in a separate module, whose auxiliary-lemma
-- cache is empty. Reproduce only that cache boundary; no declaration is changed.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-- The certified fixed-frame form, also preserving its generated numeral auxiliary. -/
def FixedFrameOSE : Prop :=
  ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
    ∀ (m r : ℕ) (ε : ℝ),
      1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
      ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
        k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
        ∀ V : Matrix (WalshIndex m) (Fin r) ℝ,
          OrthonormalFrame V → frameFailureProbability (k := k) ε V ≤ 1 / 100

/-- Both squared-norm inequalities for every vector of a fixed frame on one draw. -/
def SquaredNormEdges {m r k : ℕ} (ε : ℝ)
    (V : Matrix (WalshIndex m) (Fin r) ℝ)
    (d₁ d₂ : SignLayer (WalshIndex m)) (J : FixedSubset (WalshIndex m) k) : Prop :=
  ∀ x : Fin r → ℝ,
    (1 - ε) * euclideanNorm (V.mulVec x) ^ 2 ≤
      euclideanNorm ((rerandomizedSRHT d₁ d₂ J).transpose.mulVec (V.mulVec x)) ^ 2 ∧
    euclideanNorm ((rerandomizedSRHT d₁ d₂ J).transpose.mulVec (V.mulVec x)) ^ 2 ≤
      (1 + ε) * euclideanNorm (V.mulVec x) ^ 2

/-- At least 99/100 success for both squared-norm inequalities, with the width chosen before the frame. -/
theorem fixed_frame_squared_norm_success :
    ∃ C : ℕ, C = explicitUniversalConstant ∧ 1 ≤ C ∧
      ∀ (m r : ℕ) (ε : ℝ),
        1 ≤ r → r ≤ walshCard m → 0 < ε → ε < 1 →
        ∃ k : ℕ, r ≤ k ∧ k ≤ walshCard m ∧
          k ≤ Nat.min (walshCard m) (Nat.ceil ((C : ℝ) * r / ε ^ 2)) ∧
          ∀ V : Matrix (WalshIndex m) (Fin r) ℝ, OrthonormalFrame V →
            99 / 100 ≤ uniformProbability
              (fun ω : SignLayer (WalshIndex m) × SignLayer (WalshIndex m) ×
                  FixedSubset (WalshIndex m) k ↦
                SquaredNormEdges ε V ω.1 ω.2.1 ω.2.2) := by
  sorry

end PaperV6
end Problem56
