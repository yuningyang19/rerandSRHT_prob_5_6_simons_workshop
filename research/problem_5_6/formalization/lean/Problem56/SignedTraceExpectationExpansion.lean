import Problem56.SignedTraceEntryCumulant
import Problem56.TraceCyclicExpansion

/-!
# Expectation expansion for the signed cyclic trace

This file commutes the two finite expectations with the literal cyclic trace
expansion.  It stops before either the selector equality-partition reindexing
or the projection-entry moment--cumulant expansion.
-/

open scoped BigOperators Matrix

namespace Problem56

set_option maxHeartbeats 8000000

noncomputable section

private theorem bernoulliExpectation_sum
    {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ]
    (θ : ℝ) (F : κ → SignLayer α → ℝ) :
    bernoulliExpectation θ (fun e ↦ ∑ k, F k e) =
      ∑ k, bernoulliExpectation θ (F k) := by
  classical
  unfold bernoulliExpectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem bernoulliExpectation_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (θ c : ℝ) (F : SignLayer α → ℝ) :
    bernoulliExpectation θ (fun e ↦ c * F e) =
      c * bernoulliExpectation θ F := by
  classical
  unfold bernoulliExpectation
  calc
    (∑ e, bernoulliWeight θ e * (c * F e)) =
        ∑ e, c * (bernoulliWeight θ e * F e) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = c * ∑ e, bernoulliWeight θ e * F e := by
      rw [Finset.mul_sum]

/-- Exact finite-expectation expansion of the centered signed trace into a
selector moment and an independent sign-pair moment for each literal cyclic
row labeling. -/
theorem signBernoulliExpectation_trace_centered_product_pow_expansion
    {m r p : ℕ}
    (V : Matrix (WalshIndex m) (Fin r) ℝ) (θ : ℝ) (hp : 1 ≤ p) :
    signBernoulliExpectation θ (fun d₁ d₂ e ↦
      Matrix.trace
        (((randomProjection d₁ d₂ V -
              ((r : ℝ) / walshCard m) •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)) *
            (bernoulliProjection e - θ •
              (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
          (2 * p))) =
      ∑ x : Fin (2 * p) → WalshIndex m,
        bernoulliExpectation θ (fun e ↦
          ∏ f : Fin (2 * p), centeredBernoulliValue θ e (x f)) *
        signPairExpectation (fun d₁ d₂ ↦
          ∏ f : Fin (2 * p),
            centeredRandomProjectionEntry V
              (x f) (x (cyclicSucc f)) (d₁, d₂)) := by
  classical
  have hlength : 2 * p - 1 + 1 = 2 * p := by omega
  let R : SignLayer (WalshIndex m) → SignLayer (WalshIndex m) →
      Matrix (WalshIndex m) (WalshIndex m) ℝ := fun d₁ d₂ ↦
    randomProjection d₁ d₂ V -
      ((r : ℝ) / walshCard m) •
        (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ)
  let S : (Fin (2 * p) → WalshIndex m) →
      SignLayer (WalshIndex m) → ℝ := fun x e ↦
    ∏ f : Fin (2 * p), centeredBernoulliValue θ e (x f)
  let T : (Fin (2 * p) → WalshIndex m) →
      SignLayer (WalshIndex m) → SignLayer (WalshIndex m) → ℝ :=
    fun x d₁ d₂ ↦
      ∏ f : Fin (2 * p),
        centeredRandomProjectionEntry V
          (x f) (x (cyclicSucc f)) (d₁, d₂)
  have htrace (d₁ d₂ e : SignLayer (WalshIndex m)) :
      Matrix.trace
          (((R d₁ d₂) *
              (bernoulliProjection e - θ •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
            (2 * p)) =
        ∑ x : Fin (2 * p) → WalshIndex m, T x d₁ d₂ * S x e := by
    have h := trace_centeredSelector_product_pow_expansion
      (R d₁ d₂) θ e (2 * p - 1)
    rw [hlength] at h
    simpa only [T, S, R, centeredRandomProjectionEntry,
      Matrix.sub_apply] using h
  change signPairExpectation (fun d₁ d₂ ↦
      bernoulliExpectation θ (fun e ↦
        Matrix.trace
          (((R d₁ d₂) *
              (bernoulliProjection e - θ •
                (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
            (2 * p)))) = _
  calc
    signPairExpectation (fun d₁ d₂ ↦
        bernoulliExpectation θ (fun e ↦
          Matrix.trace
            (((R d₁ d₂) *
                (bernoulliProjection e - θ •
                  (1 : Matrix (WalshIndex m) (WalshIndex m) ℝ))) ^
              (2 * p)))) =
        signPairExpectation (fun d₁ d₂ ↦
          bernoulliExpectation θ (fun e ↦
            ∑ x : Fin (2 * p) → WalshIndex m, T x d₁ d₂ * S x e)) := by
      congr 1
      funext d₁ d₂
      congr 1
      funext e
      exact htrace d₁ d₂ e
    _ = signPairExpectation (fun d₁ d₂ ↦
          ∑ x : Fin (2 * p) → WalshIndex m,
            T x d₁ d₂ * bernoulliExpectation θ (S x)) := by
      congr 1
      funext d₁ d₂
      rw [bernoulliExpectation_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact bernoulliExpectation_const_mul θ (T x d₁ d₂) (S x)
    _ = ∑ x : Fin (2 * p) → WalshIndex m,
          signPairExpectation (fun d₁ d₂ ↦
            T x d₁ d₂ * bernoulliExpectation θ (S x)) := by
      rw [signPairExpectation_sum]
    _ = ∑ x : Fin (2 * p) → WalshIndex m,
          bernoulliExpectation θ (S x) * signPairExpectation (T x) := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        signPairExpectation (fun d₁ d₂ ↦
            T x d₁ d₂ * bernoulliExpectation θ (S x)) =
            signPairExpectation (fun d₁ d₂ ↦
              bernoulliExpectation θ (S x) * T x d₁ d₂) := by
          congr 1
          funext d₁ d₂
          ring
        _ = bernoulliExpectation θ (S x) * signPairExpectation (T x) :=
          signPairExpectation_const_mul _ _
    _ = _ := by
      rfl

#print axioms signBernoulliExpectation_trace_centered_product_pow_expansion

end

end Problem56
