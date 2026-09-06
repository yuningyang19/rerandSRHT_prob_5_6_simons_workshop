import Problem56.Definitions

/-!
Finite-field kernel counting for the corrected I22 interface.  The dependent
Walsh labels are uncurryed into one kernel vector for each Walsh bit.
-/

namespace Problem56

def xorLabelKernelEquiv (m v h : ℕ)
    (A : Matrix (Fin h) (Fin v) (ZMod 2)) :
    {x : Fin v → WalshIndex m //
      ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} ≃
      (Fin m → LinearMap.ker A.mulVecLin) where
  toFun x bit := ⟨fun j ↦ x.1 j bit, by simpa using x.2 bit⟩
  invFun y := ⟨fun j bit ↦ (y bit).1 j, fun bit ↦ by
    change A.mulVecLin (y bit).1 = 0
    exact (y bit).2⟩
  left_inv x := by
    apply Subtype.ext
    funext j bit
    rfl
  right_inv y := by
    funext bit
    apply Subtype.ext
    funext j
    rfl

theorem xor_kernel_solution_count
    (m v h : ℕ) (A : Matrix (Fin h) (Fin v) (ZMod 2))
    (hrank : Matrix.rank A = h) :
    Fintype.card {x : Fin v → WalshIndex m //
      ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} =
      (2 ^ m) ^ (v - h) := by
  letI : Fintype (LinearMap.ker A.mulVecLin) := Fintype.ofFinite _
  have hrange : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = h := by
    simpa only [Matrix.rank] using hrank
  have hnull := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdomain : Module.finrank (ZMod 2) (Fin v → ZMod 2) = v := by
    simpa using Module.finrank_fintype_fun_eq_card (R := ZMod 2) (M := ZMod 2)
      (K := ZMod 2) (V := Fin v → ZMod 2)
  have hker : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = v - h := by
    rw [hrange, hdomain] at hnull
    omega
  calc
    Fintype.card {x : Fin v → WalshIndex m //
        ∀ bit, A.mulVec (fun j ↦ x j bit) = 0} =
        Fintype.card (Fin m → LinearMap.ker A.mulVecLin) :=
      Fintype.card_congr (xorLabelKernelEquiv m v h A)
    _ = Fintype.card (LinearMap.ker A.mulVecLin) ^ m := by simp
    _ = (2 ^ (v - h)) ^ m := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2)
        (V := LinearMap.ker A.mulVecLin), hker]
      norm_num
    _ = (2 ^ m) ^ (v - h) := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]

#print axioms xor_kernel_solution_count

end Problem56
