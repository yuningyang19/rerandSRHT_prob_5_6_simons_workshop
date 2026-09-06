import Problem56.Definitions

/-! Exact unequal-dimensional chain check for the repository graph orientation. -/

open scoped BigOperators Matrix

namespace Problem56.GraphOperatorUnequalRegression

def dim (v : Fin 3) : ℕ := if v = 1 then 2 else 1

instance : Subsingleton (Fin (dim (0 : Fin 3))) := by
  rw [show dim (0 : Fin 3) = 1 by simp [dim]]
  infer_instance

instance : Subsingleton (Fin (dim (2 : Fin 3))) := by
  rw [show dim (2 : Fin 3) = 1 by simp [dim]]
  infer_instance

def src : Bool → Fin 3
  | false => 0
  | true => 1

def dst : Bool → Fin 3
  | false => 1
  | true => 2

def edgeMatrix : ∀ e : Bool,
    Matrix (Fin (dim (src e))) (Fin (dim (dst e))) ℝ
  | false => fun _ j ↦ if j.1 = 0 then 2 else 3
  | true => fun i _ ↦ if i.1 = 0 then 5 else 7

def labelsFromMiddle (j : Fin 2) (v : Fin 3) : Fin (dim v) :=
  if h : v = 1 then
    Fin.cast (by subst v; simp [dim]) j
  else
    ⟨0, by simp [dim, h]⟩

def labelEquiv : (∀ v : Fin 3, Fin (dim v)) ≃ Fin 2 where
  toFun labels := labels 1
  invFun := labelsFromMiddle
  left_inv labels := by
    funext v
    by_cases h : v = 1
    · subst v
      apply Fin.ext
      rfl
    · apply Fin.ext
      simp only [labelsFromMiddle, dif_neg h]
      have hlt := (labels v).isLt
      have hdim : dim v = 1 := by simp [dim, h]
      omega
  right_inv j := by
    apply Fin.ext
    simp [labelsFromMiddle, dim]

theorem exact_unequal_dimensional_chain :
    graphOperator dim src dst edgeMatrix 0 2 = fun _ _ ↦ 31 := by
  classical
  ext a b
  have hinput : ∀ labels : ∀ v : Fin 3, Fin (dim v), labels 0 = a := by
    intro labels
    apply Fin.ext
    have hx := (labels 0).isLt
    have ha := a.isLt
    simp [dim] at hx ha
    omega
  have houtput : ∀ labels : ∀ v : Fin 3, Fin (dim v), labels 2 = b := by
    intro labels
    apply Fin.ext
    have hx := (labels 2).isLt
    have hb := b.isLt
    simp [dim] at hx hb
    omega
  let f : (∀ v : Fin 3, Fin (dim v)) → ℝ := fun labels ↦
    if labels 0 = a ∧ labels 2 = b then
      ∏ e : Bool, edgeMatrix e (labels (src e)) (labels (dst e))
    else 0
  let g : Fin 2 → ℝ := fun j ↦ if j = 0 then 10 else 21
  change (∑ labels, f labels) = 31
  calc
    (∑ labels, f labels) = ∑ j, g j := by
      apply Fintype.sum_equiv labelEquiv f g
      intro labels
      by_cases hj : (labels 1).val = 0
      · have heq : labelEquiv labels = (0 : Fin 2) := Fin.ext hj
        have hd0 : (labels (dst false)).val = 0 := by simpa [dst] using hj
        have hs1 : (labels (src true)).val = 0 := by simpa [src] using hj
        norm_num [f, g, src, dst, edgeMatrix, hinput, houtput, hd0, hs1, heq]
      · have hjv : (labels 1).val = 1 := by
          have hlt := (labels 1).isLt
          simp [dim] at hlt
          omega
        have hne : labelEquiv labels ≠ (0 : Fin 2) := by
          intro h
          apply hj
          exact congrArg Fin.val h
        have hd0 : (labels (dst false)).val = 1 := by simpa [dst] using hjv
        have hs1 : (labels (src true)).val = 1 := by simpa [src] using hjv
        norm_num [f, g, src, dst, edgeMatrix, hinput, houtput, hd0, hs1, hne]
    _ = 31 := by norm_num [g, Fin.sum_univ_two]

#print axioms exact_unequal_dimensional_chain

end Problem56.GraphOperatorUnequalRegression
