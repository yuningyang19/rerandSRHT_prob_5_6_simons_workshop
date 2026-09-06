import Problem56.GraphOperatorL2

/-!
Kernel-checked representation tests for the finite graph operator.  These are
small exact instances used to guard the scalar edge accounting, transpose norm
orientation, the one-vertex/no-edge endpoint, and a zero-dimensional domain.
They do not replace the general nondegenerate I04 induction.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace Problem56.GraphOperatorRegression

theorem graphOperator_dim_one
    {ι ε : Type*} [Fintype ι] [Fintype ε] [DecidableEq ι]
    (src dst : ε → ι) (c : ε → ℝ) (input output : ι) :
    graphOperator (fun _ : ι ↦ 1) src dst
      (fun e _ _ ↦ c e) input output = fun _ _ ↦ ∏ e, c e := by
  classical
  ext a b
  have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
  have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
  subst a
  subst b
  simp [graphOperator]

abbrev ChainVertex := Fin 3
abbrev ChainEdge := Fin 2

def chainSrc (e : ChainEdge) : ChainVertex := if e = 0 then 0 else 1

def chainDst (e : ChainEdge) : ChainVertex := if e = 0 then 1 else 2

def chainCoefficient (e : ChainEdge) : ℝ := if e = 0 then 2 else 3

theorem exact_scalar_chain :
    graphOperator (fun _ : ChainVertex ↦ 1) chainSrc chainDst
      (fun e _ _ ↦ chainCoefficient e) 0 2 = fun _ _ ↦ 6 := by
  rw [graphOperator_dim_one]
  ext a b
  norm_num [chainCoefficient, Fin.prod_univ_two]

abbrev DiamondVertex := Fin 4
abbrev DiamondEdge := Fin 4

def diamondSrc (e : DiamondEdge) : DiamondVertex :=
  if e = 0 ∨ e = 1 then 0 else if e = 2 then 1 else 2

def diamondDst (e : DiamondEdge) : DiamondVertex :=
  if e = 0 then 1 else if e = 1 then 2 else 3

theorem exact_scalar_diamond :
    graphOperator (fun _ : DiamondVertex ↦ 1) diamondSrc diamondDst
      (fun _ _ _ ↦ (2 : ℝ)) 0 3 = fun _ _ ↦ 16 := by
  rw [graphOperator_dim_one]
  ext a b
  norm_num [Fin.prod_univ_succ]

abbrev ParallelEdge := Fin 2

def parallelSrc (_ : ParallelEdge) : Bool := false

def parallelDst (_ : ParallelEdge) : Bool := true

theorem exact_scalar_parallel_edges :
    graphOperator (fun _ : Bool ↦ 1) parallelSrc parallelDst
      (fun e _ _ ↦ chainCoefficient e)
      false true = fun _ _ ↦ 6 := by
  rw [graphOperator_dim_one]
  ext a b
  norm_num [chainCoefficient, Fin.prod_univ_two]

theorem transpose_preserves_required_norm
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℝ) :
    euclideanOperatorNorm A.transpose = euclideanOperatorNorm A :=
  euclideanOperatorNorm_transpose A

theorem zero_dimensional_domain_has_zero_norm
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α (Fin 0) ℝ) : euclideanOperatorNorm A = 0 :=
  euclideanOperatorNorm_eq_zero_of_isEmpty_domain A

#print axioms graphOperator_dim_one
#print axioms exact_scalar_chain
#print axioms exact_scalar_diamond
#print axioms exact_scalar_parallel_edges
#print axioms transpose_preserves_required_norm
#print axioms zero_dimensional_domain_has_zero_norm

end Problem56.GraphOperatorRegression
