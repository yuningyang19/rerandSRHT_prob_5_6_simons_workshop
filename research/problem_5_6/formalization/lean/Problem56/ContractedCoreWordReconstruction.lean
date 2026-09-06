import Problem56.Definitions

/-!
# Reconstruction of a finite partition from a started cyclic port dynamics

The contracted-core encoder ultimately transports two fixed-point-free
involutions to one common port graph: edge reversal and the local Euler
transition.  Their composite advances the original cyclic occurrence word by
one step.  This file isolates the generic uniqueness statement needed at the
end of that construction.  It is independent of the particular contracted
core and introduces no counting or decoder assumption.
-/

namespace Problem56

/-- Two finite partitions are equal when their occurrence ports start at the
same point, evolve by the same cyclic dynamics, and record block equality by
the same port-vertex map. -/
theorem finpartition_eq_of_started_cyclic_dynamics
    {n : ℕ}
    (P Q : Finpartition (Finset.univ : Finset (Fin (n + 1))))
    {Port Vertex : Type*}
    (tailP tailQ : Fin (n + 1) → Port)
    (portVertex : Port → Vertex) (step : Port → Port)
    (hstart : tailP 0 = tailQ 0)
    (hnextP : ∀ i, tailP (cyclicSucc i) = step (tailP i))
    (hnextQ : ∀ i, tailQ (cyclicSucc i) = step (tailQ i))
    (hclassP : ∀ i j, P.part i = P.part j ↔
      portVertex (tailP i) = portVertex (tailP j))
    (hclassQ : ∀ i j, Q.part i = Q.part j ↔
      portVertex (tailQ i) = portVertex (tailQ j)) :
    P = Q := by
  have htail : ∀ i, tailP i = tailQ i := by
    intro i
    induction i using Fin.induction with
    | zero => exact hstart
    | succ i ih =>
        have hcyclic : cyclicSucc i.castSucc = i.succ := by
          apply Fin.ext
          simp only [cyclicSucc, Fin.val_castSucc, Fin.val_succ]
          rw [Nat.mod_eq_of_lt]
          omega
        rw [← hcyclic, hnextP, hnextQ, ih]
  have hpart : ∀ i, P.part i = Q.part i := by
    intro i
    ext j
    rw [P.mem_part_iff_part_eq_part (Finset.mem_univ j)
      (Finset.mem_univ i),
      Q.mem_part_iff_part_eq_part (Finset.mem_univ j)
        (Finset.mem_univ i)]
    rw [hclassP, hclassQ, htail j, htail i]
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB hi, hpart i]
    exact Q.part_mem.mpr (Finset.mem_univ i)
  · intro hB
    obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB hi, ← hpart i]
    exact P.part_mem.mpr (Finset.mem_univ i)

/-- Positive-cardinality wrapper with the cyclic word length left abstract.
This is the convenient form for the `2p`-occurrence equality graph. -/
theorem finpartition_eq_of_started_cyclic_dynamics_of_pos
    {q : ℕ} (hq : 0 < q)
    (P Q : Finpartition (Finset.univ : Finset (Fin q)))
    {Port Vertex : Type*}
    (tailP tailQ : Fin q → Port)
    (portVertex : Port → Vertex) (step : Port → Port)
    (hstart : tailP ⟨0, hq⟩ = tailQ ⟨0, hq⟩)
    (hnextP : ∀ i, tailP (cyclicSucc i) = step (tailP i))
    (hnextQ : ∀ i, tailQ (cyclicSucc i) = step (tailQ i))
    (hclassP : ∀ i j, P.part i = P.part j ↔
      portVertex (tailP i) = portVertex (tailP j))
    (hclassQ : ∀ i j, Q.part i = Q.part j ↔
      portVertex (tailQ i) = portVertex (tailQ j)) :
    P = Q := by
  cases q with
  | zero => omega
  | succ n =>
      exact finpartition_eq_of_started_cyclic_dynamics P Q tailP tailQ
        portVertex step hstart hnextP hnextQ hclassP hclassQ

#print axioms finpartition_eq_of_started_cyclic_dynamics
#print axioms finpartition_eq_of_started_cyclic_dynamics_of_pos

end Problem56
