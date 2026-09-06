import Problem56.Definitions

/-!
Kernel-checked definitions-only lemmas for the selector quotient graph.
-/

namespace Problem56

theorem selector_quotient_parameter_bounds
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    s ≤ p - 1 ∧ s + t ≤ p := by
  have htwo : 0 < 2 * p := by omega
  haveI : Nonempty (Fin (2 * p)) := Fin.pos_iff_nonempty.mp htwo
  have huniv : (Finset.univ : Finset (Fin (2 * p))) ≠ ∅ :=
    Finset.univ_nonempty.ne_empty
  have hpartspos : 0 < Q.1.parts.card :=
    (Q.1.parts_nonempty huniv).card_pos
  have hs : s ≤ p - 1 := by
    rw [Q.2.2.1] at hpartspos
    omega
  have hoddsub : equalityOddIncidentVertices Q.1 ⊆ Q.1.parts :=
    Finset.filter_subset _ _
  have ht : t ≤ p - s := by
    have := Finset.card_le_card hoddsub
    rw [Q.2.2.2, Q.2.2.1] at this
    exact this
  constructor
  · exact hs
  · omega

theorem selector_quotient_total_excess
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (∑ B ∈ Q.1.parts, (2 * B.card - 4) = 4 * s) := by
  have hrewrite :
      (∑ B ∈ Q.1.parts, (2 * B.card - 4)) =
        2 * ∑ B ∈ Q.1.parts, (B.card - 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    have hcard := Q.2.1 B hB
    omega
  rw [hrewrite]
  have hsub :
      (∑ B ∈ Q.1.parts, (B.card - 2)) =
        (∑ B ∈ Q.1.parts, B.card) - ∑ _B ∈ Q.1.parts, 2 := by
    exact Finset.sum_tsub_distrib Q.1.parts fun B hB ↦ Q.2.1 B hB
  rw [hsub, Q.1.sum_card_parts]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  rw [Q.2.2.1]
  have hs := (selector_quotient_parameter_bounds hp Q).1
  have hsp : s ≤ p := hs.trans (Nat.sub_le p 1)
  have htwice : 2 * s ≤ 2 * p := Nat.mul_le_mul_left 2 hsp
  have hinner : 2 * p - (p - s) * 2 = 2 * s := by
    calc
      2 * p - (p - s) * 2 = 2 * p - 2 * (p - s) := by
        rw [Nat.mul_comm (p - s) 2]
      _ = 2 * p - (2 * p - 2 * s) := by
        rw [Nat.mul_sub_left_distrib]
      _ = 2 * s := Nat.sub_sub_self htwice
  calc
    2 * (2 * p - (p - s) * 2) = 2 * (2 * s) := by rw [hinner]
    _ = 4 * s := by omega

private theorem cyclicSucc_eq_add_one {q : ℕ} [NeZero q] (i : Fin q) :
    cyclicSucc i = i + 1 := by
  apply Fin.ext
  simp [cyclicSucc, Fin.add_def]

private theorem cyclicSucc_bijective {q : ℕ} (hq : 0 < q) :
    Function.Bijective (@cyclicSucc q) := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have heq : (@cyclicSucc q) = fun i : Fin q ↦ i + 1 := by
    funext i
    exact cyclicSucc_eq_add_one i
  rw [heq]
  exact (Equiv.addRight (1 : Fin q)).bijective

private theorem cycle_edge_maps_to_quotient_edge
    {q : ℕ} (hq : 2 ≤ q)
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    {i j : Fin q} (hij : (SimpleGraph.cycleGraph q).Adj i j) :
    graphAdjacent (fun e : Fin q ↦ equalityVertexAt P e)
      (fun e : Fin q ↦ equalityVertexAt P (cyclicSucc e))
      (equalityVertexAt P i) (equalityVertexAt P j) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj] at hij
  rcases hij with hij | hij
  · have hji : j + 1 = i := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hij).symm
    refine ⟨j, Or.inr ⟨rfl, ?_⟩⟩
    change equalityVertexAt P (cyclicSucc j) = equalityVertexAt P i
    rw [cyclicSucc_eq_add_one, hji]
  · have hij' : i + 1 = j := by
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hij).symm
    refine ⟨i, Or.inl ⟨rfl, ?_⟩⟩
    change equalityVertexAt P (cyclicSucc i) = equalityVertexAt P j
    rw [cyclicSucc_eq_add_one, hij']

theorem selector_quotient_graph_connected
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    GraphConnected (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) := by
  intro U V
  obtain ⟨i, hi⟩ := Q.1.nonempty_of_mem_parts U.2
  obtain ⟨j, hj⟩ := Q.1.nonempty_of_mem_parts V.2
  have hiU : equalityVertexAt Q.1 i = U := by
    apply Subtype.ext
    exact Q.1.part_eq_of_mem U.2 hi
  have hjV : equalityVertexAt Q.1 j = V := by
    apply Subtype.ext
    exact Q.1.part_eq_of_mem V.2 hj
  rw [← hiU, ← hjV]
  have hcycle : Relation.ReflTransGen (SimpleGraph.cycleGraph (2 * p)).Adj i j :=
    (SimpleGraph.reachable_iff_reflTransGen i j).mp
      (SimpleGraph.cycleGraph_preconnected i j)
  exact hcycle.lift (equalityVertexAt Q.1)
    (fun _ _ h ↦ cycle_edge_maps_to_quotient_edge (by omega) Q.1 h)

private theorem source_fiber_card
    {q : ℕ} (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : {B : Finset (Fin q) // B ∈ P.parts}) :
    ((Finset.univ : Finset (Fin q)).filter fun e ↦ equalityVertexAt P e = B).card =
      B.1.card := by
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Subtype.ext_iff]
  exact P.part_eq_iff_mem B.2

private theorem target_fiber_card
    {q : ℕ} (hq : 0 < q)
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : {B : Finset (Fin q) // B ∈ P.parts}) :
    ((Finset.univ : Finset (Fin q)).filter fun e ↦
      equalityVertexAt P (cyclicSucc e) = B).card = B.1.card := by
  classical
  let sourceFiber : Finset (Fin q) :=
    Finset.univ.filter fun e ↦ equalityVertexAt P e = B
  let targetFiber : Finset (Fin q) :=
    Finset.univ.filter fun e ↦ equalityVertexAt P (cyclicSucc e) = B
  have hbij := cyclicSucc_bijective hq
  have hcard : targetFiber.card = sourceFiber.card := by
    apply Finset.card_bij (fun e _ ↦ cyclicSucc e)
    · intro e he
      simpa [sourceFiber, targetFiber] using he
    · intro a ha b hb hab
      exact hbij.1 hab
    · intro y hy
      obtain ⟨x, rfl⟩ := hbij.2 y
      refine ⟨x, ?_, rfl⟩
      simpa [sourceFiber, targetFiber] using hy
  rw [show ((Finset.univ : Finset (Fin q)).filter fun e ↦
      equalityVertexAt P (cyclicSucc e) = B) = targetFiber by rfl,
    hcard, show sourceFiber = (Finset.univ : Finset (Fin q)).filter
      (fun e ↦ equalityVertexAt P e = B) by rfl,
    source_fiber_card]

theorem selector_quotient_degree
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1) :
    graphDegree (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 e)
      (fun e : Fin (2 * p) ↦ equalityVertexAt Q.1 (cyclicSucc e)) B =
        2 * B.1.card := by
  rw [graphDegree, source_fiber_card, target_fiber_card (by omega)]
  omega

#print axioms selector_quotient_parameter_bounds
#print axioms selector_quotient_total_excess
#print axioms selector_quotient_graph_connected
#print axioms selector_quotient_degree

end Problem56
