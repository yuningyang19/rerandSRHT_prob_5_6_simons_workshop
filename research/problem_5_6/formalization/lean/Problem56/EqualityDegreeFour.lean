import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Problem56.SelectorQuotient
import Problem56.EqualityBudget

/-!
Degree-four classification for the cyclic selector quotient multigraph.

The indexed cyclic edges are never collapsed: `equalityEdgeMultiplicity`
retains parallel edges, and a loop contributes twice to multigraph degree.
-/

open scoped BigOperators

namespace Problem56

private lemma equalityEdgeMultiplicity_symm {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B C : Finset (Fin q)) :
    equalityEdgeMultiplicity P B C = equalityEdgeMultiplicity P C B := by
  unfold equalityEdgeMultiplicity
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

private def equalitySimpleGraph {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    SimpleGraph (EqualityVertex P) where
  Adj B C := B ≠ C ∧ 0 < equalityEdgeMultiplicity P B.1 C.1
  symm.symm B C h :=
    ⟨h.1.symm, by rw [equalityEdgeMultiplicity_symm]; exact h.2⟩

private noncomputable instance equalitySimpleGraphLocallyFinite {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    (equalitySimpleGraph P).LocallyFinite :=
  fun _ ↦ Fintype.ofFinite _

@[simp] private lemma equalitySimpleGraph_adj {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B C : EqualityVertex P) :
    (equalitySimpleGraph P).Adj B C ↔
      B ≠ C ∧ 0 < equalityEdgeMultiplicity P B.1 C.1 := Iff.rfl

private noncomputable def equalityNeighbors {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : EqualityVertex P) :
    Finset (EqualityVertex P) := by
  classical
  exact Finset.univ.filter fun C ↦ (equalitySimpleGraph P).Adj B C

@[simp] private lemma mem_equalityNeighbors {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B C : EqualityVertex P) :
    C ∈ equalityNeighbors P B ↔ (equalitySimpleGraph P).Adj B C := by
  classical
  simp [equalityNeighbors]

private lemma equalityEdgeMultiplicity_eq_vertex_filter {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B C : EqualityVertex P) :
    equalityEdgeMultiplicity P B.1 C.1 =
      ((Finset.univ : Finset (Fin q)).filter fun e ↦
        (equalityVertexAt P e = B ∧ equalityVertexAt P (cyclicSucc e) = C) ∨
        (equalityVertexAt P e = C ∧ equalityVertexAt P (cyclicSucc e) = B)).card := by
  unfold equalityEdgeMultiplicity
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [equalityVertexAt, Subtype.ext_iff]

private lemma equalityLoopsAt_eq_vertex_filter {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) :
    equalityLoopsAt P B.1 =
      ((Finset.univ : Finset (Fin q)).filter fun e ↦
        equalityVertexAt P e = B ∧
          equalityVertexAt P (cyclicSucc e) = B).card := by
  unfold equalityLoopsAt
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [equalityVertexAt, Subtype.ext_iff]

private lemma card_filter_eq_sum_indicator {α : Type*} [DecidableEq α]
    (s : Finset α) (R : α → Prop) [DecidablePred R] :
    (s.filter R).card = ∑ x ∈ s, if R x then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp

private lemma equality_incident_union_count {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) :
    (∑ C : EqualityVertex P, equalityEdgeMultiplicity P B.1 C.1) =
      ((Finset.univ : Finset (Fin q)).filter fun e ↦
        equalityVertexAt P e = B ∨
          equalityVertexAt P (cyclicSucc e) = B).card := by
  classical
  simp_rw [equalityEdgeMultiplicity_eq_vertex_filter]
  simp_rw [card_filter_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  let U := equalityVertexAt P e
  let V := equalityVertexAt P (cyclicSucc e)
  change (∑ C : EqualityVertex P,
      if (U = B ∧ V = C) ∨ (U = C ∧ V = B) then 1 else 0) =
    if U = B ∨ V = B then 1 else 0
  by_cases hU : U = B
  · have hterm : ∀ C : EqualityVertex P,
        ((U = B ∧ V = C) ∨ (U = C ∧ V = B)) ↔ V = C := by
      intro C
      constructor
      · rintro (⟨_, hVC⟩ | ⟨hUC, hVB⟩)
        · exact hVC
        · rw [hU] at hUC
          exact hVB.trans hUC
      · intro hVC
        exact Or.inl ⟨hU, hVC⟩
    simp only [hterm]
    rw [Fintype.sum_ite_eq]
    simp [hU]
  · by_cases hV : V = B
    · have hterm : ∀ C : EqualityVertex P,
          ((U = B ∧ V = C) ∨ (U = C ∧ V = B)) ↔ U = C := by
        intro C
        constructor
        · rintro (⟨hUB, _⟩ | ⟨hUC, _⟩)
          · exact (hU hUB).elim
          · exact hUC
        · intro hUC
          exact Or.inr ⟨hUC, hV⟩
      simp only [hterm]
      rw [Fintype.sum_ite_eq]
      simp [hV]
    · simp [hU, hV]

private lemma equality_graphDegree_decomposition {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1) :
    2 * B.1.card = equalityLoopsAt Q.1 B.1 +
      ∑ C : EqualityVertex Q.1,
        equalityEdgeMultiplicity Q.1 B.1 C.1 := by
  classical
  have hdegree := selector_quotient_degree hp Q B
  rw [graphDegree] at hdegree
  rw [← hdegree, equality_incident_union_count,
    equalityLoopsAt_eq_vertex_filter]
  let S := (Finset.univ : Finset (Fin (2 * p))).filter fun e ↦
    equalityVertexAt Q.1 e = B
  let T := (Finset.univ : Finset (Fin (2 * p))).filter fun e ↦
    equalityVertexAt Q.1 (cyclicSucc e) = B
  have hinter : S ∩ T =
      (Finset.univ : Finset (Fin (2 * p))).filter (fun e ↦
        equalityVertexAt Q.1 e = B ∧
          equalityVertexAt Q.1 (cyclicSucc e) = B) := by
    ext e
    simp [S, T]
  have hunion : S ∪ T =
      (Finset.univ : Finset (Fin (2 * p))).filter (fun e ↦
        equalityVertexAt Q.1 e = B ∨
          equalityVertexAt Q.1 (cyclicSucc e) = B) := by
    ext e
    simp [S, T]
  rw [← hinter, ← hunion]
  have hcard := Finset.card_union_add_card_inter S T
  change S.card + T.card = (S ∩ T).card + (S ∪ T).card
  omega

private lemma equalityEdgeMultiplicity_self {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : Finset (Fin q)) :
    equalityEdgeMultiplicity P B B = equalityLoopsAt P B := by
  unfold equalityEdgeMultiplicity equalityLoopsAt
  congr 1
  ext e
  simp

private lemma graphAdjacent_to_equalitySimpleGraph {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    {B C : EqualityVertex P}
    (h : graphAdjacent (fun e : Fin q ↦ equalityVertexAt P e)
      (fun e : Fin q ↦ equalityVertexAt P (cyclicSucc e)) B C) :
    Relation.ReflTransGen (equalitySimpleGraph P).Adj B C := by
  classical
  by_cases hBC : B = C
  · subst C
    rfl
  · apply Relation.ReflTransGen.single
    refine ⟨hBC, ?_⟩
    rw [equalityEdgeMultiplicity_eq_vertex_filter]
    apply Finset.card_pos.mpr
    rcases h with ⟨e, h | h⟩
    · exact ⟨e, by simp [h.1, h.2]⟩
    · exact ⟨e, by simp [h.1, h.2]⟩

private lemma equalitySimpleGraph_preconnected {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (equalitySimpleGraph Q.1).Preconnected := by
  intro B C
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hconn := selector_quotient_graph_connected hp Q B C
  exact Relation.ReflTransGen.lift' id
    (fun _ _ h ↦ graphAdjacent_to_equalitySimpleGraph Q.1 h) B C hconn

private lemma nonexceptional_card_and_even_multiplicity {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (B : Finset (Fin (2 * p)))
    (hB : B ∈ Q.1.parts) (hBne : B ∉ equalityExceptionalVertices Q.1) :
    B.card = 2 ∧
      ∀ C ∈ Q.1.parts, C ≠ B → Even (equalityEdgeMultiplicity Q.1 B C) := by
  classical
  have hBnotOdd : B ∉ equalityOddIncidentVertices Q.1 := by
    intro h
    apply hBne
    exact Finset.mem_union_left _ h
  have hBnotLarge : B ∉ Q.1.parts.filter (fun A ↦ 2 < A.card) := by
    intro h
    apply hBne
    exact Finset.mem_union_right _ h
  constructor
  · have hmin := Q.2.1 B hB
    simp only [Finset.mem_filter, hB, true_and] at hBnotLarge
    omega
  · intro C hC hCB
    rw [← Nat.not_odd_iff_even]
    intro hodd
    apply hBnotOdd
    exact Finset.mem_filter.mpr ⟨hB, C, hC, hCB.symm, hodd⟩

private lemma nonexceptional_vertex_type_nontrivial {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1)
    (hBne : B.1 ∉ equalityExceptionalVertices Q.1) :
    2 ≤ Q.1.parts.card := by
  classical
  have hBcard := (nonexceptional_card_and_even_multiplicity Q B.1 B.2 hBne).1
  have hpos : 0 < Q.1.parts.card := Finset.card_pos.mpr ⟨B.1, B.2⟩
  by_contra hnot
  have hone : Q.1.parts.card = 1 := by omega
  obtain ⟨A, hparts⟩ := Finset.card_eq_one.mp hone
  have hAB : A = B.1 := by
    have hmem : B.1 ∈ ({A} : Finset (Finset (Fin (2 * p)))) := by
      rw [← hparts]
      exact B.2
    exact (Finset.mem_singleton.mp hmem).symm
  subst A
  have hsum := Q.1.sum_card_parts
  rw [hparts] at hsum
  simp only [Finset.sum_singleton, Finset.card_univ, Fintype.card_fin] at hsum
  omega

private lemma equality_neighbor_sum_decomposition {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1) :
    2 * B.1.card = 2 * equalityLoopsAt Q.1 B.1 +
      ∑ C ∈ equalityNeighbors Q.1 B,
        equalityEdgeMultiplicity Q.1 B.1 C.1 := by
  classical
  have hdegree := equality_graphDegree_decomposition hp Q B
  have hself := equalityEdgeMultiplicity_self Q.1 B.1
  let G := equalitySimpleGraph Q.1
  let f : EqualityVertex Q.1 → ℕ := fun C ↦
    equalityEdgeMultiplicity Q.1 B.1 C.1
  have hsubset : equalityNeighbors Q.1 B ⊆
      (Finset.univ : Finset (EqualityVertex Q.1)).erase B := by
    intro C hC
    have hadj : G.Adj B C := by simpa only [G, mem_equalityNeighbors] using hC
    exact Finset.mem_erase.mpr ⟨hadj.ne.symm, Finset.mem_univ C⟩
  have hsum :
      (∑ C ∈ (Finset.univ : Finset (EqualityVertex Q.1)).erase B, f C) =
        ∑ C ∈ equalityNeighbors Q.1 B, f C := by
    symm
    apply Finset.sum_subset hsubset
    intro C hCuniv hCnot
    have hnotadj : ¬G.Adj B C := by
      simpa only [G, mem_equalityNeighbors] using hCnot
    have hCB : C ≠ B := (Finset.mem_erase.mp hCuniv).1
    have hBC : B ≠ C := Ne.symm hCB
    change equalityEdgeMultiplicity Q.1 B.1 C.1 = 0
    change ¬(B ≠ C ∧ 0 < equalityEdgeMultiplicity Q.1 B.1 C.1) at hnotadj
    have hnotpos : ¬0 < equalityEdgeMultiplicity Q.1 B.1 C.1 :=
      fun hpos ↦ hnotadj ⟨hBC, hpos⟩
    omega
  have hsplit := Finset.sum_erase_add (s :=
    (Finset.univ : Finset (EqualityVertex Q.1))) (f := f) (Finset.mem_univ B)
  have hsplit' : (∑ C : EqualityVertex Q.1, f C) =
      f B + ∑ C ∈ (Finset.univ : Finset (EqualityVertex Q.1)).erase B, f C := by
    rw [← hsplit]
    omega
  change 2 * B.1.card = equalityLoopsAt Q.1 B.1 + ∑ C, f C at hdegree
  rw [hsplit', hsum, show f B = equalityLoopsAt Q.1 B.1 by exact hself] at hdegree
  simpa only [two_mul, add_assoc, f] using hdegree

private lemma equality_neighbor_nonempty_of_nonexceptional {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1)
    (hBne : B.1 ∉ equalityExceptionalVertices Q.1) :
    (equalityNeighbors Q.1 B).Nonempty := by
  classical
  have hcard := nonexceptional_vertex_type_nontrivial hp Q B hBne
  have htypecard : 2 ≤ Fintype.card (EqualityVertex Q.1) := by
    rw [Fintype.card_subtype]
    simpa using hcard
  letI : Nontrivial (EqualityVertex Q.1) :=
    Fintype.one_lt_card_iff_nontrivial.mp htypecard
  by_contra hempty
  have hnone : ∀ C : EqualityVertex Q.1,
      ¬(equalitySimpleGraph Q.1).Adj B C := by
    intro C hBC
    apply hempty
    exact ⟨C, mem_equalityNeighbors Q.1 B C |>.mpr hBC⟩
  exact (equalitySimpleGraph_preconnected hp Q).not_isIsolated B hnone

private lemma equality_multiplicity_eq_zero_of_not_neighbor {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (B C : EqualityVertex Q.1)
    (hBC : B ≠ C) (hC : C ∉ equalityNeighbors Q.1 B) :
    equalityEdgeMultiplicity Q.1 B.1 C.1 = 0 := by
  have hnotadj : ¬(equalitySimpleGraph Q.1).Adj B C := by
    exact fun hadj ↦ hC (mem_equalityNeighbors Q.1 B C |>.mpr hadj)
  rw [equalitySimpleGraph_adj] at hnotadj
  have hnotpos : ¬0 < equalityEdgeMultiplicity Q.1 B.1 C.1 :=
    fun hpos ↦ hnotadj ⟨hBC, hpos⟩
  omega

private lemma nonexceptional_neighbor_multiplicity_ge_two {p s t : ℕ}
    (Q : SelectorEqualityData p s t) (B C : EqualityVertex Q.1)
    (hBne : B.1 ∉ equalityExceptionalVertices Q.1)
    (hC : C ∈ equalityNeighbors Q.1 B) :
    2 ≤ equalityEdgeMultiplicity Q.1 B.1 C.1 := by
  have hadj := mem_equalityNeighbors Q.1 B C |>.mp hC
  have heven :=
    (nonexceptional_card_and_even_multiplicity Q B.1 B.2 hBne).2
      C.1 C.2 (fun h ↦ hadj.1 (Subtype.ext h.symm))
  rcases heven with ⟨k, hk⟩
  have hpos := hadj.2
  rw [hk] at hpos ⊢
  omega

private lemma equalityNeighbors_card_eq_degree {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : EqualityVertex P) :
    (equalityNeighbors P B).card = (equalitySimpleGraph P).degree B := by
  classical
  rw [← (equalitySimpleGraph P).card_neighborFinset_eq_degree]
  congr 1
  ext C
  simp only [mem_equalityNeighbors, SimpleGraph.mem_neighborFinset]

private lemma equalityNeighbors_eq_pair_of_internal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityInternal P B.1) :
    ∃ C D : EqualityVertex P, C ≠ D ∧
      equalityNeighbors P B = {C, D} := by
  classical
  rcases hB with ⟨_, C, hC, D, hD, hCD, hCB, hDB,
    hmultC, hmultD, hother⟩
  let c : EqualityVertex P := ⟨C, hC⟩
  let d : EqualityVertex P := ⟨D, hD⟩
  have hcd : c ≠ d := fun h ↦ hCD (Subtype.ext_iff.mp h)
  refine ⟨c, d, hcd, ?_⟩
  ext A
  constructor
  · intro hA
    have hadj := mem_equalityNeighbors P B A |>.mp hA
    by_cases hAc : A = c
    · simp [hAc]
    by_cases hAd : A = d
    · simp [hAd]
    exfalso
    have hAB : A.1 ≠ B.1 := fun h ↦ hadj.1 (Subtype.ext h.symm)
    have hAC : A.1 ≠ C := fun h ↦ hAc (Subtype.ext h)
    have hAD : A.1 ≠ D := fun h ↦ hAd (Subtype.ext h)
    have hz := hother A.1 A.2 hAB hAC hAD
    have hpos := hadj.2
    rw [hz] at hpos
    omega
  · intro hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · apply mem_equalityNeighbors P B c |>.mpr
      exact ⟨fun h ↦ hCB (Subtype.ext_iff.mp h).symm, by
        simpa only [c] using (show 0 < equalityEdgeMultiplicity P B.1 C by omega)⟩
    · apply mem_equalityNeighbors P B d |>.mpr
      exact ⟨fun h ↦ hDB (Subtype.ext_iff.mp h).symm, by
        simpa only [d] using (show 0 < equalityEdgeMultiplicity P B.1 D by omega)⟩

private lemma equalityNeighbors_eq_singleton_of_loop_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityLoopTerminal P B.1) :
    ∃ C : EqualityVertex P, equalityNeighbors P B = {C} := by
  classical
  rcases hB with ⟨_, C, hC, hCB, hmult, hother⟩
  let c : EqualityVertex P := ⟨C, hC⟩
  refine ⟨c, ?_⟩
  ext A
  constructor
  · intro hA
    have hadj := mem_equalityNeighbors P B A |>.mp hA
    by_cases hAc : A = c
    · simp [hAc]
    exfalso
    have hAB : A.1 ≠ B.1 := fun h ↦ hadj.1 (Subtype.ext h.symm)
    have hAC : A.1 ≠ C := fun h ↦ hAc (Subtype.ext h)
    have hz := hother A.1 A.2 hAB hAC
    have hpos := hadj.2
    rw [hz] at hpos
    omega
  · intro hA
    have hAc : A = c := Finset.mem_singleton.mp hA
    subst A
    apply mem_equalityNeighbors P B c |>.mpr
    exact ⟨fun h ↦ hCB (Subtype.ext_iff.mp h).symm, by
      simpa only [c] using (show 0 < equalityEdgeMultiplicity P B.1 C by omega)⟩

private lemma equalityNeighbors_eq_singleton_of_four_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityFourEdgeTerminal P B.1) :
    ∃ C : EqualityVertex P, equalityNeighbors P B = {C} := by
  classical
  rcases hB with ⟨_, C, hC, hCB, hmult, hother⟩
  let c : EqualityVertex P := ⟨C, hC⟩
  refine ⟨c, ?_⟩
  ext A
  constructor
  · intro hA
    have hadj := mem_equalityNeighbors P B A |>.mp hA
    by_cases hAc : A = c
    · simp [hAc]
    exfalso
    have hAB : A.1 ≠ B.1 := fun h ↦ hadj.1 (Subtype.ext h.symm)
    have hAC : A.1 ≠ C := fun h ↦ hAc (Subtype.ext h)
    have hz := hother A.1 A.2 hAB hAC
    have hpos := hadj.2
    rw [hz] at hpos
    omega
  · intro hA
    have hAc : A = c := Finset.mem_singleton.mp hA
    subst A
    apply mem_equalityNeighbors P B c |>.mpr
    exact ⟨fun h ↦ hCB (Subtype.ext_iff.mp h).symm, by
      simpa only [c] using (show 0 < equalityEdgeMultiplicity P B.1 C by omega)⟩

private lemma equalitySimpleGraph_degree_eq_two_of_internal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityInternal P B.1) :
    (equalitySimpleGraph P).degree B = 2 := by
  obtain ⟨C, D, hCD, hN⟩ := equalityNeighbors_eq_pair_of_internal P B hB
  rw [← equalityNeighbors_card_eq_degree, hN]
  simp [hCD]

private lemma equalitySimpleGraph_degree_eq_one_of_loop_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityLoopTerminal P B.1) :
    (equalitySimpleGraph P).degree B = 1 := by
  obtain ⟨C, hN⟩ := equalityNeighbors_eq_singleton_of_loop_terminal P B hB
  rw [← equalityNeighbors_card_eq_degree, hN]
  simp

private lemma equalitySimpleGraph_degree_eq_one_of_four_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityFourEdgeTerminal P B.1) :
    (equalitySimpleGraph P).degree B = 1 := by
  obtain ⟨C, hN⟩ := equalityNeighbors_eq_singleton_of_four_terminal P B hB
  rw [← equalityNeighbors_card_eq_degree, hN]
  simp

private noncomputable def finiteSimpleDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact ((Finset.univ : Finset V).filter fun w ↦ G.Adj v w).card

private lemma card_degree_one_le_two_of_connected_max_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : G.Connected) (hdegree : ∀ v, finiteSimpleDegree G v ≤ 2) :
    ((Finset.univ : Finset V).filter fun v ↦ finiteSimpleDegree G v = 1).card ≤ 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  let L := (Finset.univ : Finset V).filter fun v ↦ finiteSimpleDegree G v = 1
  have hsum_le : L.card + ∑ v, finiteSimpleDegree G v ≤ 2 * Fintype.card V := by
    calc
      L.card + ∑ v, finiteSimpleDegree G v =
          ∑ v : V, ((if finiteSimpleDegree G v = 1 then 1 else 0) +
            finiteSimpleDegree G v) := by
        rw [show L.card = ∑ v : V,
            if finiteSimpleDegree G v = 1 then 1 else 0 by
          exact card_filter_eq_sum_indicator Finset.univ
            (fun v ↦ finiteSimpleDegree G v = 1)]
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ _v : V, 2 := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : finiteSimpleDegree G v = 1
        · simp [hv]
        · simp only [hv, if_false, zero_add]
          exact hdegree v
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have hconnected := hG.card_vert_le_card_edgeSet_add_one
  have hconnected' : Fintype.card V ≤ Nat.card G.edgeSet + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hconnected
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have hdegree_eq (v : V) : finiteSimpleDegree G v = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree]
    simp [finiteSimpleDegree, G.neighborFinset_eq_filter]
  have hsum_degree_eq : (∑ v, finiteSimpleDegree G v) = ∑ v, G.degree v := by
    apply Finset.sum_congr rfl
    intro v _
    exact hdegree_eq v
  rw [← hsum_degree_eq] at hhandshake
  rw [G.edgeFinset_card, ← Nat.card_eq_fintype_card] at hhandshake
  change L.card ≤ 2
  omega

private lemma exists_ne_finiteSimpleDegree_one_of_connected_max_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdegree : ∀ w, finiteSimpleDegree G w ≤ 2)
    (v : V) (hv : finiteSimpleDegree G v = 1) :
    ∃ w, w ≠ v ∧ finiteSimpleDegree G w = 1 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hdegree_eq (w : V) : finiteSimpleDegree G w = G.degree w := by
    rw [← G.card_neighborFinset_eq_degree]
    simp [finiteSimpleDegree, G.neighborFinset_eq_filter]
  have hvodd : Odd (G.degree v) := by
    rw [← hdegree_eq, hv]
    exact odd_one
  obtain ⟨w, hwv, hwodd⟩ := G.exists_ne_odd_degree_of_exists_odd_degree v hvodd
  refine ⟨w, hwv, ?_⟩
  have hwle := hdegree w
  rw [hdegree_eq] at hwle
  rcases hwodd with ⟨k, hk⟩
  rw [hdegree_eq, hk]
  rw [hk] at hwle
  omega

private lemma outside_leaves_le_exceptional_degree_sum_of_tree
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V)
    (E : Finset V) (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V)
    (hdegree : ∀ v ∉ E, finiteSimpleDegree T v ≤ 2) :
    ((Finset.univ.filter fun v : V ↦
      v ∉ E ∧ finiteSimpleDegree T v = 1).card) ≤
      2 + ∑ v ∈ E, finiteSimpleDegree T v := by
  classical
  letI : DecidableRel T.Adj := Classical.decRel _
  let O := (Finset.univ : Finset V) \ E
  let L := O.filter fun v ↦ finiteSimpleDegree T v = 1
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have hdegree_eq (v : V) : finiteSimpleDegree T v = T.degree v := by
    rw [← T.card_neighborFinset_eq_degree]
    simp [finiteSimpleDegree, T.neighborFinset_eq_filter]
  have hpositive (v : V) : 0 < finiteSimpleDegree T v := by
    rw [hdegree_eq, T.degree_pos]
    exact hT.preconnected.not_isIsolated v
  have hout_degree : ∀ v ∈ O,
      finiteSimpleDegree T v = 1 ∨ finiteSimpleDegree T v = 2 := by
    intro v hv
    have hvE : v ∉ E := by
      simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hv
    have hvle := hdegree v hvE
    have hvpos := hpositive v
    omega
  have hLdef :
      (Finset.univ.filter fun v : V ↦
        v ∉ E ∧ finiteSimpleDegree T v = 1) = L := by
    ext v
    simp [L, O]
  have hout_sum : (∑ v ∈ O, finiteSimpleDegree T v) + L.card = 2 * O.card := by
    calc
      (∑ v ∈ O, finiteSimpleDegree T v) + L.card =
          ∑ v ∈ O, (finiteSimpleDegree T v +
            if finiteSimpleDegree T v = 1 then 1 else 0) := by
        rw [show L.card = ∑ v ∈ O,
            if finiteSimpleDegree T v = 1 then 1 else 0 by
          exact card_filter_eq_sum_indicator O
            (fun v ↦ finiteSimpleDegree T v = 1)]
        rw [Finset.sum_add_distrib]
      _ = ∑ _v ∈ O, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rcases hout_degree v hv with hvone | hvtwo
        · simp [hvone]
        · simp [hvtwo]
      _ = 2 * O.card := by simp [Nat.mul_comm]
  have hEsub : E ⊆ (Finset.univ : Finset V) := Finset.subset_univ E
  have hsum_split := Finset.sum_sdiff hEsub
    (f := fun v ↦ finiteSimpleDegree T v)
  have hcard_split := Finset.card_sdiff_add_card_eq_card hEsub
  change (∑ v ∈ O, finiteSimpleDegree T v) +
      ∑ v ∈ E, finiteSimpleDegree T v =
    ∑ v : V, finiteSimpleDegree T v at hsum_split
  change O.card + E.card = Fintype.card V at hcard_split
  have htree_card := (T.isTree_iff_connected_and_card.mp hT).2
  have hhandshake := T.sum_degrees_eq_twice_card_edges
  have hsum_degree_eq : (∑ v, finiteSimpleDegree T v) = ∑ v, T.degree v := by
    apply Finset.sum_congr rfl
    intro v _
    exact hdegree_eq v
  rw [← hsum_degree_eq] at hhandshake
  rw [T.edgeFinset_card, ← Nat.card_eq_fintype_card] at hhandshake
  have htree_card' : Nat.card T.edgeSet + 1 = Fintype.card V :=
    htree_card.trans Nat.card_eq_fintype_card
  rw [hhandshake] at hsum_split
  rw [← htree_card'] at hcard_split
  rw [hLdef]
  change L.card ≤ 2 + ∑ v ∈ E, finiteSimpleDegree T v
  omega

theorem equality_degree_four_local_classification {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : Finset (Fin (2 * p))) (hB : B ∈ Q.1.parts)
    (hBne : B ∉ equalityExceptionalVertices Q.1) :
    IsEqualityInternal Q.1 B ∨ IsEqualityLoopTerminal Q.1 B ∨
      IsEqualityFourEdgeTerminal Q.1 B := by
  classical
  let b : EqualityVertex Q.1 := ⟨B, hB⟩
  let N := equalityNeighbors Q.1 b
  have hBcard : B.card = 2 :=
    (nonexceptional_card_and_even_multiplicity Q B hB hBne).1
  have hdegree := equality_neighbor_sum_decomposition hp Q b
  have hNnonempty := equality_neighbor_nonempty_of_nonexceptional hp Q b hBne
  have hsum_ge : 2 * N.card ≤
      ∑ C ∈ N, equalityEdgeMultiplicity Q.1 B C.1 := by
    calc
      2 * N.card = ∑ _C ∈ N, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ C ∈ N, equalityEdgeMultiplicity Q.1 B C.1 := by
        apply Finset.sum_le_sum
        intro C hC
        exact nonexceptional_neighbor_multiplicity_ge_two Q b C hBne hC
  have hNcard : N.card ≤ 2 := by
    change 2 * B.card = 2 * equalityLoopsAt Q.1 B +
      ∑ C ∈ N, equalityEdgeMultiplicity Q.1 B C.1 at hdegree
    omega
  have hNpos : 0 < N.card := Finset.card_pos.mpr hNnonempty
  have hcases : N.card = 1 ∨ N.card = 2 := by omega
  rcases hcases with hNone | hNtwo
  · obtain ⟨C, hNC⟩ := Finset.card_eq_one.mp hNone
    have hCmem : C ∈ N := by simp [hNC]
    have hadj := mem_equalityNeighbors Q.1 b C |>.mp hCmem
    have hmultge := nonexceptional_neighbor_multiplicity_ge_two Q b C hBne hCmem
    have hdecomp : 4 = 2 * equalityLoopsAt Q.1 B +
        equalityEdgeMultiplicity Q.1 B C.1 := by
      change 2 * B.card = 2 * equalityLoopsAt Q.1 B +
        ∑ C' ∈ N, equalityEdgeMultiplicity Q.1 B C'.1 at hdegree
      rw [hBcard, hNC] at hdegree
      simpa using hdegree
    have heven :=
      (nonexceptional_card_and_even_multiplicity Q B hB hBne).2
        C.1 C.2 (fun h ↦ hadj.1 (Subtype.ext h.symm))
    rcases heven with ⟨k, hk⟩
    have halts :
        (equalityLoopsAt Q.1 B = 1 ∧
          equalityEdgeMultiplicity Q.1 B C.1 = 2) ∨
        (equalityLoopsAt Q.1 B = 0 ∧
          equalityEdgeMultiplicity Q.1 B C.1 = 4) := by
      rw [hk] at hdecomp hmultge ⊢
      omega
    rcases halts with hloop | hfour
    · exact Or.inr (Or.inl ⟨hloop.1, C.1, C.2,
        (fun h ↦ hadj.1 (Subtype.ext h.symm)),
        hloop.2, fun A hA hAB hAC ↦ by
          let a : EqualityVertex Q.1 := ⟨A, hA⟩
          have haC : a ≠ C := by exact fun h ↦ hAC (Subtype.ext_iff.mp h)
          have haB : a ≠ b := by exact fun h ↦ hAB (Subtype.ext_iff.mp h)
          apply equality_multiplicity_eq_zero_of_not_neighbor Q b a haB.symm
          change a ∉ N
          rw [hNC]
          simpa only [Finset.mem_singleton] using haC⟩)
    · exact Or.inr (Or.inr ⟨hfour.1, C.1, C.2,
        (fun h ↦ hadj.1 (Subtype.ext h.symm)),
        hfour.2, fun A hA hAB hAC ↦ by
          let a : EqualityVertex Q.1 := ⟨A, hA⟩
          have haC : a ≠ C := by exact fun h ↦ hAC (Subtype.ext_iff.mp h)
          have haB : a ≠ b := by exact fun h ↦ hAB (Subtype.ext_iff.mp h)
          apply equality_multiplicity_eq_zero_of_not_neighbor Q b a haB.symm
          change a ∉ N
          rw [hNC]
          simpa only [Finset.mem_singleton] using haC⟩)
  · obtain ⟨C, D, hCD, hNCD⟩ := Finset.card_eq_two.mp hNtwo
    have hCmem : C ∈ N := by simp [hNCD]
    have hDmem : D ∈ N := by simp [hNCD]
    have hCadj := mem_equalityNeighbors Q.1 b C |>.mp hCmem
    have hDadj := mem_equalityNeighbors Q.1 b D |>.mp hDmem
    have hCge := nonexceptional_neighbor_multiplicity_ge_two Q b C hBne hCmem
    have hDge := nonexceptional_neighbor_multiplicity_ge_two Q b D hBne hDmem
    change 2 ≤ equalityEdgeMultiplicity Q.1 B C.1 at hCge
    change 2 ≤ equalityEdgeMultiplicity Q.1 B D.1 at hDge
    have hdecomp : 4 = 2 * equalityLoopsAt Q.1 B +
        (equalityEdgeMultiplicity Q.1 B C.1 +
          equalityEdgeMultiplicity Q.1 B D.1) := by
      change 2 * B.card = 2 * equalityLoopsAt Q.1 B +
        ∑ C' ∈ N, equalityEdgeMultiplicity Q.1 B C'.1 at hdegree
      rw [hBcard, hNCD] at hdegree
      simpa [hCD] using hdegree
    have hloop : equalityLoopsAt Q.1 B = 0 := by omega
    have hCeq : equalityEdgeMultiplicity Q.1 B C.1 = 2 := by omega
    have hDeq : equalityEdgeMultiplicity Q.1 B D.1 = 2 := by omega
    exact Or.inl ⟨hloop, C.1, C.2, D.1, D.2,
      fun h ↦ hCD (Subtype.ext h),
      (fun h ↦ hCadj.1 (Subtype.ext h.symm)),
      (fun h ↦ hDadj.1 (Subtype.ext h.symm)),
      hCeq, hDeq, fun A hA hAB hAC hAD ↦ by
        let a : EqualityVertex Q.1 := ⟨A, hA⟩
        have haC : a ≠ C := by exact fun h ↦ hAC (Subtype.ext_iff.mp h)
        have haD : a ≠ D := by exact fun h ↦ hAD (Subtype.ext_iff.mp h)
        have haB : a ≠ b := by exact fun h ↦ hAB (Subtype.ext_iff.mp h)
        apply equality_multiplicity_eq_zero_of_not_neighbor Q b a haB.symm
        change a ∉ N
        rw [hNCD]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact not_or_intro haC haD⟩

private lemma finiteSimpleDegree_equalitySimpleGraph {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : EqualityVertex P) :
    finiteSimpleDegree (equalitySimpleGraph P) B = (equalityNeighbors P B).card := by
  classical
  simp [finiteSimpleDegree, equalityNeighbors]

private lemma finiteSimpleDegree_eq_two_of_internal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityInternal P B.1) :
    finiteSimpleDegree (equalitySimpleGraph P) B = 2 := by
  rw [finiteSimpleDegree_equalitySimpleGraph]
  obtain ⟨C, D, hCD, hN⟩ := equalityNeighbors_eq_pair_of_internal P B hB
  rw [hN]
  simp [hCD]

private lemma finiteSimpleDegree_eq_one_of_loop_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityLoopTerminal P B.1) :
    finiteSimpleDegree (equalitySimpleGraph P) B = 1 := by
  rw [finiteSimpleDegree_equalitySimpleGraph]
  obtain ⟨C, hN⟩ := equalityNeighbors_eq_singleton_of_loop_terminal P B hB
  rw [hN]
  simp

private lemma finiteSimpleDegree_eq_one_of_four_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B : EqualityVertex P) (hB : IsEqualityFourEdgeTerminal P B.1) :
    finiteSimpleDegree (equalitySimpleGraph P) B = 1 := by
  rw [finiteSimpleDegree_equalitySimpleGraph]
  obtain ⟨C, hN⟩ := equalityNeighbors_eq_singleton_of_four_terminal P B hB
  rw [hN]
  simp

private lemma nonexceptional_finiteSimpleDegree_le_two {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) (B : EqualityVertex Q.1)
    (hBne : B.1 ∉ equalityExceptionalVertices Q.1) :
    finiteSimpleDegree (equalitySimpleGraph Q.1) B ≤ 2 := by
  rcases equality_degree_four_local_classification hp Q B.1 B.2 hBne with
    hB | hB | hB
  · rw [finiteSimpleDegree_eq_two_of_internal Q.1 B hB]
  · rw [finiteSimpleDegree_eq_one_of_loop_terminal Q.1 B hB]
    omega
  · rw [finiteSimpleDegree_eq_one_of_four_terminal Q.1 B hB]
    omega

private lemma equality_multiplicity_le_two_of_internal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B A : EqualityVertex P) (hB : IsEqualityInternal P B.1)
    (hAB : A.1 ≠ B.1) : equalityEdgeMultiplicity P B.1 A.1 ≤ 2 := by
  rcases hB with ⟨_, C, hC, D, hD, _, _, _, hCmult, hDmult, hother⟩
  by_cases hAC : A.1 = C
  · rw [hAC, hCmult]
  by_cases hAD : A.1 = D
  · rw [hAD, hDmult]
  rw [hother A.1 A.2 hAB hAC hAD]
  omega

private lemma equality_multiplicity_le_two_of_loop_terminal {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q)))
    (B A : EqualityVertex P) (hB : IsEqualityLoopTerminal P B.1)
    (hAB : A.1 ≠ B.1) : equalityEdgeMultiplicity P B.1 A.1 ≤ 2 := by
  rcases hB with ⟨_, C, hC, _, hCmult, hother⟩
  by_cases hAC : A.1 = C
  · rw [hAC, hCmult]
  rw [hother A.1 A.2 hAB hAC]
  omega

private lemma four_terminal_neighbor_is_four_terminal {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B C : EqualityVertex Q.1) (hBfour : IsEqualityFourEdgeTerminal Q.1 B.1)
    (hBCmult : equalityEdgeMultiplicity Q.1 B.1 C.1 = 4)
    (hBC : B.1 ≠ C.1)
    (hCne : C.1 ∉ equalityExceptionalVertices Q.1) :
    IsEqualityFourEdgeTerminal Q.1 C.1 := by
  have hCBmult : equalityEdgeMultiplicity Q.1 C.1 B.1 = 4 := by
    rw [equalityEdgeMultiplicity_symm, hBCmult]
  rcases equality_degree_four_local_classification hp Q C.1 C.2 hCne with
    hCinternal | hCloop | hCfour
  · have hle := equality_multiplicity_le_two_of_internal Q.1 C B hCinternal hBC
    rw [hCBmult] at hle
    omega
  · have hle := equality_multiplicity_le_two_of_loop_terminal Q.1 C B hCloop hBC
    rw [hCBmult] at hle
    omega
  · exact hCfour

private lemma exceptional_empty_four_terminal_global {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (hE : equalityExceptionalVertices Q.1 = ∅)
    (U : Finset (Fin (2 * p))) (hU : U ∈ Q.1.parts)
    (hUfour : IsEqualityFourEdgeTerminal Q.1 U) :
    Q.1.parts.card = 2 ∧
      ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B := by
  classical
  rcases hUfour with ⟨hUloop, V, hV, hVU, hUVmult, hUother⟩
  let u : EqualityVertex Q.1 := ⟨U, hU⟩
  let v : EqualityVertex Q.1 := ⟨V, hV⟩
  have huv : u ≠ v := fun h ↦ hVU (Subtype.ext_iff.mp h).symm
  have hVne : V ∉ equalityExceptionalVertices Q.1 := by simp [hE]
  have hUfour' : IsEqualityFourEdgeTerminal Q.1 U :=
    ⟨hUloop, V, hV, hVU, hUVmult, hUother⟩
  have hVfour : IsEqualityFourEdgeTerminal Q.1 V :=
    four_terminal_neighbor_is_four_terminal hp Q u v hUfour' hUVmult
      hVU.symm hVne
  obtain ⟨Z, hNuZ⟩ := equalityNeighbors_eq_singleton_of_four_terminal Q.1 u hUfour'
  have hv_mem_u : v ∈ equalityNeighbors Q.1 u := by
    apply mem_equalityNeighbors Q.1 u v |>.mpr
    exact ⟨huv, by simpa only [u, v] using (show 0 <
      equalityEdgeMultiplicity Q.1 U V by omega)⟩
  have hZ : Z = v := by
    rw [hNuZ] at hv_mem_u
    exact (Finset.mem_singleton.mp hv_mem_u).symm
  have hNu : equalityNeighbors Q.1 u = {v} := by simpa [hZ] using hNuZ
  obtain ⟨W, hNvW⟩ := equalityNeighbors_eq_singleton_of_four_terminal Q.1 v hVfour
  have hu_mem_v : u ∈ equalityNeighbors Q.1 v := by
    apply mem_equalityNeighbors Q.1 v u |>.mpr
    exact ⟨huv.symm, by rw [equalityEdgeMultiplicity_symm, hUVmult]; omega⟩
  have hW : W = u := by
    rw [hNvW] at hu_mem_v
    exact (Finset.mem_singleton.mp hu_mem_v).symm
  have hNv : equalityNeighbors Q.1 v = {u} := by simpa [hW] using hNvW
  have hall : ∀ A : EqualityVertex Q.1, A = u ∨ A = v := by
    intro A
    have hreach := equalitySimpleGraph_preconnected hp Q u A
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact Or.inl rfl
    | @tail B C _ hBC ih =>
        rcases ih with hBu | hBv
        · subst B
          have hmem := mem_equalityNeighbors Q.1 u C |>.mpr hBC
          rw [hNu] at hmem
          exact Or.inr (Finset.mem_singleton.mp hmem)
        · subst B
          have hmem := mem_equalityNeighbors Q.1 v C |>.mpr hBC
          rw [hNv] at hmem
          exact Or.inl (Finset.mem_singleton.mp hmem)
  have hparts : Q.1.parts = {U, V} := by
    ext A
    constructor
    · intro hA
      rcases hall (⟨A, hA⟩ : EqualityVertex Q.1) with hAu | hAv
      · have : A = U := Subtype.ext_iff.mp hAu
        simp [this]
      · have : A = V := Subtype.ext_iff.mp hAv
        simp [this]
    · intro hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact hU
      · exact hV
  constructor
  · rw [hparts]
    have hUnot : U ∉ ({V} : Finset (Finset (Fin (2 * p)))) := by
      simpa only [Finset.mem_singleton] using hVU.symm
    rw [Finset.card_insert_of_notMem hUnot]
    simp
  · intro B hB
    rcases hall (⟨B, hB⟩ : EqualityVertex Q.1) with hBu | hBv
    · have : B = U := Subtype.ext_iff.mp hBu
      simpa [this] using hUfour'
    · have : B = V := Subtype.ext_iff.mp hBv
      simpa [this] using hVfour

theorem equality_exceptional_empty_classification {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (hE : equalityExceptionalVertices Q.1 = ∅) :
    (∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B) ∨
    (∃ U ∈ Q.1.parts, ∃ V ∈ Q.1.parts, U ≠ V ∧
      IsEqualityLoopTerminal Q.1 U ∧ IsEqualityLoopTerminal Q.1 V ∧
      ∀ B ∈ Q.1.parts, B ≠ U → B ≠ V → IsEqualityInternal Q.1 B) ∨
    (Q.1.parts.card = 2 ∧
      ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B) ∨
    (Q.1.parts.card = 1 ∧ equalityLoopOccurrences Q.1 = 2) := by
  classical
  have hpartsne : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  obtain ⟨B₀, hB₀⟩ := hpartsne
  letI : Nonempty (EqualityVertex Q.1) := ⟨⟨B₀, hB₀⟩⟩
  have hnonexceptional (B : EqualityVertex Q.1) :
      B.1 ∉ equalityExceptionalVertices Q.1 := by simp [hE]
  have hdegree (B : EqualityVertex Q.1) :
      finiteSimpleDegree (equalitySimpleGraph Q.1) B ≤ 2 :=
    nonexceptional_finiteSimpleDegree_le_two hp Q B (hnonexceptional B)
  have hconnected : (equalitySimpleGraph Q.1).Connected :=
    ⟨equalitySimpleGraph_preconnected hp Q⟩
  have hdegreeOneCard :=
    card_degree_one_le_two_of_connected_max_degree_two
      (equalitySimpleGraph Q.1) hconnected hdegree
  by_cases hfour : ∃ U ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 U
  · obtain ⟨U, hU, hUfour⟩ := hfour
    exact Or.inr (Or.inr (Or.inl
      (exceptional_empty_four_terminal_global hp Q hE U hU hUfour)))
  · by_cases hall : ∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B
    · exact Or.inl hall
    · push_neg at hall
      obtain ⟨U, hU, hUnotinternal⟩ := hall
      have hUlocal := equality_degree_four_local_classification hp Q U hU (by simp [hE])
      have hUloop : IsEqualityLoopTerminal Q.1 U := by
        rcases hUlocal with hUint | hUloop | hUfour
        · exact (hUnotinternal hUint).elim
        · exact hUloop
        · exact (hfour ⟨U, hU, hUfour⟩).elim
      let u : EqualityVertex Q.1 := ⟨U, hU⟩
      have huDegree : finiteSimpleDegree (equalitySimpleGraph Q.1) u = 1 :=
        finiteSimpleDegree_eq_one_of_loop_terminal Q.1 u hUloop
      obtain ⟨v, hvu, hvDegree⟩ :=
        exists_ne_finiteSimpleDegree_one_of_connected_max_degree_two
          (equalitySimpleGraph Q.1) hdegree u huDegree
      have hVloop : IsEqualityLoopTerminal Q.1 v.1 := by
        have hVlocal := equality_degree_four_local_classification hp Q v.1 v.2
          (hnonexceptional v)
        rcases hVlocal with hVint | hVloop | hVfour
        · have hvTwo := finiteSimpleDegree_eq_two_of_internal Q.1 v hVint
          rw [hvDegree] at hvTwo
          omega
        · exact hVloop
        · exact (hfour ⟨v.1, v.2, hVfour⟩).elim
      have hUV : U ≠ v.1 := fun h ↦ hvu (Subtype.ext h.symm)
      refine Or.inr (Or.inl ⟨U, hU, v.1, v.2, hUV, hUloop, hVloop, ?_⟩)
      intro B hB hBU hBV
      have hBlocal := equality_degree_four_local_classification hp Q B hB (by simp [hE])
      rcases hBlocal with hBint | hBloop | hBfour
      · exact hBint
      · exfalso
        let b : EqualityVertex Q.1 := ⟨B, hB⟩
        let L := (Finset.univ : Finset (EqualityVertex Q.1)).filter fun w ↦
          finiteSimpleDegree (equalitySimpleGraph Q.1) w = 1
        have hbDegree : finiteSimpleDegree (equalitySimpleGraph Q.1) b = 1 :=
          finiteSimpleDegree_eq_one_of_loop_terminal Q.1 b hBloop
        have huL : u ∈ L := by simp [L, huDegree]
        have hvL : v ∈ L := by simp [L, hvDegree]
        have hbL : b ∈ L := by simp [L, hbDegree]
        have hbu : b ≠ u := fun h ↦ hBU (Subtype.ext_iff.mp h)
        have hbv : b ≠ v := fun h ↦ hBV (Subtype.ext_iff.mp h)
        have hsub : ({u, v, b} : Finset (EqualityVertex Q.1)) ⊆ L := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact huL
          · exact hvL
          · exact hbL
        have hthree : ({u, v, b} : Finset (EqualityVertex Q.1)).card = 3 := by
          have hu_not : u ∉ ({v, b} : Finset (EqualityVertex Q.1)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hvu.symm, hbu.symm⟩
          have hv_not : v ∉ ({b} : Finset (EqualityVertex Q.1)) := by
            simpa only [Finset.mem_singleton] using hbv.symm
          rw [Finset.card_insert_of_notMem hu_not,
            Finset.card_insert_of_notMem hv_not]
          simp
        have hle := Finset.card_le_card hsub
        rw [hthree] at hle
        change L.card ≤ 2 at hdegreeOneCard
        omega
      · exact (hfour ⟨B, hB, hBfour⟩).elim

private lemma equalityLoopOccurrences_eq_sum_loopsAt {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    equalityLoopOccurrences P =
      ∑ B : EqualityVertex P, equalityLoopsAt P B.1 := by
  classical
  simp_rw [equalityLoopsAt_eq_vertex_filter]
  simp_rw [card_filter_eq_sum_indicator]
  rw [Finset.sum_comm]
  unfold equalityLoopOccurrences
  rw [card_filter_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro e _
  let U := equalityVertexAt P e
  let V := equalityVertexAt P (cyclicSucc e)
  have hparts : (P.part e = P.part (cyclicSucc e)) ↔ U = V := by
    simp only [U, V, equalityVertexAt, Subtype.ext_iff]
  change (if P.part e = P.part (cyclicSucc e) then 1 else 0) =
    ∑ B : EqualityVertex P, if U = B ∧ V = B then 1 else 0
  by_cases hpart : P.part e = P.part (cyclicSucc e)
  · have hUV : U = V := hparts.mp hpart
    have hterm : ∀ B : EqualityVertex P, (U = B ∧ V = B) ↔ U = B := by
      intro B
      rw [← hUV]
      simp
    simp only [hpart, if_true, hterm]
    rw [Fintype.sum_ite_eq]
  · have hUV : U ≠ V := fun h ↦ hpart (hparts.mpr h)
    have hfalse : ∀ B : EqualityVertex P, ¬(U = B ∧ V = B) := by
      intro B h
      exact hUV (h.1.trans h.2.symm)
    simp [hpart, hfalse]

private lemma equalityExceptionalVertices_subset_parts {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    equalityExceptionalVertices P ⊆ P.parts := by
  apply Finset.union_subset
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _

private noncomputable def equalityExceptionalVertexFinset {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) :
    Finset (EqualityVertex P) := by
  classical
  exact Finset.univ.filter fun B ↦ B.1 ∈ equalityExceptionalVertices P

@[simp] private lemma mem_equalityExceptionalVertexFinset {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (B : EqualityVertex P) :
    B ∈ equalityExceptionalVertexFinset P ↔
      B.1 ∈ equalityExceptionalVertices P := by
  classical
  simp [equalityExceptionalVertexFinset]

private lemma sum_equalityExceptionalVertexFinset {q : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin q))) (f : Finset (Fin q) → ℕ) :
    (∑ B ∈ equalityExceptionalVertexFinset P, f B.1) =
      ∑ B ∈ equalityExceptionalVertices P, f B := by
  classical
  apply Finset.sum_bij (fun B _ ↦ B.1)
  · intro B hB
    exact (mem_equalityExceptionalVertexFinset P B).mp hB
  · intro B₁ hB₁ B₂ hB₂ h
    exact Subtype.ext h
  · intro B hB
    let b : EqualityVertex P :=
      ⟨B, equalityExceptionalVertices_subset_parts P hB⟩
    exact ⟨b, (mem_equalityExceptionalVertexFinset P b).mpr hB, rfl⟩
  · intro B hB
    rfl

private lemma finiteSimpleDegree_le_of_le {V : Type*} [Fintype V]
    {G H : SimpleGraph V} (hGH : G ≤ H) (v : V) :
    finiteSimpleDegree G v ≤ finiteSimpleDegree H v := by
  classical
  unfold finiteSimpleDegree
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact hGH hw

private lemma finiteSimpleDegree_pos_of_preconnected
    {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Preconnected) (v : V) :
    0 < finiteSimpleDegree G v := by
  classical
  obtain ⟨w, hw⟩ := G.exists_adj_iff_not_isIsolated.mpr
    (hG.not_isIsolated v)
  unfold finiteSimpleDegree
  apply Finset.card_pos.mpr
  exact ⟨w, by simp [hw]⟩

private lemma equality_loop_plus_simple_degree_le_multigraph_degree {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t)
    (B : EqualityVertex Q.1) :
    equalityLoopsAt Q.1 B.1 + finiteSimpleDegree (equalitySimpleGraph Q.1) B ≤
      2 * B.1.card := by
  classical
  have hdecomp := equality_neighbor_sum_decomposition hp Q B
  have hdeg_card := finiteSimpleDegree_equalitySimpleGraph Q.1 B
  have hneighbors_le : (equalityNeighbors Q.1 B).card ≤
      ∑ C ∈ equalityNeighbors Q.1 B,
        equalityEdgeMultiplicity Q.1 B.1 C.1 := by
    calc
      (equalityNeighbors Q.1 B).card =
          ∑ _C ∈ equalityNeighbors Q.1 B, 1 := by simp
      _ ≤ ∑ C ∈ equalityNeighbors Q.1 B,
          equalityEdgeMultiplicity Q.1 B.1 C.1 := by
        apply Finset.sum_le_sum
        intro C hC
        have hadj := mem_equalityNeighbors Q.1 B C |>.mp hC
        exact hadj.2
  rw [hdeg_card]
  omega

theorem equality_loop_occurrences_le_exceptionalDegree_add_two {p s t : ℕ}
    (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    equalityLoopOccurrences Q.1 ≤ equalityExceptionalDegree Q.1 + 2 := by
  classical
  have hpartsne : Q.1.parts.Nonempty := by
    apply Q.1.parts_nonempty
    exact Finset.ne_empty_of_mem
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (2 * p)))
  obtain ⟨B₀, hB₀⟩ := hpartsne
  letI : Nonempty (EqualityVertex Q.1) := ⟨⟨B₀, hB₀⟩⟩
  have htypecard : Fintype.card (EqualityVertex Q.1) = Q.1.parts.card := by
    rw [Fintype.card_subtype]
    simp
  by_cases hcard : 2 ≤ Fintype.card (EqualityVertex Q.1)
  · have hconnected : (equalitySimpleGraph Q.1).Connected :=
      ⟨equalitySimpleGraph_preconnected hp Q⟩
    obtain ⟨T, hTG, hTtree⟩ := hconnected.exists_isTree_le
    let E := equalityExceptionalVertexFinset Q.1
    let O := (Finset.univ : Finset (EqualityVertex Q.1)) \ E
    let L := (Finset.univ : Finset (EqualityVertex Q.1)).filter fun B ↦
      B ∉ E ∧ finiteSimpleDegree T B = 1
    have hTdegree (B : EqualityVertex Q.1) (hBE : B ∉ E) :
        finiteSimpleDegree T B ≤ 2 := by
      have hTleG := finiteSimpleDegree_le_of_le hTG B
      have hBne : B.1 ∉ equalityExceptionalVertices Q.1 := by
        simpa only [E, mem_equalityExceptionalVertexFinset] using hBE
      exact hTleG.trans (nonexceptional_finiteSimpleDegree_le_two hp Q B hBne)
    have hleaf : L.card ≤ 2 + ∑ B ∈ E, finiteSimpleDegree T B := by
      have h := outside_leaves_le_exceptional_degree_sum_of_tree
        T E hTtree hcard hTdegree
      change L.card ≤ 2 + ∑ B ∈ E, finiteSimpleDegree T B
      exact h
    letI : Nontrivial (EqualityVertex Q.1) :=
      Fintype.one_lt_card_iff_nontrivial.mp hcard
    have hTpositive (B : EqualityVertex Q.1) : 0 < finiteSimpleDegree T B :=
      finiteSimpleDegree_pos_of_preconnected T hTtree.preconnected B
    have hout_point (B : EqualityVertex Q.1) (hBO : B ∈ O) :
        equalityLoopsAt Q.1 B.1 ≤
          if finiteSimpleDegree T B = 1 then 1 else 0 := by
      have hBE : B ∉ E := by
        simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hBO
      have hBne : B.1 ∉ equalityExceptionalVertices Q.1 := by
        simpa only [E, mem_equalityExceptionalVertexFinset] using hBE
      have hTleG := finiteSimpleDegree_le_of_le hTG B
      rcases equality_degree_four_local_classification hp Q B.1 B.2 hBne with
        hBint | hBloop | hBfour
      · rw [hBint.1]
        simp
      · have hGone := finiteSimpleDegree_eq_one_of_loop_terminal Q.1 B hBloop
        have hTone : finiteSimpleDegree T B = 1 := by
          have hpos := hTpositive B
          rw [hGone] at hTleG
          omega
        rw [hBloop.1, hTone]
        simp
      · rw [hBfour.1]
        simp
    have hout_loops : (∑ B ∈ O, equalityLoopsAt Q.1 B.1) ≤ L.card := by
      calc
        (∑ B ∈ O, equalityLoopsAt Q.1 B.1) ≤
            ∑ B ∈ O, if finiteSimpleDegree T B = 1 then 1 else 0 := by
          apply Finset.sum_le_sum
          intro B hBO
          exact hout_point B hBO
        _ = L.card := by
          have hL : L = O.filter (fun B ↦ finiteSimpleDegree T B = 1) := by
            ext B
            simp [L, O]
          rw [hL]
          exact (card_filter_eq_sum_indicator O
            (fun B ↦ finiteSimpleDegree T B = 1)).symm
    have hEpoint (B : EqualityVertex Q.1) :
        equalityLoopsAt Q.1 B.1 + finiteSimpleDegree T B ≤ 2 * B.1.card := by
      have hTleG := finiteSimpleDegree_le_of_le hTG B
      exact (Nat.add_le_add_left hTleG _).trans
        (equality_loop_plus_simple_degree_le_multigraph_degree hp Q B)
    have hEbudget :
        (∑ B ∈ E, equalityLoopsAt Q.1 B.1) +
          (∑ B ∈ E, finiteSimpleDegree T B) ≤
            equalityExceptionalDegree Q.1 := by
      calc
        (∑ B ∈ E, equalityLoopsAt Q.1 B.1) +
            (∑ B ∈ E, finiteSimpleDegree T B) =
            ∑ B ∈ E,
              (equalityLoopsAt Q.1 B.1 + finiteSimpleDegree T B) := by
          rw [Finset.sum_add_distrib]
        _ ≤ ∑ B ∈ E, 2 * B.1.card := by
          apply Finset.sum_le_sum
          intro B _
          exact hEpoint B
        _ = equalityExceptionalDegree Q.1 := by
          simpa only [E, equalityExceptionalDegree] using
            (sum_equalityExceptionalVertexFinset Q.1 (fun B ↦ 2 * B.card))
    have hEsub : E ⊆ (Finset.univ : Finset (EqualityVertex Q.1)) :=
      Finset.subset_univ E
    have hsum_split := Finset.sum_sdiff hEsub
      (f := fun B : EqualityVertex Q.1 ↦ equalityLoopsAt Q.1 B.1)
    change (∑ B ∈ O, equalityLoopsAt Q.1 B.1) +
        (∑ B ∈ E, equalityLoopsAt Q.1 B.1) =
          ∑ B : EqualityVertex Q.1, equalityLoopsAt Q.1 B.1 at hsum_split
    calc
      equalityLoopOccurrences Q.1 =
          (∑ B ∈ O, equalityLoopsAt Q.1 B.1) +
            (∑ B ∈ E, equalityLoopsAt Q.1 B.1) := by
        rw [equalityLoopOccurrences_eq_sum_loopsAt, hsum_split]
      _ ≤ L.card + ∑ B ∈ E, equalityLoopsAt Q.1 B.1 :=
        Nat.add_le_add_right hout_loops _
      _ ≤ (2 + ∑ B ∈ E, finiteSimpleDegree T B) +
          ∑ B ∈ E, equalityLoopsAt Q.1 B.1 :=
        Nat.add_le_add_right hleaf _
      _ = ((∑ B ∈ E, equalityLoopsAt Q.1 B.1) +
          ∑ B ∈ E, finiteSimpleDegree T B) + 2 := by omega
      _ ≤ equalityExceptionalDegree Q.1 + 2 := Nat.add_le_add_right hEbudget 2
  · have hcardone : Fintype.card (EqualityVertex Q.1) = 1 := by
      have hpos : 0 < Fintype.card (EqualityVertex Q.1) :=
        Fintype.card_pos_iff.mpr inferInstance
      omega
    have hpartscard : Q.1.parts.card = 1 := by omega
    obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hpartscard
    have hBmem : B ∈ Q.1.parts := by rw [hparts]; simp
    have hBcard : B.card = 2 * p := by
      have hsum := Q.1.sum_card_parts
      rw [hparts] at hsum
      simpa only [Finset.sum_singleton, Finset.card_univ, Fintype.card_fin] using hsum
    have hBexceptional : B ∈ equalityExceptionalVertices Q.1 := by
      apply Finset.mem_union_right
      simp only [Finset.mem_filter, hBmem, true_and]
      omega
    have hExceptional : equalityExceptionalVertices Q.1 = {B} := by
      ext A
      constructor
      · intro hA
        have hApart := equalityExceptionalVertices_subset_parts Q.1 hA
        rw [hparts] at hApart
        simpa only [Finset.mem_singleton] using hApart
      · intro hA
        have hAB : A = B := Finset.mem_singleton.mp hA
        simpa [hAB] using hBexceptional
    have hloopcard : equalityLoopOccurrences Q.1 ≤ 2 * p := by
      unfold equalityLoopOccurrences
      calc
        (Finset.univ.filter fun i : Fin (2 * p) ↦
          Q.1.part i = Q.1.part (cyclicSucc i)).card ≤
            (Finset.univ : Finset (Fin (2 * p))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 * p := by simp
    unfold equalityExceptionalDegree
    rw [hExceptional]
    simp only [Finset.sum_singleton]
    omega

theorem degree_four_classification_and_loop_bound
    {p s t : ℕ} (hp : 2 ≤ p) (Q : SelectorEqualityData p s t) :
    (∀ B ∈ Q.1.parts, B ∉ equalityExceptionalVertices Q.1 →
      IsEqualityInternal Q.1 B ∨ IsEqualityLoopTerminal Q.1 B ∨
        IsEqualityFourEdgeTerminal Q.1 B) ∧
    (equalityExceptionalVertices Q.1 = ∅ →
      (∀ B ∈ Q.1.parts, IsEqualityInternal Q.1 B) ∨
      (∃ U ∈ Q.1.parts, ∃ V ∈ Q.1.parts, U ≠ V ∧
        IsEqualityLoopTerminal Q.1 U ∧ IsEqualityLoopTerminal Q.1 V ∧
        ∀ B ∈ Q.1.parts, B ≠ U → B ≠ V → IsEqualityInternal Q.1 B) ∨
      (Q.1.parts.card = 2 ∧
        ∀ B ∈ Q.1.parts, IsEqualityFourEdgeTerminal Q.1 B) ∨
      (Q.1.parts.card = 1 ∧ equalityLoopOccurrences Q.1 = 2)) ∧
    equalityLoopOccurrences Q.1 ≤ 4 * t + 12 * s + 2 := by
  constructor
  · intro B hB hBne
    exact equality_degree_four_local_classification hp Q B hB hBne
  constructor
  · exact equality_exceptional_empty_classification hp Q
  · have hloop := equality_loop_occurrences_le_exceptionalDegree_add_two hp Q
    have hbudget := (selector_exceptional_vertex_degree_budget hp Q).2
    omega

#print axioms degree_four_classification_and_loop_bound

end Problem56
