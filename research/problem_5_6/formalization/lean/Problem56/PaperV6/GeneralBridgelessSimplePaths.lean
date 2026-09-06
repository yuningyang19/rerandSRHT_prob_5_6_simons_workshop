import Problem56.PaperV6.GeneralBridgelessPaths

namespace Problem56.PaperV6

/-- Erase cycles from a relational walk without introducing new edges.
This generic lemma requires no symmetry or finiteness of the ambient type. -/
theorem exists_simple_chain_of_walk {α : Type*} (R : α → α → Prop)
    {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ l : List α, (a :: l).IsChain R ∧
      (a :: l).getLast (List.cons_ne_nil _ _) = b ∧ (a :: l).Nodup := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .singleton _, rfl, by simp⟩
  | @head x y hxy hyb ih =>
    obtain ⟨l, hchain, hlast, hnodup⟩ := ih
    by_cases hx : x ∈ y :: l
    · obtain ⟨p, q, hpq⟩ := List.mem_iff_append.mp hx
      have hchain' : (p ++ x :: q).IsChain R := hpq ▸ hchain
      have hnodup' : (p ++ x :: q).Nodup := hpq ▸ hnodup
      refine ⟨q, hchain'.right_of_append, ?_, hnodup'.of_append_right⟩
      have hlast' : (p ++ x :: q).getLast (by simp) = b := by
        simpa only [hpq] using hlast
      simpa only [List.getLast_append_of_right_ne_nil p (x :: q)
        (List.cons_ne_nil _ _)] using hlast'
    · exact ⟨y :: l, .cons_cons hxy hchain,
        by simpa only [List.getLast_cons_cons] using hlast,
        List.nodup_cons.mpr ⟨hx, hnodup⟩⟩

/-- The simple return path needed in the published ear insertion. Every step
before the final endpoint starts outside the old graph and carries an unused
indexed edge different from the entering edge. No parity is assumed. -/
theorem exists_simple_unused_return_path {ι ε : Type*} (src dst : ε → ι)
    (hbridge : EveryEdgeDeletionConnected src dst)
    (vertices : Set ι) (used : Set ε)
    (hends : ∀ f ∈ used, src f ∈ vertices ∧ dst f ∈ vertices)
    (entering : ε) (x z : ι) (hx : x ∈ vertices) :
    ∃ (y : ι) (l : List ι), y ∈ vertices ∧
      (z :: l).IsChain (unusedReturnStep src dst vertices used entering) ∧
      (z :: l).getLast (List.cons_ne_nil _ _) = y ∧ (z :: l).Nodup := by
  obtain ⟨y, hy, hwalk⟩ := exists_unused_return_walk
    src dst hbridge vertices used hends entering x z hx
  obtain ⟨l, hchain, hlast, hnodup⟩ := exists_simple_chain_of_walk _ hwalk
  exact ⟨y, l, hy, hchain, hlast, hnodup⟩

end Problem56.PaperV6
