import Problem56.PaperV6.GeneralBridgelessSimplePaths

namespace Problem56.PaperV6

/-- Connectivity finds a fresh edge touching a nonempty current graph whenever
some original edge remains unused. This keeps indexed parallel edges distinct. -/
theorem exists_unused_edge_at_old_vertex {ι ε : Type*} (src dst : ε → ι)
    (hconn : GraphConnected src dst) (vertices : Set ι) (used : Set ε)
    (hends : ∀ f ∈ used, src f ∈ vertices ∧ dst f ∈ vertices)
    (hne : vertices.Nonempty) (hfresh : ∃ e : ε, e ∉ used) :
    ∃ (x : ι) (e : ε), x ∈ vertices ∧ e ∉ used ∧
      (src e = x ∨ dst e = x) := by
  classical
  by_contra hnone
  have hclosed : ∀ a b, graphAdjacent src dst a b →
      a ∈ vertices → b ∈ vertices := by
    intro a b hab ha
    obtain ⟨e, he⟩ := hab
    by_cases heused : e ∈ used
    · rcases he with hforward | hbackward
      · exact hforward.2 ▸ (hends e heused).2
      · exact hbackward.1 ▸ (hends e heused).1
    · exfalso
      apply hnone
      refine ⟨a, e, ha, heused, ?_⟩
      rcases he with hforward | hbackward
      · exact Or.inl hforward.1
      · exact Or.inr hbackward.2
  obtain ⟨a, ha⟩ := hne
  have hall : ∀ b, b ∈ vertices := by
    intro b
    induction hconn a b with
    | refl => exact ha
    | tail hp hab ih => exact hclosed _ _ hab ih
  obtain ⟨e, he⟩ := hfresh
  exact hnone ⟨src e, e, hall (src e), he, Or.inl rfl⟩

/-- Complete primitive ear selection: a fresh indexed entering edge, followed
by a vertex-simple return path whose internal vertices lie outside the old
graph and whose edges avoid both the old graph and the entering edge. -/
theorem exists_fresh_ear_path {ι ε : Type*} (src dst : ε → ι)
    (hconn : GraphConnected src dst)
    (hbridge : EveryEdgeDeletionConnected src dst)
    (vertices : Set ι) (used : Set ε)
    (hends : ∀ f ∈ used, src f ∈ vertices ∧ dst f ∈ vertices)
    (hne : vertices.Nonempty) (hfresh : ∃ e : ε, e ∉ used) :
    ∃ (x z y : ι) (e : ε) (l : List ι),
      x ∈ vertices ∧ y ∈ vertices ∧ e ∉ used ∧
      ((src e = x ∧ dst e = z) ∨ (src e = z ∧ dst e = x)) ∧
      (z :: l).IsChain (unusedReturnStep src dst vertices used e) ∧
      (z :: l).getLast (List.cons_ne_nil _ _) = y ∧ (z :: l).Nodup := by
  obtain ⟨x, e, hx, he, hinc⟩ := exists_unused_edge_at_old_vertex
    src dst hconn vertices used hends hne hfresh
  rcases hinc with hsrc | hdst
  · obtain ⟨y, l, hy, hchain, hlast, hnodup⟩ := exists_simple_unused_return_path
      src dst hbridge vertices used hends e x (dst e) hx
    exact ⟨x, dst e, y, e, l, hx, hy, he, Or.inl ⟨hsrc, rfl⟩,
      hchain, hlast, hnodup⟩
  · obtain ⟨y, l, hy, hchain, hlast, hnodup⟩ := exists_simple_unused_return_path
      src dst hbridge vertices used hends e x (src e) hx
    exact ⟨x, src e, y, e, l, hx, hy, he, Or.inr ⟨rfl, hdst⟩,
      hchain, hlast, hnodup⟩

end Problem56.PaperV6
