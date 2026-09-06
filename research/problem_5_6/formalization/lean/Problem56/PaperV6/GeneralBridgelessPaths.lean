import Problem56.PaperV6.GeneralBridgelessExpected

namespace Problem56.PaperV6

/-- Stop a walk at its first visit to a designated set. Every source of a
retained step is outside that set, including when the original walk revisits
vertices. This is the reachability part of ear extraction. -/
theorem exists_first_hit_walk {α : Type*} (R : α → α → Prop)
    (S : Set α) {a b : α} (h : Relation.ReflTransGen R a b) (hb : b ∈ S) :
    ∃ c ∈ S, Relation.ReflTransGen (fun x y => x ∉ S ∧ R x y) a c := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨b, hb, Relation.ReflTransGen.refl⟩
  | @head x y hxy hyb ih =>
    by_cases hx : x ∈ S
    · exact ⟨x, hx, Relation.ReflTransGen.refl⟩
    · obtain ⟨c, hc, hyc⟩ := ih
      exact ⟨c, hc, hyc.head ⟨hx, hxy⟩⟩

/-- A return step has not yet entered the current graph, and uses an edge
different from both the entering edge and all edges of the current graph. -/
def unusedReturnStep {ι ε : Type*} (src dst : ε → ι)
    (vertices : Set ι) (used : Set ε) (entering : ε) (a b : ι) : Prop :=
  a ∉ vertices ∧ ∃ f : ε, f ∉ used ∧ f ≠ entering ∧
    ((src f = a ∧ dst f = b) ∨ (src f = b ∧ dst f = a))

/-- The non-cutting-edge argument in published Lemma 16: after an edge from
the current graph reaches `z`, a walk returns from `z` to that graph using
neither the entering edge nor any already used edge. The walk stops at its
first old vertex. This permits the zero-length return when `z` is already an
old vertex, including loops. Simple-path extraction and insertion are separate
remaining obligations; this theorem does not claim graph conversion. -/
theorem exists_unused_return_walk {ι ε : Type*} (src dst : ε → ι)
    (hbridge : EveryEdgeDeletionConnected src dst)
    (vertices : Set ι) (used : Set ε)
    (hends : ∀ f ∈ used, src f ∈ vertices ∧ dst f ∈ vertices)
    (entering : ε) (x z : ι) (hx : x ∈ vertices) :
    ∃ y ∈ vertices,
      Relation.ReflTransGen (unusedReturnStep src dst vertices used entering) z y := by
  obtain ⟨y, hy, hpath⟩ := exists_first_hit_walk
    (graphAdjacent
      (fun f : {f : ε // f ≠ entering} => src f.1)
      (fun f : {f : ε // f ≠ entering} => dst f.1))
    vertices (hbridge entering z x) hx
  refine ⟨y, hy, ?_⟩
  clear hy
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hp hab ih =>
    rcases hab with ⟨ha, f, horient⟩
    apply ih.tail
    refine ⟨ha, f.1, ?_, f.2, horient⟩
    intro hf
    rcases horient with hforward | hbackward
    · exact ha (hforward.1 ▸ (hends f.1 hf).1)
    · exact ha (hbackward.2 ▸ (hends f.1 hf).2)

end Problem56.PaperV6
