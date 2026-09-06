import Problem56.PaperV6.GeneralBridgelessActiveGraph
import Problem56.PaperV6.GeneralBridgelessActivateEdge

namespace Problem56.PaperV6

/-- A concrete fresh ear already oriented in the current full graph. Its
internal original vertices are inactive, and its endpoints are active. These
are finite incidence data, not a DAG/analytic conclusion or an existence axiom. -/
structure StateFreshEar {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G) where
  internalCount : ℕ
  point : Fin (internalCount + 2) → S.current.Vertex
  edge : Fin (internalCount + 1) → G.Edge
  point_injective : Function.Injective point
  edge_fresh : ∀ i, edge i ∉ S.used
  source : ∀ i, S.current.src (S.oldEdge (edge i)) = point i.castSucc
  target : ∀ i, S.current.dst (S.oldEdge (edge i)) = point i.succ
  start_active : S.projection (point 0) ∈ S.active
  finish_active : S.projection (point (Fin.last (internalCount + 1))) ∈ S.active
  internal_inactive : ∀ i : Fin internalCount,
    S.projection (point ⟨i.1 + 1, by omega⟩) ∉ S.active

namespace StateFreshEar

variable {G : FiniteBoundaryGraph} {S : GeneralBridgelessState G}

def start (P : StateFreshEar S) : S.ActiveVertex := ⟨P.point 0, P.start_active⟩
def finish (P : StateFreshEar S) : S.ActiveVertex :=
  ⟨P.point (Fin.last (P.internalCount + 1)), P.finish_active⟩

def newActive (P : StateFreshEar S) : Set G.Vertex :=
  S.active ∪ Set.range (fun i => S.projection (P.point i))

def newUsed (P : StateFreshEar S) : Set G.Edge := S.used ∪ Set.range P.edge

def vertexEmbed (P : StateFreshEar S) : AdjoinedEarVertex S.ActiveVertex P.internalCount →
    S.current.Vertex
  | Sum.inl v => v.1
  | Sum.inr i => P.point ⟨i.1 + 1, by omega⟩

theorem vertexEmbed_injective (P : StateFreshEar S) : Function.Injective P.vertexEmbed := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hab)
    | inr b =>
      exfalso
      apply P.internal_inactive b
      change a.1 = P.point ⟨b.1 + 1, by omega⟩ at hab
      rw [← hab]
      exact a.2
  | inr a =>
    cases b with
    | inl b =>
      exfalso
      apply P.internal_inactive a
      change P.point ⟨a.1 + 1, by omega⟩ = b.1 at hab
      rw [hab]
      exact b.2
    | inr b =>
      have h := congrArg (fun i : Fin (P.internalCount + 2) => i.1) (P.point_injective hab)
      apply congrArg Sum.inr
      apply Fin.ext
      dsimp only at h
      omega

theorem vertexEmbed_point (P : StateFreshEar S) (i : Fin (P.internalCount + 2)) :
    P.vertexEmbed (adjoinedEarPoint P.start P.finish P.internalCount i) = P.point i := by
  classical
  by_cases hzero : i.1 = 0
  · have hi : i = 0 := Fin.ext hzero
    subst i
    rfl
  · by_cases hlast : i.1 = P.internalCount + 1
    · have hi : i = Fin.last (P.internalCount + 1) := Fin.ext hlast
      subst i
      rw [adjoinedEarPoint_last]
      rfl
    · simp only [adjoinedEarPoint, dif_neg hzero, dif_neg hlast, vertexEmbed]
      apply congrArg P.point
      apply Fin.ext
      dsimp only
      omega

theorem vertexEmbed_surjective_active (P : StateFreshEar S) (v : S.current.Vertex)
    (hv : S.projection v ∈ P.newActive) :
    ∃ q : AdjoinedEarVertex S.ActiveVertex P.internalCount, P.vertexEmbed q = v := by
  classical
  by_cases hold : S.projection v ∈ S.active
  · exact ⟨Sum.inl ⟨v, hold⟩, rfl⟩
  · obtain ⟨i, hi⟩ := hv.resolve_left hold
    change S.projection (P.point i) = S.projection v at hi
    have hnot : S.projection (P.point i) ∉ S.active := by rw [hi]; exact hold
    have hzero : i.1 ≠ 0 := by
      intro h
      have hi0 : i = 0 := Fin.ext h
      exact hnot (by simpa only [hi0] using P.start_active)
    have hlast : i.1 ≠ P.internalCount + 1 := by
      intro h
      have hil : i = Fin.last (P.internalCount + 1) := Fin.ext h
      exact hnot (by simpa only [hil] using P.finish_active)
    let j : Fin P.internalCount := ⟨i.1 - 1, by omega⟩
    have hp : (⟨j.1 + 1, by omega⟩ : Fin (P.internalCount + 2)) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    refine ⟨Sum.inr j, ?_⟩
    change P.point ⟨j.1 + 1, by omega⟩ = v
    rw [hp]
    exact S.outside_fiber_unique (S.projection (P.point i)) hnot (P.point i) v rfl hi.symm

noncomputable def vertexRetract (P : StateFreshEar S) (v : S.current.Vertex) :
    AdjoinedEarVertex S.ActiveVertex P.internalCount := by
  classical
  exact if h : v ∈ Set.range P.vertexEmbed then Classical.choose h else Sum.inl S.activeInput

@[simp] theorem vertexRetract_embed (P : StateFreshEar S)
    (v : AdjoinedEarVertex S.ActiveVertex P.internalCount) :
    P.vertexRetract (P.vertexEmbed v) = v := by
  classical
  have h : P.vertexEmbed v ∈ Set.range P.vertexEmbed := ⟨v, rfl⟩
  simp only [vertexRetract, dif_pos h]
  exact P.vertexEmbed_injective (Classical.choose_spec h)

theorem vertexEmbed_retract (P : StateFreshEar S) (v : S.current.Vertex)
    (hv : S.projection v ∈ P.newActive) : P.vertexEmbed (P.vertexRetract v) = v := by
  classical
  have h : v ∈ Set.range P.vertexEmbed := P.vertexEmbed_surjective_active v hv
  have hr : P.vertexRetract v = Classical.choose h := by
    unfold vertexRetract
    rw [dif_pos h]
  rw [hr]
  exact Classical.choose_spec h

def edgeEmbed (P : StateFreshEar S) : AdjoinedEarEdge S.ActiveEdge P.internalCount → S.current.Edge
  | Sum.inl e => e.1
  | Sum.inr i => S.oldEdge (P.edge i)

theorem edgeEmbed_src (P : StateFreshEar S)
    (e : AdjoinedEarEdge S.ActiveEdge P.internalCount) :
    P.vertexEmbed (adjoinedEarSrc S.activeSrc P.start P.finish P.internalCount e) =
      S.current.src (P.edgeEmbed e) := by
  cases e with
  | inl e => rfl
  | inr i => exact (P.vertexEmbed_point i.castSucc).trans (P.source i).symm

theorem edgeEmbed_dst (P : StateFreshEar S)
    (e : AdjoinedEarEdge S.ActiveEdge P.internalCount) :
    P.vertexEmbed (adjoinedEarDst S.activeDst P.start P.finish P.internalCount e) =
      S.current.dst (P.edgeEmbed e) := by
  cases e with
  | inl e => rfl
  | inr i => exact (P.vertexEmbed_point i.succ).trans (P.target i).symm

theorem edgeEmbed_active (P : StateFreshEar S)
    (e : AdjoinedEarEdge S.ActiveEdge P.internalCount) :
    constructionActiveEdge S.current S.oldEdge P.newUsed (P.edgeEmbed e) := by
  cases e with
  | inl e =>
    rcases e.2 with haux | ⟨f, hf, hfe⟩
    · exact Or.inl haux
    · exact Or.inr ⟨f, Or.inl hf, hfe⟩
  | inr i => exact Or.inr ⟨P.edge i, Or.inr ⟨i, rfl⟩, rfl⟩

theorem edgeEmbed_surjective_active (P : StateFreshEar S) (e : S.current.Edge)
    (he : constructionActiveEdge S.current S.oldEdge P.newUsed e) :
    ∃ q : AdjoinedEarEdge S.ActiveEdge P.internalCount, P.edgeEmbed q = e := by
  rcases he with haux | ⟨f, hf, hfe⟩
  · exact ⟨Sum.inl ⟨e, Or.inl haux⟩, rfl⟩
  · rcases hf with hold | ⟨i, hi⟩
    · exact ⟨Sum.inl ⟨e, Or.inr ⟨f, hold, hfe⟩⟩, rfl⟩
    · exact ⟨Sum.inr i, (congrArg S.oldEdge hi).trans hfe⟩

end StateFreshEar
end Problem56.PaperV6
