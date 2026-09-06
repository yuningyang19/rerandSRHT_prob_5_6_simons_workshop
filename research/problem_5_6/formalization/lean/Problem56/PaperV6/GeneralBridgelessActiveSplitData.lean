import Problem56.PaperV6.GeneralBridgelessActiveGraph

namespace Problem56.PaperV6

/-- Inactive vertices have only the false copy. Active vertices have both
incoming/false and outgoing/true copies. -/
abbrev ActiveSplitCopy {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (v : S.current.Vertex) := {b : Bool // b = false ∨ S.projection v ∈ S.active}

noncomputable instance activeSplitCopyFintype {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (v : S.current.Vertex) : Fintype (ActiveSplitCopy S v) := by
  classical
  exact inferInstance

def activeSplitRoot {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G)
    (v : S.current.Vertex) : ActiveSplitCopy S v := ⟨false, Or.inl rfl⟩

/-- Routing data constrains only the already active incidences. Unused
incidences can be assigned to either available copy, which will allow a new
closed ear to have a false first endpoint and a true last endpoint. -/
structure ActiveSplitRouting {G : FiniteBoundaryGraph} (S : GeneralBridgelessState G) where
  srcCopy : ∀ e, ActiveSplitCopy S (S.current.src e)
  dstCopy : ∀ e, ActiveSplitCopy S (S.current.dst e)
  source_active : ∀ e, constructionActiveEdge S.current S.oldEdge S.used e →
    (srcCopy e).1 = true
  target_active : ∀ e, constructionActiveEdge S.current S.oldEdge S.used e →
    (dstCopy e).1 = false

noncomputable def defaultActiveSplitRouting {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : ActiveSplitRouting S := by
  classical
  exact {
    srcCopy := fun e => if he : constructionActiveEdge S.current S.oldEdge S.used e
      then ⟨true, Or.inr (S.active_edge_endpoints e he).1⟩ else activeSplitRoot S _
    dstCopy := fun e => activeSplitRoot S _
    source_active := fun e he => by simp [he]
    target_active := fun _ _ => rfl }

noncomputable def activeSplitGraph {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) : FiniteBoundaryGraph :=
  S.current.split (ActiveSplitCopy S) (activeSplitRoot S) R.srcCopy R.dstCopy
    (activeSplitRoot S S.current.input)
    ⟨true, Or.inr (by rw [S.output_projection]; exact S.output_active)⟩

def activeSplitOldEdge {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) (e : G.Edge) :
    (activeSplitGraph S R).Edge := Sum.inl (S.oldEdge e)

def activeSplitProjection {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : (activeSplitGraph S R).Vertex) : G.Vertex := S.projection v.1

theorem activeSplit_inl_active_iff {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S) (e : S.current.Edge) :
    constructionActiveEdge (activeSplitGraph S R) (activeSplitOldEdge S R) S.used
      (Sum.inl e) ↔ constructionActiveEdge S.current S.oldEdge S.used e := by
  constructor
  · rintro (hnot | ⟨f, hf, hfe⟩)
    · left
      rintro ⟨f, hf⟩
      exact hnot ⟨f, congrArg Sum.inl hf⟩
    · exact Or.inr ⟨f, hf, Sum.inl.inj hfe⟩
  · rintro (hnot | ⟨f, hf, hfe⟩)
    · left
      rintro ⟨f, hf⟩
      exact hnot ⟨f, Sum.inl.inj hf⟩
    · exact Or.inr ⟨f, hf, congrArg Sum.inl hfe⟩

theorem activeSplit_inr_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (z : ProperFiberCopy (ActiveSplitCopy S) (activeSplitRoot S)) :
    constructionActiveEdge (activeSplitGraph S R) (activeSplitOldEdge S R) S.used
      (Sum.inr z) := by
  left
  rintro ⟨e, he⟩
  change Sum.inl (S.oldEdge e) = Sum.inr z at he
  cases he

theorem activeSplit_proper_is_true {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G)
    (z : ProperFiberCopy (ActiveSplitCopy S) (activeSplitRoot S)) : z.1.2.1 = true := by
  cases hb : z.1.2.1 with
  | false =>
    exfalso
    exact z.2 (Subtype.ext hb)
  | true => rfl

theorem activeSplit_proper_is_active {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G)
    (z : ProperFiberCopy (ActiveSplitCopy S) (activeSplitRoot S)) :
    S.projection z.1.1 ∈ S.active := by
  rcases z.1.2.2 with hfalse | hactive
  · have htrue := activeSplit_proper_is_true S z
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  · exact hactive

def activeSplitEmbed {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : IncomingOutgoingVertex S.ActiveVertex) : (activeSplitGraph S R).Vertex :=
  ⟨v.1.1, ⟨v.2, Or.inr v.1.2⟩⟩

noncomputable def activeSplitRetract {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : (activeSplitGraph S R).Vertex) : IncomingOutgoingVertex S.ActiveVertex := by
  classical
  exact if hv : S.projection v.1 ∈ S.active then ⟨⟨v.1, hv⟩, v.2.1⟩
    else ⟨S.activeInput, false⟩

@[simp] theorem activeSplitRetract_embed {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : IncomingOutgoingVertex S.ActiveVertex) :
    activeSplitRetract S R (activeSplitEmbed S R v) = v := by
  classical
  rcases v with ⟨⟨v, hv⟩, side⟩
  simp [activeSplitRetract, activeSplitEmbed, hv]

theorem activeSplitEmbed_retract {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (R : ActiveSplitRouting S)
    (v : (activeSplitGraph S R).Vertex) (hv : S.projection v.1 ∈ S.active) :
    activeSplitEmbed S R (activeSplitRetract S R v) = v := by
  classical
  have hret : activeSplitRetract S R v = ⟨⟨v.1, hv⟩, v.2.1⟩ := by
    unfold activeSplitRetract
    rw [dif_pos hv]
  rw [hret]
  rcases v with ⟨v, ⟨side, hside⟩⟩
  rfl

end Problem56.PaperV6
