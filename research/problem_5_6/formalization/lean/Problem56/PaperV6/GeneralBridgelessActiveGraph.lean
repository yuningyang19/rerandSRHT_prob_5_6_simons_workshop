import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

theorem GeneralBridgelessState.active_edge_endpoints {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (e : S.current.Edge)
    (he : constructionActiveEdge S.current S.oldEdge S.used e) :
    S.projection (S.current.src e) ∈ S.active ∧
      S.projection (S.current.dst e) ∈ S.active := by
  rcases he with haux | ⟨f, hf, hfe⟩
  · exact S.auxiliary_endpoints_active e haux
  · rw [← hfe, S.source_projection, S.target_projection]
    have h := S.used_endpoints_active f hf
    cases hr : S.reversed f
    · exact h
    · exact h.symm

abbrev GeneralBridgelessState.ActiveVertex {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) := {v : S.current.Vertex // S.projection v ∈ S.active}

abbrev GeneralBridgelessState.ActiveEdge {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) :=
  {e : S.current.Edge // constructionActiveEdge S.current S.oldEdge S.used e}

def GeneralBridgelessState.activeSrc {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (e : S.ActiveEdge) : S.ActiveVertex :=
  ⟨S.current.src e.1, (S.active_edge_endpoints e.1 e.2).1⟩

def GeneralBridgelessState.activeDst {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (e : S.ActiveEdge) : S.ActiveVertex :=
  ⟨S.current.dst e.1, (S.active_edge_endpoints e.1 e.2).2⟩

def GeneralBridgelessState.activeInput {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : S.ActiveVertex :=
  ⟨S.current.input, by rw [S.input_projection]; exact S.input_active⟩

def GeneralBridgelessState.activeOutput {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : S.ActiveVertex :=
  ⟨S.current.output, by rw [S.output_projection]; exact S.output_active⟩

noncomputable def GeneralBridgelessState.activeGraph {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : FiniteBoundaryGraph := by
  classical
  exact {
    Vertex := S.ActiveVertex
    Edge := S.ActiveEdge
    vertexFintype := inferInstance
    edgeFintype := inferInstance
    vertexDecidableEq := inferInstance
    dim := fun v => S.current.dim v.1
    src := S.activeSrc
    dst := S.activeDst
    matrix := fun e => S.current.matrix e.1
    input := S.activeInput
    output := S.activeOutput }

theorem GeneralBridgelessState.active_adjacency_iff {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (a b : S.ActiveVertex) :
    directedAdjacent S.activeSrc S.activeDst a b ↔
      constructionAdjacent S.current S.oldEdge S.used a.1 b.1 := by
  constructor
  · rintro ⟨e, hs, ht⟩
    exact ⟨e.1, congrArg Subtype.val hs, congrArg Subtype.val ht, e.2⟩
  · rintro ⟨e, hs, ht, he⟩
    exact ⟨⟨e, he⟩, Subtype.ext hs, Subtype.ext ht⟩

noncomputable def GeneralBridgelessState.activeRetract {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (v : S.current.Vertex) : S.ActiveVertex := by
  classical
  exact if hv : S.projection v ∈ S.active then ⟨v, hv⟩ else S.activeInput

@[simp] theorem GeneralBridgelessState.activeRetract_coe {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (v : S.ActiveVertex) : S.activeRetract v.1 = v := by
  classical
  simp [activeRetract, v.2]

theorem GeneralBridgelessState.activeRetract_step {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) {a b : S.current.Vertex}
    (h : constructionAdjacent S.current S.oldEdge S.used a b) :
    directedAdjacent S.activeSrc S.activeDst (S.activeRetract a) (S.activeRetract b) := by
  classical
  obtain ⟨e, hs, ht, he⟩ := h
  have hends := S.active_edge_endpoints e he
  have ha : S.projection a ∈ S.active := hs ▸ hends.1
  have hb : S.projection b ∈ S.active := ht ▸ hends.2
  apply (S.active_adjacency_iff _ _).2
  simpa [activeRetract, ha, hb] using
    (show constructionAdjacent S.current S.oldEdge S.used a b from ⟨e, hs, ht, he⟩)

/-- Restrict the genuine partial DAG to its active vertex and edge types.
This supplies the finite DAG to which the local split and ear lemmas apply. -/
theorem GeneralBridgelessState.activeGraph_dag {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) :
    MingoAdmissibleDAG S.activeSrc S.activeDst S.activeInput S.activeOutput := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hcycle
    apply S.partial_acyclic v.1
    exact hcycle.lift Subtype.val (fun a b hab => (S.active_adjacency_iff a b).1 hab)
  · intro v
    rcases S.partial_from_input v.1 v.2 with heq | hpath
    · exact Or.inl (Subtype.ext heq)
    · right
      have h := hpath.lift S.activeRetract (fun _ _ hab => S.activeRetract_step hab)
      have hi : S.activeRetract S.current.input = S.activeInput :=
        S.activeRetract_coe S.activeInput
      simpa only [Function.onFun, hi, S.activeRetract_coe v] using h
  · intro v
    rcases S.partial_to_output v.1 v.2 with heq | hpath
    · exact Or.inl (Subtype.ext heq)
    · right
      have h := hpath.lift S.activeRetract (fun _ _ hab => S.activeRetract_step hab)
      have ho : S.activeRetract S.current.output = S.activeOutput :=
        S.activeRetract_coe S.activeOutput
      simpa only [Function.onFun, ho, S.activeRetract_coe v] using h

end Problem56.PaperV6
