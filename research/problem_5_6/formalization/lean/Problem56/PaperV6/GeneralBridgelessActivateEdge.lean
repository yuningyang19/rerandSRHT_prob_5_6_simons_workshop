import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

theorem constructionAdjacent_mono {H : FiniteBoundaryGraph} {ε : Type}
    (oldEdge : ε → H.Edge) {used used' : Set ε} (hsub : used ⊆ used') :
    constructionAdjacent H oldEdge used ≤ constructionAdjacent H oldEdge used' := by
  rintro a b ⟨e, hs, ht, he⟩
  refine ⟨e, hs, ht, ?_⟩
  rcases he with hnot | ⟨f, hf, hfe⟩
  · exact Or.inl hnot
  · exact Or.inr ⟨f, hsub hf, hfe⟩

theorem transGen_rank_lt_of_rel {α : Type*} {R : α → α → Prop}
    (rank : α → ℕ) (hstep : ∀ a b, R a b → rank a < rank b)
    {a b : α} (h : Relation.TransGen R a b) : rank a < rank b := by
  induction h with
  | single hab => exact hstep _ _ hab
  | tail hp hab ih => exact ih.trans (hstep _ _ hab)

/-- Add one already correctly oriented original edge whose two original
endpoints are active. Strict rank increase is the local, checkable insertion
condition; the updated full DAG is not a hypothesis. The full graph and its
finite modification history do not change in this activation step. -/
def GeneralBridgelessState.activateEdge {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (e : G.Edge)
    (hends : G.src e ∈ S.active ∧ G.dst e ∈ S.active)
    (rank : S.current.Vertex → ℕ)
    (hrank : ∀ a b, constructionAdjacent S.current S.oldEdge S.used a b →
      rank a < rank b)
    (hedge : rank (S.current.src (S.oldEdge e)) <
      rank (S.current.dst (S.oldEdge e))) : GeneralBridgelessState G := by
  have hmono : constructionAdjacent S.current S.oldEdge S.used ≤
      constructionAdjacent S.current S.oldEdge (insert e S.used) :=
    constructionAdjacent_mono S.oldEdge (Set.subset_insert e S.used)
  have hnewrank : ∀ a b,
      constructionAdjacent S.current S.oldEdge (insert e S.used) a b → rank a < rank b := by
    rintro a b ⟨f, hs, ht, hf⟩
    rcases hf with hnot | ⟨g, hg, hgf⟩
    · exact hrank a b ⟨f, hs, ht, Or.inl hnot⟩
    · rcases Set.mem_insert_iff.mp hg with rfl | hg
      · rw [← hgf] at hs ht
        simpa only [hs, ht] using hedge
      · exact hrank a b ⟨f, hs, ht, Or.inr ⟨g, hg, hgf⟩⟩
  refine { S with
    used := insert e S.used
    used_endpoints_active := ?_
    partial_acyclic := ?_
    partial_from_input := ?_
    partial_to_output := ?_ }
  · intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact hends
    · exact S.used_endpoints_active f hf
  · intro v hcycle
    exact (Nat.lt_irrefl _) (transGen_rank_lt_of_rel rank hnewrank hcycle)
  · intro v hv
    rcases S.partial_from_input v hv with heq | hpath
    · exact Or.inl heq
    · exact Or.inr (Relation.TransGen.mono hmono _ _ hpath)
  · intro v hv
    rcases S.partial_to_output v hv with heq | hpath
    · exact Or.inl heq
    · exact Or.inr (Relation.TransGen.mono hmono _ _ hpath)

theorem GeneralBridgelessState.activateEdge_remaining_lt {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) (e : G.Edge) (hfresh : e ∉ S.used)
    (hends : G.src e ∈ S.active ∧ G.dst e ∈ S.active)
    (rank : S.current.Vertex → ℕ)
    (hrank : ∀ a b, constructionAdjacent S.current S.oldEdge S.used a b →
      rank a < rank b)
    (hedge : rank (S.current.src (S.oldEdge e)) <
      rank (S.current.dst (S.oldEdge e))) :
    (S.activateEdge e hends rank hrank hedge).remaining < S.remaining := by
  classical
  let f : {a : G.Edge // a ∉ insert e S.used} → {a : G.Edge // a ∉ S.used} :=
    fun a => ⟨a.1, fun ha => a.2 (Set.mem_insert_of_mem e ha)⟩
  dsimp only [remaining, activateEdge]
  simp only [← Nat.card_eq_fintype_card]
  change Nat.card {a : G.Edge // a ∉ insert e S.used} <
    Nat.card {a : G.Edge // a ∉ S.used}
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_of_notMem f
    (fun a b h => Subtype.ext
      (congrArg (fun z : {a : G.Edge // a ∉ S.used} => z.1) h)) (b := ⟨e, hfresh⟩)
  rintro ⟨a, ha⟩
  apply a.2
  have hav : a.1 = e := congrArg (fun z : {a : G.Edge // a ∉ S.used} => z.1) ha
  rw [hav]
  exact Set.mem_insert e S.used

end Problem56.PaperV6
