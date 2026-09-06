import Problem56.PaperV6.GeneralBridgelessState

namespace Problem56.PaperV6

theorem GeneralBridgelessState.remaining_lt_of_used_subset {G : FiniteBoundaryGraph}
    (S T : GeneralBridgelessState G) (hsub : S.used ⊆ T.used)
    (hnew : ∃ e, e ∈ T.used ∧ e ∉ S.used) : T.remaining < S.remaining := by
  classical
  obtain ⟨e, heT, heS⟩ := hnew
  let f : {a : G.Edge // a ∉ T.used} → {a : G.Edge // a ∉ S.used} :=
    fun a => ⟨a.1, fun ha => a.2 (hsub ha)⟩
  unfold GeneralBridgelessState.remaining
  apply Fintype.card_lt_of_injective_of_notMem f
    (fun a b h => Subtype.ext (congrArg (fun z : {a : G.Edge // a ∉ S.used} => z.1) h))
    (b := ⟨e, heS⟩)
  rintro ⟨a, ha⟩
  apply a.2
  have hav : a.1 = e := congrArg (fun z : {a : G.Edge // a ∉ S.used} => z.1) ha
  rw [hav]
  exact heT

theorem GeneralBridgelessState.remaining_eq_zero_iff {G : FiniteBoundaryGraph}
    (S : GeneralBridgelessState G) : S.remaining = 0 ↔ ∀ e, e ∈ S.used := by
  classical
  unfold remaining
  constructor
  · intro h e
    by_contra he
    have hpos : 0 < Fintype.card {e : G.Edge // e ∉ S.used} :=
      Fintype.card_pos_iff.mpr ⟨⟨e, he⟩⟩
    omega
  · intro hall
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => e.2 (hall e.1)⟩

/-- The finite descent engine. A separately proved state-extension theorem
must supply the progress premise; this lemma is not the public conversion. -/
theorem exists_completed_state_of_strict_progress {G : FiniteBoundaryGraph}
    (hprogress : ∀ S : GeneralBridgelessState G,
      (∃ e, e ∉ S.used) → ∃ T : GeneralBridgelessState G, T.remaining < S.remaining)
    (S : GeneralBridgelessState G) :
    ∃ T : GeneralBridgelessState G, ∀ e, e ∈ T.used := by
  classical
  have h : ∀ n, ∀ T : GeneralBridgelessState G, T.remaining = n →
      ∃ U : GeneralBridgelessState G, ∀ e, e ∈ U.used := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT
      by_cases hall : ∀ e, e ∈ T.used
      · exact ⟨T, hall⟩
      · obtain ⟨e, he⟩ := Classical.not_forall.mp hall
        obtain ⟨U, hU⟩ := hprogress T ⟨e, he⟩
        exact ih U.remaining (hT ▸ hU) U rfl
  exact h S.remaining S rfl

end Problem56.PaperV6
