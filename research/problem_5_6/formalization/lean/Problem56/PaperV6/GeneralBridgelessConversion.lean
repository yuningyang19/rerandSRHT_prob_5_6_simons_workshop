import Problem56.PaperV6.GeneralBridgelessSplitEar
import Problem56.PaperV6.GeneralBridgelessInitialState
import Problem56.PaperV6.GeneralBridgelessCompletion

namespace Problem56.PaperV6

/-- Every unfinished state admits a genuine split/reversal/ear extension.
Connectedness and deletion-connectedness are used only to select its original
ear; the construction proves the partial-DAG invariant and strict progress. -/
theorem generalBridgeless_state_progress {G : FiniteBoundaryGraph}
    (hconn : GraphConnected G.src G.dst) (hbridge : EveryEdgeDeletionConnected G.src G.dst)
    (S : GeneralBridgelessState G) (hfresh : ∃ e, e ∉ S.used) :
    ∃ T : GeneralBridgelessState G, T.remaining < S.remaining := by
  obtain ⟨P⟩ := exists_originalFreshEar S hconn hbridge hfresh
  exact P.exists_progress

/-- Published general bridgeless conversion: the prescribed distinct input
and output are retained, while a finite history of actual edge reversals and
rooted identity vertex splits yields an input-output DAG. No orientation,
ear decomposition, construction state, or operator certificate is assumed. -/
theorem generalBridgeless_modification : GeneralBridgelessModificationExpected := by
  intro G hconn hbridge hne
  obtain ⟨S⟩ := exists_initial_generalBridgelessState G hconn
  obtain ⟨T, hall⟩ := exists_completed_state_of_strict_progress
    (generalBridgeless_state_progress hconn hbridge) S
  exact T.completed_modification hconn hne hall

end Problem56.PaperV6
