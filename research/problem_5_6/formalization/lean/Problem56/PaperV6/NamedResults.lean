import Problem56.PaperV6.BinaryBridges
import Problem56.PaperV6.EntryBridges

namespace Problem56.PaperV6

/-- All independently frozen clauses of v6 `lem:binary-constraints`. -/
theorem v6_binary_constraints :
    BinaryForbiddenPairExpected ∧ BinaryCountExpected ∧ BinaryOddIncidenceExpected :=
  ⟨binary_forbidden_pair, binary_count, binary_odd_incidence⟩

/-- Both independently frozen finite-sum bounds of `prop:entry-contribution`. -/
theorem v6_entry_contribution :
    EntryWeightedCountExpected ∧ EntryAbsoluteContributionExpected :=
  ⟨entry_weighted_count, entry_absolute_contribution⟩

end Problem56.PaperV6
