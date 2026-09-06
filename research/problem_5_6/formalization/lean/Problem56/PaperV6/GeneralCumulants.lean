import Problem56.PaperV6.GeneralCumulantsMoment
import Problem56.PaperV6.GeneralCumulantsProduct
import Problem56.PaperV6.GeneralCumulantsSymmetry
import Problem56.PaperV6.GeneralCumulantsShifts

/-! All conjuncts of frozen v6 `lem:cumulant-identities`. -/
namespace Problem56.PaperV6

theorem generalCumulantIdentities :
    GeneralMomentIdentityExpected ∧ GeneralProductIdentityExpected ∧
    GeneralMultilinearityExpected ∧ GeneralMixedIndependenceExpected ∧
    GeneralShiftInvarianceExpected ∧ GeneralOddSymmetryExpected :=
  ⟨generalMomentIdentity, generalProductIdentity, generalMultilinearity,
    generalMixedIndependence, generalShiftInvariance, generalOddSymmetry⟩

end Problem56.PaperV6
