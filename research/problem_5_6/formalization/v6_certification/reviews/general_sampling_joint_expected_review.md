# Independent joint sampling expected-statement review

Reviewer context: `/root/v6_inventory`, independent of proof authors. Reviewed before any joint-client proof was supplied.

Verdict: APPROVED_AS_SOURCE_SCOPE, not kernel acceptance.

Frozen expected file: `Problem56/PaperV6/GeneralSamplingJointExpected.lean`
SHA-256: `a398279d2501b7b55d3923440000fe30ce7226b851ec3dcb2ece5ffefbf896f2`

The quantifiers retain an arbitrary measurable probability space and an arbitrary measurable matrix-valued X, orthonormal almost surely. No finite-range or finite probability-space assumption is imposed on X. Sampling S has precisely the uniform k-subset marginal; Eminus and Eplus have precisely the finite product Bernoulli marginals for the manuscript theta values. Each is independent of X. Their mutual independence is absent, correctly: only two marginal Gram bounds are used in the source. The three explicit marginal equations describe sampling laws, not the desired failure conclusions. Measurability is bookkeeping rather than an extra substantive probabilistic restriction. The antecedents and conclusion retain both theta ranges, epsilon/4, and the exact 2 gamma + 2 exp(-epsilon^2 k/48) bound.

Required actual proof: instantiate the generic finite-noise law with the three exact weights, prove normalization/nonnegativity and measurable Gram events, transport both hypotheses and the conclusion to the averaged general theorem, then discharge that theorem. This review does not pre-accept that application.
