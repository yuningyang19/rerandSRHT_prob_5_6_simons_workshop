# General probability scope preparation

Source: frozen C `main.tex`, lines 1080–1170 and 1190–1354; random-frame sampling lines 2739–2770. B is read-only.

`GeneralCumulantsExpected.lean` records six obligation propositions with ordinary real Bochner expectations on an arbitrary probability space. Its `FiniteJointMoments` requires integrability of every subset of occurrence positions. This includes the empty product, whose integrability is automatic for a probability measure. It allows repeated random variables through distinct positions and requires no higher products or exponential moment. Multilinearity asks for a linear combination of two replacements of one coordinate, assuming finite moments of the two input families. Independence concerns the two restricted random vectors, rather than pairwise independence. Symmetry uses equality in distribution with the negative variable.

No proof of these obligation propositions has been generated at this preparation checkpoint. Independent review requested from the distinct `v6_inventory` context.

## Narrow additive reuse route

The actual moment inverse in B is finite uniform, but its nonempty-index proof uses expectation only as an arbitrary scalar-valued function applied to finite products. No positivity, probability normalization, linearity, or finiteness of the sample space is used in that branch. Reuse the public finite partition combinatorics from `CumulantMoment.lean`, and generalize only the moment-dependent helper layer (product expansion, lifting block moments, global refinement sums, and final inverse) to real integrals. This proves the stronger algebraic conclusion even for a totalized integral; the public wrapper retains the paper's finite-moment and probability hypotheses.

The product formula similarly reuses the public join/connectivity partition, coarsening equivalences, and Stirling cancellation in `ProductCumulant.lean`. Its expectation-dependent helper layer needs the general inverse above plus explicit product regrouping. It cannot be closed by merely citing the old finite-uniform theorem.

Multilinearity requires integral linearity only for finite products in the two input families. Mixed independence requires factorization of finite subproducts from independence of the two random vectors, then finite partition cancellation; Mathlib `IndepFun.integral_fun_comp_mul_comp` and `IndepFun.integral_fun_mul_eq_mul_integral` are relevant. Shifts follow from deterministic-argument vanishing and multilinearity. Odd symmetry follows from equality in distribution of each finite power and scalar homogeneity. These expectation bridges remain separate proof obligations until implemented.

## Random frames

B's `fixed_size_sampling_transfer_proof` quantifies over a finite uniform auxiliary Ω. The paper permits an arbitrary independent random frame, so this is strictly narrower as encoded. A faithful route is to prove the pointwise finite-sampling failure inequality as a deterministic-frame specialization of B with unequal left and right errors combined, then integrate that inequality against an arbitrary probability law of frames. One must retain the sum of the two marginal errors: choosing a common pointwise maximum would only give twice the maximum after averaging and would not imply the stated bound from the two marginal γ assumptions. A separate independence/product-law bridge interprets this integral as the paper's marginal failure probability. No source defect has been identified by this inspection.

Independent intended-type approval received from `v6_inventory` before proof generation. Approved `GeneralCumulantsExpected.lean` SHA256: `e455d314ba827a7be386fb256a5041c54e625435c95bd44fcce49dcd5e1fc1e0`. Root's targeted elaboration of the definitions-only expected module succeeded after adding classical decidability for the connectivity predicate; mathematical types unchanged.

Development build evidence coordinated and executed serially by root:

- `GeneralCumulantsMoment.lean`: PASS; `generalMomentIdentity` has exactly `GeneralMomentIdentityExpected`.
- `GeneralCumulantsProduct.lean`: PASS; `generalProductIdentity` has exactly `GeneralProductIdentityExpected`.
- `GeneralCumulantsSymmetry.lean`: PASS; `generalOddSymmetry` has exactly `GeneralOddSymmetryExpected`.
- `GeneralCumulantsMultilinear.lean`: PASS; `generalMultilinearity` has exactly `GeneralMultilinearityExpected`.
- `GeneralCumulantsMixed.lean`: PASS; `generalMixedIndependence` has exactly `GeneralMixedIndependenceExpected`.
- `GeneralCumulantsShifts.lean`: PASS; `generalShiftInvariance` has exactly `GeneralShiftInvarianceExpected`.
- `GeneralCumulants.lean`: PASS; `generalCumulantIdentities` is the full conjunction of all six approved propositions.

Raw diagnostic/build logs include `logs/general_cumulants_development.log`, `logs/cumulants_iteration2.log`, `logs/additive_batch3.log`, `logs/additive_batch4.log`, and `logs/additive_batch6.log`. In batch 6 the generalized cumulant modules and their conjunction root passed; unrelated targets in the same batch failed, so the overall batch is not reported as PASS. These are development checks, not a substitute for the final transitive axiom audit, combined build, cold reproduction, or independent implementation correspondence review.

The mixed proof uses genuine Mathlib independence of the two random vectors; measurable multiplication of their coordinates gives independence of the two products, and `IndepFun.integral_fun_mul_eq_mul_integral` supplies expectation factorization. The connected proper-block induction from B is then adapted with integrability and independence transported to the restricted blocks. No factorization or vanishing conclusion is assumed as a new primitive hypothesis in the public target. The shift proof separately derives preservation of finite moments under constants before applying multilinearity and deterministic-group vanishing.

## Proof lineage and written-proof comparison

| C clause | Additive public declaration | Reused B proof layer | Written-proof comparison |
|---|---|---|---|
| Moment identity, 1146–1153 | `generalMomentIdentity` | `CumulantMoment.lean` public nested/global refinement equivalence and coarsening Möbius cancellation; expectation-dependent layer adapted from lines 127–142, 501–550, 613–645, 1816–1846, 1863–1929 | Valid alternative: finite Möbius cancellation instead of formal-log coefficient inversion |
| Product identity, 1154–1164 | `generalProductIdentity` | `ProductCumulant.lean` connectivity partition, common-coarsening weights, and Stirling cancellation; expectation-dependent reindexing layer generalized | Same finite refinement and common-coarsening coefficient argument, with explicit subtype bookkeeping |
| Multilinearity, 1165 | `generalMultilinearity` | Direct partition definition; no old finite probability theorem substituted | Same argument: the changed occurrence belongs to one and only one block in each summand |
| Independent groups vanish, 1165–1166 | `generalMixedIndependence` | `MixedCumulant.lean` two-family partition and connected proper-block induction; finite-coordinate factorization replaced by actual measure-theoretic independence | Valid alternative: connected-block induction rather than formal-log additivity |
| Deterministic shifts, 1167–1168 | `generalShiftInvariance` | Newly proved integrability-preserving update lemmas, generalized multilinearity and mixed vanishing | Same argument; finite-set induction makes simultaneous shifts explicit |
| Odd symmetric variable, 1168–1169 | `generalOddSymmetry` | Homogeneity pattern adapted from `JointEntryCumulant.lean` lines 40–83; `IdentDistrib.pow.integral_eq` gives genuine law invariance | Same argument: equality with the negative law plus odd homogeneity |

The formal-series descriptions in C are mathematically consistent under the finite occurrence-subset moment assumptions: each fixed coefficient contains finitely many terms. The additive proofs do not claim to kernel-verify every explanatory formal-series sentence; their alternative finite combinatorial proofs establish the exact public conclusions. No necessary manuscript repair was identified in this assigned scope.

Status: all six exact expected propositions and their conjunction root development-built. All six public proposition definitions remain byte-identical to the independently approved hash above. `GeneralCumulants.lean` assembles the six propositions as the single named lemma's full conjunction. Implementation frozen for independent actual-code review; no further Lean edits by the general-scope author after this checkpoint.

## Frozen implementation hashes

- `GeneralCumulants.lean`: `81ce23e18814626a0a0ba6eee08099ae26b5311cc225b1e7926d4fc781841c9f`
- `GeneralCumulantsExpected.lean`: `e455d314ba827a7be386fb256a5041c54e625435c95bd44fcce49dcd5e1fc1e0`
- `GeneralCumulantsMixed.lean`: `8b9830de7a2e1462e044b4fca3681a2f6572db7a7bb2a063381e6e5cf91ece3f`
- `GeneralCumulantsMoment.lean`: `c2ea73be9546f02621b5dcfd044971633fe3c895634a402c6a70f0f9f51813e8`
- `GeneralCumulantsMultilinear.lean`: `563f0651115eb0e61959c8ba341996b67bdf8260643dd93a83ae90bb05160389`
- `GeneralCumulantsProduct.lean`: `281964ca58b40f925c854077ba7cee208dc0a5c2ad18c9a36548fc769feedcde`
- `GeneralCumulantsShifts.lean`: `edadc907daa54212e0d544330ad9b9542f0e156cadcb65c23daf1edee4815cac`
- `GeneralCumulantsSymmetry.lean`: `9d4504ec73d139fea917173cd4c0e30d6fb96521e8e2f70d751284a4e7044bc9`
