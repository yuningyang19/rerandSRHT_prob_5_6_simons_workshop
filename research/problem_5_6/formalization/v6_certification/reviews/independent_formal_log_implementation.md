# Independent formal-log implementation review

Reviewer `/root/baseline_audit`, separate from the proof authors. **The prior literal I-V6-14 coefficient gap is closed at source implementation level.** The six reviewed files and all five expected propositions are bound in `formal_log_scope_preparation.md` and the companion JSON. Final combined kernel/axiom and clean replay binding is still pending.

The definitions encode actual subset convolution and recursive powers; the log and exp coefficients use their ordinary signed reciprocal and reciprocal-factorial coefficients, with finite truncation justified by zero constant term. The desired cumulant or inverse identity is not an input field, axiom or disguised coefficient definition. The same scalar, probability and finite-moment scope as C is retained.

`FormalLogBasic` proves vanishing above the subset cardinality by power induction and supplies the probability-normalized empty coefficients. `FormalLogPartitions` constructs a bijection between a distinguished nonempty subset plus a partition of its complement, and a partition with one distinguished block. `FormalLogPowers` uses this bijection to derive the factor j+1 in a convolution step and then j! by induction. Thus the ordered-partition multiplicity is an actual theorem about the convolution powers.

`FormalLogCoefficients` proves the logarithm coefficient formula, including the nonzero-j factorial arithmetic and the zero/nonempty cases. It also proves the exponential coefficient partition expansion from powers divided by factorials. Its ambient/subtype partition equivalence matches cumulants of repeated random variables indexed by distinct occurrence positions. `FormalLogInverse` transports the already proved general moment-cumulant identity to ambient subsets, then proves exp(log moment)=moment using the actual log and exp coefficient expansions.

That last dependency is not circular: the general moment identity was independently proved earlier by partition cancellation, and its imports do not depend on FormalLog. The current proof establishes the literal coefficient assertions without rewriting the earlier theorem provenance to claim it was originally proved from formal logarithms. C can present the standard coefficient route; its mathematical claims now have explicit coefficient proof evidence.

The finite squarefree quotient faithfully retains the ordinary formal coefficients used by C, because nonsquarefree monomials cannot contribute to squarefree products. No claim is made that an infinite multivariate formal-series datatype, analytic moment-generating function or unrestricted analytic inverse theorem was formalized. In particular, the unconditional finite definition squarefreeExp_empty is interpreted as the formal exponential coefficient only at a zero-constant input; the actual log input proves that condition.

The source receipt `inverse_selection_noties_iteration6.execution.json` binds all six reviewed file hashes, and its raw log records successful FormalLogPowers, FormalLogCoefficients and FormalLogInverse builds. The overall command returned **1** because two separate ContinuousCoupling targets failed. The report therefore records successful FormalLog module compilation, not a successful combined command.

Five explicit reviewer-owned source-type assignments plus the conjunction assignment are in `ExpectedFormalLogChecks.lean`. They supply existing theorem terms only. The iteration9 raw log records this module built successfully and its source hash matches the execution receipt. That combined command failed on unrelated GeneralBridgelessOriginalEar; final import-closure/replay binding is still pending.

## Reverse tests

- Deletion: actual convolution, block selection bijection and factorial multiplicity are necessary additions; deleting them restores the old literal-coefficient gap.
- Object identity: subset coefficients represent occurrence monomials; moment normalization, empty log coefficient and real integral moments match C.
- Route substitution: literal coefficient identities are proved; the inverse statement transparently reuses the previous independent partition-cancellation result.
- Endpoint: zero power, empty S, nonempty cumulant subsets, powers above card(S), nonzero denominator j and factorial, and probability normalization are all retained.

No mathematical defect or necessary manuscript correction was identified in this delta. Status is `LITERAL_COEFFICIENT_IMPLEMENTATION_ACCEPTED_FINAL_KERNEL_BINDING_PENDING`, not final manuscript certification. After integration, literal interface accounting can add I-V6-14 back without changing the frozen 50-item denominator.

## Final binding update

The final 359-target / 134-definition / 63,329-node audit and complete 159-file source manifest are now independently checked and bound in the JSON companion. Main ExpectedChecks and all four imported independent check modules compiled successfully in `combined_integration_final`. This closes the earlier component-binding pending status. The separate frozen-source I-V6-11 dimension-scope repair remains explicit; whole-manuscript coverage is not established.
