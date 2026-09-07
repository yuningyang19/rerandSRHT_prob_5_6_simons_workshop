# Palomar packaging status

PACKAGE is complete. The prepared submission candidate is
`158a716c07e16ec4fca14e36836b14d8d20ee7c8`. This status and its reports are recorded in a later
documentation-only commit; that later commit is not the CI-tested candidate.

- Immutable certified inputs: 601/601 PASS, unchanged.
- Current formalization.yaml parser and v0.4 schema: PASS.
- Local Challenge and Solution elaboration: PASS.
- Declaration closure: 11,960 declarations identical; 61,548 proof dependencies.
- Two public theorem axiom audits: PASS, only the three permitted axioms.
- Pinned Linux Comparator: PASS; solution build completed with 8,784 jobs.
- Lean default kernel and independent NanoDa kernel: both accepted the solution.
- Challenge provenance: PASS; no untrusted sources.
- Mechanical report: complete/pass, no report-level errors or warnings.
- GitHub Actions terminal result: success.
- Service submission: accepted as `99q9xdqita2v`; official mechanical verification PASS.
- Editorial review: complete and retrieved privately; contents are not published here.
- Registration: exact-review consent given; request accepted, publication pending.

[Compatibility run](https://github.com/yuningyang19/rerandSRHT_prob_5_6_simons_workshop/actions/runs/34049757010) completed at 2026-09-06T18:04:07Z.
The original [mechanical report](compatibility_evidence/mechanical-report.json),
[GitHub run](compatibility_evidence/github-run.json), and
[receipt](compatibility_evidence/receipt.json) are retained here.
Mathlib caches were reused. Ordinary Lean linter messages remain in the build
log; they are distinct from report-level warnings.

The verification used the pinned public Palomar pipeline on this repository's
own Ubuntu runner. The report's `pkg260907002` identifier is a local workflow
request identifier, not a Palomar service submission ID.

## Prepared service submission

- Repository: `yuningyang19/rerandSRHT_prob_5_6_simons_workshop`
- Commit: `158a716c07e16ec4fca14e36836b14d8d20ee7c8`
- Comparator configuration: `comparator.json`
- Relationship: `maintainer` (Yuning Yang, previously confirmed)

The user agreed to this exact tuple and intake was accepted at 2026-09-06T23:24:10Z.
Both temporary ownership artifacts were deleted.
[Official verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34066787391) completed successfully;
this is distinct from the completed own-repository compatibility run above.
See [submission_receipt.json](submission_receipt.json). The complete review was shown and its exact digest authorized.
Registration was requested; public record and preservation checks are pending.

See [operation.json](operation.json), [return.json](return.json), and
[policy_snapshot.json](policy_snapshot.json). No mathematical scope, novelty,
manuscript-readiness, or research release status is promoted by this package.

Official [mechanical report](official_evidence/mechanical-report.json) and
[receipt](official_evidence/receipt.json) confirm PASS for the submitted SHA.

Submission `99q9xdqita2v` is now `review-ready`. The complete review and
its digest were retrieved privately for the user. The user subsequently authorized registration of that exact review.
The request returned HTTP 200; terminal registration is not yet claimed.
