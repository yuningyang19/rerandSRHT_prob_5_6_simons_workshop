# Positive-coordinate-dimension revision

This layer binds the unchanged Problem 5.6 Lean development to paper commit
`f279b6fac180125dce81a82d824da971bb7ae715`. The source delta is exactly one
clarification in Definition 3.1: coordinate dimensions are positive integers.
The existing positive-dimension branches of the graph modification proofs then
cover I-V6-11. See [STATUS.md](STATUS.md) for the completed result.

## Check this binding

From the certification repository root in the recorded workspace:

```sh
python3 research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/check_full_paper_scope.py
```

This command validates the independent revision lock, exact paper delta,
all source anchors, unchanged Lean sources and expected types, the current
combined audit, the current graph-history client receipt, and all seven
inherited cold-check receipts. It then applies the original fail-closed
full-paper coverage condition to the newly reviewed map. Expected result:
12/12 named results, 50/50 interfaces, 34/34 definitions, no unresolved items.
The old parent gate still targets `4551d08` and retains its I11 rejection.

The current audit receipts identify their actual original working directory.
On another checkout, first build the unchanged sources using the preserved
pinned toolchain/dependency files, then generate actual receipts for that
checkout. From `research/problem_5_6/formalization/lean/`:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake --no-cache build Problem56.PaperV6.AuditTools Problem56.PaperV6.Certification
```

From this revision directory:

```sh
python3 run_logged.py current_graph_history_client lake env lean Problem56/PaperV6/ExpectedGraphHistoryChecks.lean
python3 run_logged.py current_combined_audit lake env lean Problem56/PaperV6/CombinedAudit.lean
python3 check_full_paper_scope.py
python3 test_revision_gate.py
```

Each logged command preserves its real exit code, working directory, source
hashes and output. The historical cold receipts remain unchanged: their original
cwd is checked against the independently recorded cold directory, their logs
and receipt bytes against the capture manifest, and every source hash against
the current proof tree. The old cold directory need not remain on disk.
No new cold build or fresh kernel replay is claimed for this revision; their
successful prior results are explicitly inherited under exact proof identity.
The installed Lean toolchain/kernel is trusted as before.

## Evidence

- `paper_delta.patch`, `frozen_C_manifest.json`, `snapshots/`: exact new source.
- `reviewed_crosswalk.json` and `three_way_crosswalk.md`: all 96 source rows.
- `independent_report.json/md`, `reviewed_revision_lock.json`: separate review.
- `logs/`: current type/audit execution and final scope/negative-test results;
  compressed logs preserve their raw hashes.
- `certification_record.json`: final combined record and controller acceptance.
- `tex_validation.json`, `tex_build/`: compiled PDF, numbering and page-11 check.
- `history/`: exact prior metadata and actual gate receipts before an enum-only
  contract clarification; mathematical bytes and accepted mapping did not change.

The parent `6bb96aa` companion archive retains its original paper binding.
This directory is the new binding layer; the older archive is not relabeled.
The original workflow metadata limitations remain separate, and this operation
does not assert author comprehension or public-release approval.
