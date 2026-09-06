# Reproducing the v6 Lean companion

Run commands from the repository root unless a directory change is shown.

## Immutable source check

```bash
python3 scripts/verify_source_identity.py
```

This checks all 601 inputs in `EXPORT_MANIFEST.json` against their SHA-256 digests and rejects additions or omissions in the exported Lean inventory. The export includes 162 Lean module files plus `lakefile.lean`, dependency pins, reviewed types, correspondence records, source snapshots, and historical receipts. The narrower `combined_source_manifest.json` has 159 inputs, including dependency configuration; its denominator is not the total number of exported Lean modules.

## Complete public-package check

```bash
python3 scripts/verify_companion.py
```

This preserves the exported files and writes execution logs and a disposable workspace beneath `.verification/`. Its six stages are:

1. Build the v6 certification root and audit tools from local source.
2. Elaborate the current graph-history expected-type client.
3. Run the 359-target combined dependency, axiom, and definition audit.
4. Check the independent revision lock and full 12/50/34 paper scope.
5. Run the revision gate's negative fixtures.
6. Replay the certification proof objects using `leanchecker --fresh`.

The script stops at the first failed command, keeps its actual exit code and log, and produces `.verification/latest_result.json`. It checks source identity again after success. Historical cold-build receipts remain historical; this script also performs a new local proof build and kernel replay.

By default the disposable directory starts without `.lake`, and compiled-cache download is disabled with `MATHLIB_NO_CACHE_ON_UPDATE=1` and `lake --no-cache`. Network access is needed to fetch pinned source dependencies. The standard installed Lean toolchain is trusted. For a faster run with an existing compatible Mathlib installation:

```bash
python3 scripts/verify_companion.py --dependency-cache /absolute/path/to/.lake/packages
```

This explicitly reuses dependency sources and compiled dependency artifacts through a directory link. No compiled `Problem56` artifacts are copied. The report records the option, so such a run is not described as an all-dependencies cold build. Use a writable compatible cache; Lake may build missing dependency artifacts there.

## Direct Lean use

```bash
cd research/problem_5_6/formalization/lean
lake exe cache get
lake build Problem56.PaperV6.AuditTools Problem56.PaperV6.Certification
lake env lean Problem56/PaperV6/CombinedAudit.lean
lake env leanchecker --fresh -v Problem56.PaperV6.Certification
```

This route explicitly downloads dependency caches. It checks Lean but does not replace the full source-correspondence gate above. Import `Problem56.PaperV6.Certification` for the complete formal surface, or `Problem56.PaperV6.FixedFrame` for the main fixed-frame results.

The original nested reproduction scripts retain historical paths and evidence bindings. In particular, the old parent `scripts/check_full_paper_scope.py` deliberately rejects the old paper snapshot's I11. The root wrapper uses the corrected revision's gate and regenerates working-directory-dependent receipts in the disposable copy. Do not rewrite historical receipts merely to make their recorded paths match a new machine.
