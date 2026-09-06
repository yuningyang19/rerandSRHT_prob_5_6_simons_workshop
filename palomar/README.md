# Palomar package

The public surface consists of root `Challenge.lean`, `Solution.lean`,
`comparator.json`, `formalization.yaml`, and `LICENSE` (Apache-2.0, confirmed by
the user). The complete original Lean development remains in its nested source
directory, and the root Lakefile makes it available to Palomar.

Run from the repository root:

```bash
python3 scripts/verify_palomar.py --static-only
lake exe cache get
lake build Challenge Solution
python3 scripts/verify_palomar.py
```

The first command is a cheap immutable-source and extraction check. The build
may reuse Mathlib caches. The last command elaborates the two public modules,
checks full declaration closure, and audits both proof axiom sets. Deliberate
Challenge theorem holes are expected; Solution proof dependencies must not use
`sorryAx` or any non-permitted axiom.

`.github/workflows/palomar-compatibility.yml` runs the current pinned public
Palomar verifier on Ubuntu. Its report is compatibility evidence from this
repository's own GitHub Actions runner. It does not submit to Palomar, prove
service ownership, request editorial review, or register a result. These later
service actions have separate exact-version and review-consent requirements.

The submitted-surface scope and generated auxiliary compatibility are documented
in [PUBLIC_SURFACE_AUDIT.md](PUBLIC_SURFACE_AUDIT.md). Current evidence and any
remaining action are recorded in [STATUS.md](STATUS.md).
