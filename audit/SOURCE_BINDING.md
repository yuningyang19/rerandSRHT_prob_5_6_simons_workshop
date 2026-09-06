# Source binding

| Artifact | Immutable identity |
|---|---|
| Current v6 paper | `f279b6fac180125dce81a82d824da971bb7ae715` |
| Current main.tex SHA-256 | `778731145bc9f537e561579303eb644388733d485b483c90f82e62243971e8cc` |
| Development export/evidence commit | `93acaadec26c715917c1cf54d22781820a8a20c6` |
| Earlier independently cold-tested Lean source commit | `6bb96aa844c9c54dbf0d31a1cf5d4777f3fb0446` |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The development repository is `yuningyang19/rsvd_essential`. `EXPORT_MANIFEST.json` binds 601 exported inputs to the development commit. Those inputs are preserved byte-for-byte, including reviewed statements, mathematical source, dependency pins, independent reports, and historical logs. The root README, audit guides, and root verification scripts are packaging additions, outside the mathematical certification.

The current paper-binding revision reran the graph-history client and combined audit and independently closed I-V6-11. Its earlier successful cold build and kernel replay were inherited only after source and receipt revalidation; the revision did not claim a new cold build. The original cold run reused source Git objects but no compiled dependency caches. Its logs and exact execution boundary remain in the exported records.

For the public export, `scripts/verify_companion.py` rebuilds local project proofs in a separate directory and records dependency-cache reuse explicitly. Its output is package reproducibility evidence, separate from the pre-existing independent mathematical correspondence review. No theorem or proof is modified by the export.

The user authorized publication of this companion to the existing public repository. Historical records saying publication approval was not asserted describe their original operation and are retained unchanged. This export does not assert Palomar submission, registration, external endorsement, or a new manuscript-release verdict.
