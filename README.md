# Rerandomized SRHT: Problem 5.6 Lean Companion

This repository contains the Lean 4 companion to the v6 manuscript on rerandomized subsampled randomized Hadamard transforms (SRHT), addressing Problem 5.6 of the Simons workshop problem collection. It includes the complete exported Lean development, supporting proofs, and evidence connecting the paper statements to their formal statements and proofs.

The current manuscript is frozen at `f279b6fac180125dce81a82d824da971bb7ae715`. Independent correspondence review covers **12/12 named results, 50/50 mathematical interfaces, and 34/34 definitions**. The certified inputs are copied byte-for-byte from development commit `93acaadec26c715917c1cf54d22781820a8a20c6`.

## Main result

For every power-of-two ambient dimension $n$, rank $1\le r\le n$, and accuracy $0<\varepsilon<1$, there is a deterministic sketch width

$$
r\le k\le \min\{n,\lceil Cr/\varepsilon^2\rceil\}
$$

for a universal constant $C\ge1$, chosen independently of the orthonormal frame $V$, such that

$$
\sup_{V^TV=I_r}\Pr\!\left(\left\|V^T\Omega_{n,k}\Omega_{n,k}^TV-I_r\right\|_2>\varepsilon\right)\le 0.01.
$$

The sampling model uses independent uniform sign layers and an independent uniform subset of $k$ coordinates sampled without replacement. For each fixed frame, the same event gives both squared-norm inequalities for every vector in its subspace, with probability at least $0.99$. The supremum is outside the probability: the statement is uniform over fixed frames, without asserting one draw works for all frames simultaneously.

The principal entry points are:

- [`Problem56.main_universal_ose`](research/problem_5_6/formalization/lean/Problem56/Statements.lean): the universal width and spectral-error guarantee.
- [`Problem56.PaperV6.fixed_frame_ose`](research/problem_5_6/formalization/lean/Problem56/PaperV6/FixedFrame.lean): the guarantee for each fixed orthonormal frame.
- [`Problem56.PaperV6.fixed_frame_squared_norm_success`](research/problem_5_6/formalization/lean/Problem56/PaperV6/FixedFrame.lean): simultaneous upper and lower squared-norm bounds within that frame.
- [`Problem56.PaperV6.Certification`](research/problem_5_6/formalization/lean/Problem56/PaperV6/Certification.lean): the complete v6 proof and expected-type import root.

See the [12-result theorem map](audit/THEOREM_MAP.md) for the supporting spectral-transfer, graph, cumulant, counting, and sampling results.

## Reproduce

Install [Lean via elan](https://github.com/leanprover/elan), Python 3, and Git. From this repository's root, run:

```bash
python3 scripts/verify_source_identity.py
python3 scripts/verify_companion.py
```

The package pins Lean **v4.33.0** and Mathlib commit **`db584cd6d46c92f209a44c0f1c829460d327499d`**. The second command creates a disposable copy, builds the local proofs, checks the current 12/50/34 manuscript mapping and transitive axiom audit, rejects invalid revision fixtures, and replays stored proof objects with `leanchecker --fresh`. It preserves historical evidence. Without an explicitly supplied dependency cache, dependencies are built from source; this can take substantial time and disk space.

For direct Lean use and the dependency-cache option, see [REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Paper-to-Lean correspondence

The current [reviewed three-way map](research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/three_way_crosswalk.md) links the frozen paper to formal statements, definitions, and proved declarations. The [machine-readable map](research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/reviewed_crosswalk.json) retains exact source anchors, type hashes, and review decisions. The [frozen TeX](research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/snapshots/research/problem_5_6/paper/v6/main.tex) is included for comparison.

The final revision makes positive coordinate dimensions explicit in Definition 3.1 and closes interface I-V6-11 using existing Lean proofs. All 96 current inventory rows pass. Older records referring to paper commit `4551d08` retain their historical I11 repair verdict; the [current certification record](research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/certification_record.json) and [independent report](research/problem_5_6/formalization/v6_certification/revisions/20260907_positive_dimensions/independent_report.md) document the updated binding.

## Certification boundary

The combined audit covers 359 targets and 134 primitive definitions. Audited theorem dependencies use only a subset of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is accepted. Lean and its installed standard kernel remain trusted. Independent review records statement correspondence and proof routes, including places where the formal proof uses a valid alternative route to the written proof.

Mathematical certification does not establish novelty, priority, citation accuracy, author comprehension, or editorial acceptance. The retained [workflow metadata limitations](research/problem_5_6/formalization/v6_certification/workflow_limitations.md) are separate from the mathematical checks. See [source binding](audit/SOURCE_BINDING.md) for exact versions and the distinction between inherited cold verification and this package's reproduction checks.
