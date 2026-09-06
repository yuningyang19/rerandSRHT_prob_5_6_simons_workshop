# Current revision binding

The latest paper snapshot is `f279b6fac180125dce81a82d824da971bb7ae715`.
Its positive-coordinate-dimension clarification closes I11 using unchanged Lean
proofs. The revised mathematical scope gate passes 12/12 named results, 50/50
interfaces and 34/34 definitions. Use the [revision entrypoint](revisions/20260907_positive_dimensions/README.md)
and [current status](revisions/20260907_positive_dimensions/STATUS.md).

The original companion description below retains its binding to `4551d08`.
Its source archive and historical repair verdict are not rewritten by this
revision; the new binding is recorded separately.

---

# Frozen v6 Lean companion candidate

This workspace binds the Problem 5.6 manuscript at commit
`4551d08f3732a3ca06c2f576794e1d75790e1972` to the preserved Lean development
at `40f96935796e484ab4c03865bc93b47827f99980` and additive `Problem56.PaperV6`
modules. The main result is the rerandomized-SRHT guarantee for any fixed
orthonormal frame, with a universal width bound chosen before the frame and
both simultaneous squared-norm inequalities.

Read `final_status.md` and `STATUS.md` for current completion. The exact
corrected archive at `6bb96aa844c9c54dbf0d31a1cf5d4777f3fb0446` passed its
single documented command, including a fresh full proof-object build and kernel
replay. Source Git objects were reused; compiled caches were not. The later
evidence commit records that execution without changing the tested archive.
To regenerate that exact archive, run the deterministic exporter from a detached
checkout of that commit; exporting a later evidence commit produces a different
archive. `export_candidate.json` records the tested hash. The source denominators are 12 named
results, 50 additional mathematical interfaces, and 34 definitions/notation
objects. A compiled named theorem does not close an unresolved auxiliary
interface. `three_way_crosswalk.md` gives the source-to-code routes and the
distinction between the written proof and valid alternative formal proofs.

The unchanged manuscript currently needs a dimension-scope clarification in
I-V6-11: the generic graph definition does not explicitly require positive
coordinate dimensions, while the splitting prose says an identity matrix has
norm one and the norm product is preserved. In dimension zero the identity
has norm zero. The Lean development proves entry preservation and a weak norm
inequality in all dimensions, and equality in positive dimensions. See
`required_manuscript_repairs.md`; no manuscript bytes were edited.

## Reproduce

Install the standard Lean toolchain named in the preserved `lean-toolchain`
file, plus Python 3 and Git. From the root of the exported archive or repository:

```sh
python3 research/problem_5_6/formalization/v6_certification/scripts/run_suite.py
```

The command first builds `Problem56.PaperV6.AuditTools`, then explicitly builds
`Problem56.PaperV6.Certification`, elaborates the
independently written expected-type checks, runs the old semantic witness
modules and new definition checks, runs structural guards and invalid-fixture
tests, replays stored proofs with `leanchecker --fresh`, and enforces actual
transitive axiom/dependency and source/type bindings. Every subprocess has a
raw log and actual exit code. No compiled-cache download is requested. To test
an all-dependencies cold build, run in a new directory with no `.lake` folder.
Do not remove another checkout's cache.

The explicit audit-tool build fixes a defect exposed by the c030 cold run:
the mathematical root does not import this logging module, although the later
combined audit requires it. The original failure and successful bounded
recovery remain recorded in `reproduction/`. No proof or expected type changes
are part of this entrypoint correction.

This command verifies the encoded mathematics and exact evidence bindings;
its JSON reports unresolved manuscript items separately. The additional full
paper-scope gate rejects any unresolved source repair or literal interface:

```sh
python3 research/problem_5_6/formalization/v6_certification/scripts/check_full_paper_scope.py
```

For this unchanged snapshot, that gate must fail on I-V6-11. A successful
encoded-proof reproduction is not a full manuscript certification.

`scripts/export_companion.py --output /absolute/path/companion.tar.gz` creates
a deterministic archive from committed, byte-checked inputs. It preserves the
proof-relative paths and includes `EXPORT_MANIFEST.json`. No compiled objects
or unrelated repository files enter the archive. The historical raw logs use
gzip compression; execution records contain the uncompressed log SHA256.

## Scope and trust

The allowed axioms for every audited theorem are a subset of `propext`,
`Classical.choice`, and `Quot.sound`. The installed Lean compiler/kernel and
standard toolchain are trusted; stored-proof replay uses the Lean kernel and
is not an independently implemented checker. External comparator use is not
asserted. The pinned dependency sources and their revisions are recorded.

The original 53 declarations remain a historical PROBE scope, separately
reproduced. This candidate does not assert author comprehension, originality,
publication approval, or certification of a newer manuscript. See the
independent reports, `required_manuscript_repairs.md`, and current coverage
report before interpreting any component PASS as manuscript certification.
