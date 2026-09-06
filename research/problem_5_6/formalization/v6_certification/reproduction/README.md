# Final corrected-package reproduction

The final archive is `packages/frozen-v6-companion-6bb96aa.tar.gz`, from
`6bb96aa844c9c54dbf0d31a1cf5d4777f3fb0446`, SHA256
`9e4dcf6c813914bf4d98f23a2fdf54d408ef71b811cedd169b4cd1c5b8fa12a7`.
The unchanged documented `run_suite.py` passed in one invocation, with no
recovery after suite start. Its AuditTools prerequisite, all seven mandatory
checks, combined audit, and independent completion audit passed. The full-paper
scope gate independently exited 1 solely on I-V6-11.

Read `independent_final_source_cold_completion_6bb96aa-final.md` or the matching
JSON report for commands, times, hashes, and results. Verbatim receipts and
compressed logs are in `../cold_evidence_final/`; their original working-directory
and timestamp fields are preserved. The capture manifest verifies both raw and
compressed log hashes. This evidence belongs to the exact archive above;
subsequent report/documentation commits do not replace its identity.

All project/dependency proof objects were newly compiled. The final run started
with zero compiled objects and reused only exact source Git objects from the
previously verified official-source repositories after two preserved transport
failures. No compiled cache or build directory was copied. Source-object reuse
is explicit; this is not an unqualified cache-free run. The standard installed
Lean toolchain is trusted. The failure and recovery history below is retained.

# Historical c030 source archive execution

The mathematical archive is `packages/frozen-v6-companion-c0303801.tar.gz`,
bound to commit `c0303801ca01e9507a27ef4a47236807c9e39ab7` with SHA256
`15b07372fcf0e146347c447ec2aed1db0782f7a37499bd97037273460c41cfb6`.
Paths here are relative to the parent certification evidence directory.
The source archive is unchanged by later evidence or correspondence wording
commits. Its repeated deterministic export has the same hash.

Two attempts to acquire dependencies through Lake's full Git clone failed in
the network transfer, before Lean compilation. Their actual results are
`reproduction/independent_cold_export_c0303801.json` and
`reproduction/independent_cold_export_c0303801_http11.json`, with compressed
raw logs beside them. Neither attempt is labeled successful.

The independent reviewer then unpacked the same archive into a third, absent
directory, `packages/cold-c0303801ca01-shallow`. The source recovery runner used
official Git remotes and shallow fetches of each exact revision in the pinned
Lake manifest. It verified all nine detached HEADs and clean tracked sources.
The initial archive and the directory immediately before compilation both
contained zero compiled objects. No objects or dependency directories were
copied from earlier attempts or another checkout.

After this explicit source-acquisition recovery, the unchanged documented
command was actually invoked from the fresh unpacked root:

```sh
python3 research/problem_5_6/formalization/v6_certification/scripts/run_suite.py
```

`independent_source_recovery_runner.py` records the actual recovery harness;
`independent_source_cold_recovery_c0303801.json` and its raw log record the
commands, working directories, source acquisition and suite execution. The
completion audit is a separate inspection of the real finished run, including
the additional full-paper scope gate. Consult the completion report and
`final_status.json` for the result; a running record is not a build pass.

The trust boundary includes the standard installed Lean 4.33.0 distribution,
the operating system and hardware. Project and dependency proof objects are
rebuilt from source. Stored-proof replay uses Lean's kernel; it does not claim
an independently implemented logic checker.

The cold directory retains the exact c030 correspondence metadata. The later
I-V6-11 wording clarification is separately recorded in
`reviews/i11_implication_metadata_clarification.json`; it changes no proof,
expected type, primitive definition, checker or source manifest. Both metadata
versions retain I-V6-11 as an unresolved literal manuscript interface. The
source archive, its independent cold execution and the later metadata audit
must be read with these distinct hashes.

The original c030 suite subsequently failed after all seven mandatory checks:
`CombinedAudit.lean` could not import the unbuilt `AuditTools.olean`. Its source
was then explicitly compiled and the recovered audit passed. The original
single-command result remains FAIL. The main entrypoint has since been repaired
to build this logger first; a different, exact corrected archive requires its
own fresh test. See `independent_source_cold_completion_c0303801.json` for the
completed c030 recovery and the parent `final_status.json` for the final package.
