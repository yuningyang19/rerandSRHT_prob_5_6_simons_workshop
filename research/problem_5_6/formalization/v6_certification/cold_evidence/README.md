# Captured execution evidence

These are byte-preserved execution receipts and deterministically compressed
raw logs from `packages/cold-c0303801ca01-shallow`. `capture_manifest.json`
records the tested c030 archive/source identity, original directory and hashes.
The original raw logs remain in that local cold directory. No compiled objects
are included here.

Receipt working directories and source paths describe the actual execution;
they have not been rewritten to make copied historical evidence appear newly
executed elsewhere. Each compressed log decompresses to the receipt's exact
`log_sha256`. To reproduce the mathematics in another directory, use the
documented suite in a fresh unpacked source archive.

The independent completion report in `reproduction/` separately checks all
current receipts, protected input bytes, actual target types and dependencies,
and the full-paper scope rejection. Consult `final_status.json` for the final
scope and execution outcome.
