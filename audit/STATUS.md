# Public companion verification: PASS

The package for paper `f279b6fac180125dce81a82d824da971bb7ae715` is published.
All 601 immutable inputs also passed byte-identity verification in a separate
clone of the public repository.

The new package verification completed at 2026-09-06T17:22:10.668317+00:00:

| Check | Result | Seconds |
|---|---|---:|
| Fresh local proof build, 8860 jobs | PASS | 702.7 |
| Graph-history expected-type client | PASS | 19.3 |
| Combined audit, 359 targets | PASS | 32.1 |
| Current paper scope, 12/50/34 | PASS | 10.3 |
| Invalid revision fixtures | PASS | 0.9 |
| Fresh kernel replay | PASS | 969.8 |

Dependency sources and compiled Mathlib dependency artifacts were explicitly
reused. No compiled Problem56 artifact was copied. This is a fresh local-proof
build and kernel replay, not an all-dependencies cold build. The earlier independent
cold verification and correspondence reviews remain separately preserved.

See the [actual execution record](package_verification/result.json) and compressed
logs in that directory. Recorded absolute paths identify the actual execution;
the published_log entries identify the preserved public copies. The source
package commit is recorded in the receipt; this documentation-only follow-up
preserves all certified inputs. No mathematical proof was changed.
