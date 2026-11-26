# tests/compress-failure-classes — one regression test per Stage-3 failure class

After a train's keep-going build, `tools/compress/scheme/failures.py` names each failing module's first
error, `scheme/attribute.py` maps it to the owner whose edit list caused it, `scheme/edits_deny.py` drops that owner's
edits in that module for the next train - and the module re-enters only after the owner's tool has a regression test for
the failure class. This directory holds those tests (owners' tool directories are not edited here).

Layout: `<class>/run.sh [WORK]` - builds a minimal Lean repro of the failing edit pattern (no Mathlib unless the
class needs it), runs the owner's tool on it, prints `PASS ...` / `FAIL ...` rows and a final `RESULT PASS|FAIL`.
`run.sh [WORK]` runs all of them. Each test names: the train and module where the class was seen, the tool
and the sha it was fixed in, and what the test asserts (the tool refuses the edit, or produces an edit that builds).

All tools under test are untrusted producers: a test failure can only block a module's re-entry, never change a verdict.
