# Sub-challenges (`tools/subcontract/`, EXPERIMENTAL in v0.1)

Splits an open proof into pinned sub-challenges, one per open lemma, so untrusted contributors can prove them separately.
Every verdict comes from the sound judge. Every command needs `--experimental`.

```bash
S=fastverify/tools/subcontract
python3 -I $S/mint.py --experimental BLUEPRINT CHALLENGE OUT --packages "$WS" --challenge-sha256 "$PIN" --comparator-sha256 "$CFG_PIN"
python3 -I $S/triage.py OUT/manifest.json --jobs 8                     # sandboxed probes before any proving work
python3 -I $S/subverify.py --experimental OUT/manifest.json LEMMA submission.lean   # 0 accepted, 1 rejected, 2 no verdict
python3 -I $S/merge.py --experimental OUT/manifest.json OUT/verified_subproofs/*.verified.json   # re-runs the frontier check
python3 -I $S/report.py OUT --markdown
```

`mint.py` writes one sub-challenge per open lemma of the frontier, with the lemma's statement pinned. `subverify.py`
compiles a submission in a sandbox and judges it against its sub-challenge; only the source file the manifest names is
used, and paths are confined to the project. `merge.py` splices verified proofs into the parent under a lock and runs the
conditional check again (exit 3 CONDITIONAL while lemmas stay open, 0 when none remain).
