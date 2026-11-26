# CI gate (`tools/ci-action/`, EXPERIMENTAL in v0.1)

A pull-request gate: `fv ci` and the GitHub composite action (`action.yml`) run `fv-ci.sh`, which verifies the submitted
tree with a cold sound run and writes a verdict, SARIF and a Markdown summary. It runs only with `--experimental` (action
input `experimental: "true"`, or `FV_EXPERIMENTAL_CI=1`).

```yaml
- uses: ./fastverify/tools/ci-action
  with:
    experimental: "true"
    project: .
    challenge: challenge
    challenge-sha256: ${{ vars.FV_CHALLENGE_SHA256 }}
    comparator-sha256: ${{ vars.FV_COMPARATOR_SHA256 }}
    # outside the checkout: an output directory inside the judged project is refused
    out-dir: ${{ runner.temp }}/fv-out
```

Other inputs: `packages`, `preset`, `pins`, `closure-only`, `confirm-reject`, `frontier` (with `allowed-frontier`,
`frontier-axioms`, `frontier-pinned`), `threads`, `wall-limit`, `mem-limit`, `commit-sha`. Outputs: `verdict`, `accepted`,
`trust`, `exit-code`, `wall-seconds`, `result-json`, `sarif-file`, `summary-markdown`. In v0.1 `cache-dir` is ignored (every
run is cold) and `disk-limit` has no effect. Count no verdict as a failure, and do not run untrusted fork pull requests on
persistent shared self-hosted runners. Known limitations: [limitations](../../../docs/limitations.md#services).
