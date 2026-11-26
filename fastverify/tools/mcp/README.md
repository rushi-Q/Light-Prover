# MCP server (`tools/mcp/fastverify-mcp`)

An MCP server (JSON-RPC 2.0 over stdio; newline-delimited MCP `2025-11-25` and `Content-Length` MCP `2024-11-05` framing)
that gives an LLM-based prover or assistant the sound judge as tools: verify attempts, batches, projects and patches, check
exports, triage lemmas, look up duplicates, diff exports, mint sub-challenges, audit challenges. The tool list:
[CLI reference](../../../docs/reference/cli.md#mcp-tools-fastverify-mcp).

```json
{"mcpServers": {"fastverify": {
  "command": "<repo>/fastverify/tools/mcp/fastverify-mcp",
  "args": ["--fvserve-state", "<fvserve state>", "--fvwork-state", "<fvwork state>",
           "--challenge", "main=<challenge dir>:<PIN>:<CFG_PIN>", "--default-pset", "math",
           "--packages", "<workspace>", "--allow-root", "<workspace root>"]}}}
```

Trusted challenges are registered with `--challenge ID=DIR[:CHALLENGE_SHA256[:COMPARATOR_SHA256]]`; `--allow-root DIR`
confines every path argument. Only an ACCEPTED with a counted trust is reported as accepted. Triage and the notary check
are EXPERIMENTAL and need the server started with `--experimental` (or `FV_EXPERIMENTAL=1`).
