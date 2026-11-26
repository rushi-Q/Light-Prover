# HTTP API (`tools/http/fvapi.py`)

An HTTP front end of the attempt service [`fvserve`](../fvserve/README.md) for provers and RL pipelines, with a
Kimina-compatible batch endpoint.

```
python3 -I fastverify/tools/http/fvapi.py --fvserve-state "$ST" --default-pset math --host 127.0.0.1 --port 8080 \
    [--api-key-file FILE] [--max-concurrent N] [--max-batch N] [--request-timeout S]
```

Endpoints: `/health`, `/metrics`, `/v1/verify`, `/v1/verify/batch`, and the Kimina-style `/verify` and `/api/check`. Each
request names the theorem to judge explicitly (`theorem`, or `--custom-id-is-theorem`); a missing or unknown theorem is
NO-VERDICT. `is_pass` / `reward = 1.0` only for an ACCEPTED of the sound judge; every other outcome is 0. The server binds
to loopback by default, refuses malformed, oversized or duplicate-key JSON, bounds connections, request bodies and read
times, and supports a Bearer key. Theorem inference from the source (`--experimental-theorem-inference`) is EXPERIMENTAL
and not reward-safe ([limitations](../../../docs/limitations.md#services)). Request and reply formats:
[result.json and the API envelope](../../../docs/reference/result-json.md).
