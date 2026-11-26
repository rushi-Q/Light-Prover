# `tests/kernel-cves` — Lean #16489, #15100, and #15101 Adversarial Regression Suite

Tests all trusted `fastverify` verification paths (`check-sound.sh`, `check-notary.sh`, `check-sound-lowmem.sh`, `check-frontier.sh`) against crafted NDJSON exports exercising:

1. **Lean #16489** (*`add_inductive` accepts constructor type with loose bound variable and stores a different type*, fixed in Lean PR #16512 commit `427023483c` AFTER v4.36.0):
   - `16489_safe_ctor`: `T.mk : (a : Type) → (y : #1) → T #1` (`isUnsafe=false`). Accepted & rewritten to `y : #0` by Lean 4.36's kernel, caught by `Replay.checkPostponedConstructors` and independently by `gruszka` (`type has loose bound variables`).
   - `16489_unsafe_ctor` & `16489_2param_unsafe`: Same loose-bvar constructor marked `isUnsafe=true` inside a safe inductive. **Bypasses `Replay.checkPostponedConstructors`** (`remaining` skips `isUnsafe=true` entries), so standalone v4.36 `leanchecker`, `leanchecker-paranoid`, `pleanchecker`, `pleanchecker-notary`, and official `lake comparator` (without external kernel) ALL accept (`exit 0`). **All trusted `fastverify` paths REJECT (`exit 1`)** via mandatory independent Rust second kernel `gruszka`.
2. **Lean #15100-class** (constructor/recursor checks in `Lean.Replay` / `PChk/Par.lean`):
   - `15100_unsafe_axiom_as_ctor` & `15100_unsafe_ctor_forged_meta`: Safe inductive referencing an `unsafe axiom` or an `unsafe ctor` with forged `induct`/`cidx`/`numParams`/`numFields`. Accepted by standalone v4.36 `leanchecker`, `leanchecker-paranoid`, `pleanchecker`, and official `lake comparator` (without external kernel); **REJECTED (`exit 1`) by all trusted `fastverify` paths** via `gruszka`.
3. **Lean #15101** (`Replay.lean` / `PChk/Par.lean` treats arbitrary `.quotInfo` as canonical `Quot`):
   - `15101_fake_quot_clean` & `15101_fake_quot_plus_mk`: Arbitrary `FakeQuot : ∀ p : Prop, p` (`kind="type"`) without `Quot`. Accepted by standalone v4.36 `leanchecker`, `leanchecker-paranoid`, `pleanchecker`, and official `lake comparator` (without external kernel); **REJECTED (`exit 1`) by all trusted `fastverify` paths** via `gruszka` (`quot.rs:172`).

Run:
```bash
chmod +x fastverify/tests/kernel-cves/run.sh
bash fastverify/tests/kernel-cves/run.sh
```
