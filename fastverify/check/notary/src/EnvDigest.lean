import Lean
import PChk.Par

/-!
`EnvDigest` — Runtime Cross-Leg Canonical Environment SHA-256 Digest.

Computes two deterministic, order-independent cryptographic SHA-256 Merkle DAG digests over
an `ExportedEnv`'s `constMap`:
  - `env_sha256_v1` (`strict := false`): 3-leg digest shared identically across `ccmp-notary`,
    `pleanchecker-notary`, and `gruszka-r7`.
  - `env_strict_sha256_v1` (`strict := true`): 2-leg digest shared across `ccmp-notary` and
    `pleanchecker-notary`, additionally binding `Expr.letE.nondep` and `Expr.mdata` wrappers.

All `ConstantInfo` constructors are unpacked by Lean's type-checked pattern matcher; the hot
iterative Merkle DAG hashing of `Name`/`Level`/`Expr` runs in `c/fv_env_digest.c` with bounded
per-worker memory and zero C recursion.
-/

namespace FV.EnvDigest
open Lean

opaque DigestCtxPointed : NonemptyType
def DigestCtx : Type := DigestCtxPointed.type
instance : Nonempty DigestCtx := DigestCtxPointed.property

@[extern "fv_sha256_selftest"]
opaque sha256SelfTest : IO Bool

@[extern "fv_digest_ctx_new"]
opaque DigestCtx.new (strict : UInt8) : IO DigestCtx

@[extern "fv_digest_hash_axiom"]
opaque DigestCtx.hashAxiom (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (isUnsafe : UInt8) : IO ByteArray

@[extern "fv_digest_hash_defn"]
opaque DigestCtx.hashDefn (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (val : @& Expr) (hintKind : UInt8) (hintHeight : UInt32) (safety : UInt8)
    (all : @& List Name) : IO ByteArray

@[extern "fv_digest_hash_thm"]
opaque DigestCtx.hashThm (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (val : @& Expr) (all : @& List Name) : IO ByteArray

@[extern "fv_digest_hash_opaque"]
opaque DigestCtx.hashOpaque (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (val : @& Expr) (isUnsafe : UInt8) (all : @& List Name) : IO ByteArray

@[extern "fv_digest_hash_quot"]
opaque DigestCtx.hashQuot (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (qkind : UInt8) : IO ByteArray

@[extern "fv_digest_hash_induct"]
opaque DigestCtx.hashInduct (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (nparams : @& Nat) (nindices : @& Nat) (all : @& List Name)
    (ctors : @& List Name) (nnested : @& Nat) (isRec isUnsafe isRefl : UInt8) : IO ByteArray

@[extern "fv_digest_hash_ctor"]
opaque DigestCtx.hashCtor (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (induct : @& Name) (cidx : @& Nat) (nparams : @& Nat) (nfields : @& Nat)
    (isUnsafe : UInt8) : IO ByteArray

@[extern "fv_digest_hash_rec_rule"]
opaque DigestCtx.hashRecRule (ctx : @& DigestCtx) (ctor : @& Name) (nfields : @& Nat)
    (rhs : @& Expr) : IO ByteArray

@[extern "fv_digest_hash_rec"]
opaque DigestCtx.hashRec (ctx : @& DigestCtx) (name : @& Name) (lparams : @& List Name)
    (ty : @& Expr) (all : @& List Name) (nparams : @& Nat) (nindices : @& Nat)
    (nmotives : @& Nat) (nminors : @& Nat) (ruleHashes : @& Array ByteArray)
    (kFlag isUnsafe : UInt8) : IO ByteArray

@[extern "fv_digest_finalize_env"]
opaque finalizeEnv (pairs : @& Array ByteArray) (strict : UInt8) : IO String

@[inline] def boolU8 (b : Bool) : UInt8 := if b then 1 else 0

/-- Canonical `DefinitionSafety` code: safe=0, unsafe=1, partial=2 (matches gruszka/susz). -/
@[inline] def safetyCode : DefinitionSafety → UInt8
  | .safe => 0
  | .unsafe => 1
  | .partial => 2

@[inline] def quotCode : QuotKind → UInt8
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind  => 3

def hashConst (ctx : DigestCtx) (ci : ConstantInfo) : IO ByteArray :=
  match ci with
  | .axiomInfo v =>
    ctx.hashAxiom v.name v.levelParams v.type (boolU8 v.isUnsafe)
  | .defnInfo v =>
    let (hk, hh) := match v.hints with
      | .opaque => ((0 : UInt8), (0 : UInt32))
      | .abbrev => ((1 : UInt8), (0 : UInt32))
      | .regular h => ((2 : UInt8), h)
    ctx.hashDefn v.name v.levelParams v.type v.value hk hh (safetyCode v.safety) v.all
  | .thmInfo v =>
    ctx.hashThm v.name v.levelParams v.type v.value v.all
  | .opaqueInfo v =>
    ctx.hashOpaque v.name v.levelParams v.type v.value (boolU8 v.isUnsafe) v.all
  | .quotInfo v =>
    ctx.hashQuot v.name v.levelParams v.type (quotCode v.kind)
  | .inductInfo v =>
    ctx.hashInduct v.name v.levelParams v.type v.numParams v.numIndices v.all v.ctors
      v.numNested (boolU8 v.isRec) (boolU8 v.isUnsafe) (boolU8 v.isReflexive)
  | .ctorInfo v =>
    ctx.hashCtor v.name v.levelParams v.type v.induct v.cidx v.numParams v.numFields (boolU8 v.isUnsafe)
  | .recInfo v => do
    let mut rhs : Array ByteArray := Array.mkEmpty v.rules.length
    for r in v.rules do
      rhs := rhs.push (← ctx.hashRecRule r.ctor r.nfields r.rhs)
    ctx.hashRec v.name v.levelParams v.type v.all v.numParams v.numIndices v.numMotives v.numMinors
      rhs (boolU8 v.k) (boolU8 v.isUnsafe)

/-- Compute one canonical environment SHA-256 digest over `cis` in parallel using `nthreads` workers. -/
def computeDigestArray (cis : Array ConstantInfo) (strict : Bool) (nthreads : Nat) : IO String := do
  unless (← sha256SelfTest) do
    throw <| IO.userError "internal error: FIPS 180-4 SHA-256 self-test failed"
  let su8 : UInt8 := if strict then 1 else 0
  let n := cis.size
  if n == 0 then
    return ← finalizeEnv #[] su8
  let nw := max 1 (min nthreads (min 64 ((n + 255) / 256)))
  if nw == 1 then
    let ctx ← DigestCtx.new su8
    let mut pairs : Array ByteArray := Array.mkEmpty n
    for ci in cis do
      pairs := pairs.push (← hashConst ctx ci)
    return ← finalizeEnv pairs su8
  let chunkSz := (n + nw - 1) / nw
  let mut tasks := Array.mkEmpty nw
  for w in [0:nw] do
    let lo := w * chunkSz
    let hi := min n (lo + chunkSz)
    if lo < hi then
      tasks := tasks.push (← IO.asTask (prio := .dedicated) do
        let ctx ← DigestCtx.new su8
        let mut out : Array ByteArray := Array.mkEmpty (hi - lo)
        for i in [lo:hi] do
          out := out.push (← hashConst ctx cis[i]!)
        return out)
  let mut allPairs : Array ByteArray := Array.mkEmpty n
  for t in tasks do
    let part ← IO.ofExcept (← IO.wait t)
    allPairs := allPairs ++ part
  finalizeEnv allPairs su8

structure EnvDigests where
  v1 : String
  strictV1 : String
  constCount : Nat
  ms : Nat

/-- Compute both `env_sha256_v1` and `env_strict_sha256_v1` over `constMap`. -/
def computeEnvDigests (constMap : Std.HashMap Name ConstantInfo) (nthreads : Nat) : IO EnvDigests := do
  let t0 ← IO.monoMsNow
  let cis := constMap.toArray.map (·.2)
  let v1 ← computeDigestArray cis false nthreads
  let strictV1 ← computeDigestArray cis true nthreads
  let ms := (← IO.monoMsNow) - t0
  return { v1, strictV1, constCount := cis.size, ms }

/-- Write the canonical digest lines atomically to `path`. -/
def writeDigestFile (path : System.FilePath) (d : EnvDigests) : IO Unit := do
  let tmp := System.FilePath.mk (path.toString ++ ".tmp")
  let content := s!"env_sha256_v1={d.v1}\nenv_strict_sha256_v1={d.strictV1}\nconst_count={d.constCount}\ndigest_ms={d.ms}\n"
  IO.FS.writeFile tmp content
  IO.FS.rename tmp path

end FV.EnvDigest
