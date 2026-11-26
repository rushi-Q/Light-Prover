/- Challenge for cedar-spec (cedar-lean) at e7e336260332 (Lean v4.33.1, batteries v4.33.1): headline theorems of
   Cedar.Thm.Authorization, Cedar.Thm.Validation and Cedar.Thm.Typechecking, statements copied verbatim (proofs: sorry).
   The statement definitions local to the theorem files (HasSatisfiedEffect, IsExplicitlyForbidden/Permitted,
   PolicyIdsUnique, typecheck) are copied verbatim too; everything else comes from the project's own definition modules
   (copied into the challenge by tools/fetch.sh from the pinned commit). -/
import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

section Authorization
open Cedar.Data
open Cedar.Spec

def PolicyIdsUnique (policies : Policies) :=
  ∀ p₁ ∈ policies, ∀ p₂ ∈ policies, p₁.id = p₂.id → p₁ = p₂

def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Policies) : Prop :=
  ∃ (policy : Policy),
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities

def IsExplicitlyForbidden := HasSatisfiedEffect .forbid

def IsExplicitlyPermitted := HasSatisfiedEffect .permit

theorem forbid_trumps_permit
  (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyForbidden request entities policies) →
  (isAuthorized request entities policies).decision = .deny
:= sorry

theorem allowed_only_if_explicitly_permitted (request : Request) (entities : Entities) (policies : Policies) :
  (isAuthorized request entities policies).decision = .allow →
  IsExplicitlyPermitted request entities policies
:= sorry

theorem default_deny (request : Request) (entities : Entities) (policies : Policies) :
  ¬ IsExplicitlyPermitted request entities policies →
  (isAuthorized request entities policies).decision = .deny
:= sorry

theorem allowed_iff_explicitly_permitted_and_not_denied (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyPermitted request entities policies ∧ ¬ IsExplicitlyForbidden request entities policies) ↔
  (isAuthorized request entities policies).decision = .allow
:= sorry

theorem denied_iff_explicitly_denied_or_not_permitted (request: Request) (entities : Entities) (policies: Policies) :
  (IsExplicitlyForbidden request entities policies ∨ ¬ IsExplicitlyPermitted request entities policies) ↔
    (isAuthorized request entities policies).decision = .deny
  := sorry

theorem order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  isAuthorized request entities policies₁ = isAuthorized request entities policies₂
:= sorry

theorem unchanged_allow_when_add_permit (request: Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .permit →
  (isAuthorized request entities policies).decision = .allow →
  (isAuthorized request entities (policy₂ :: policies)).decision = .allow
:= sorry

theorem unchanged_deny_when_add_forbid (request : Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .forbid →
  (isAuthorized request entities policies).decision = .deny →
  (isAuthorized request entities (policy₂ :: policies)).decision = .deny
  := sorry

end Authorization

section Validation
open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  schema.validateWellFormed = .ok () →
  validate policies schema = .ok () →
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  AllEvaluateToBool policies request entities
:= sorry

end Validation

section Typechecking
open Cedar.Spec
open Cedar.Validation

def typecheck (policy : Policy) (env : TypeEnv) : Except TypeError CedarType := do
  let (ty, _) ← (typeOf policy.toExpr ∅ env).typeOf
  if ty ⊑ .bool .anyBool
  then .ok ty
  else .error (.unexpectedType ty)

theorem typecheck_is_sound (policy : Policy) (env : TypeEnv) (t : CedarType) (request : Request) (entities : Entities) :
  InstanceOfWellFormedEnvironment request entities env →
  typecheck policy env = .ok t →
  (∃ (b : Bool), EvaluatesTo policy.toExpr request entities b)
:= sorry

end Typechecking

end Cedar.Thm
