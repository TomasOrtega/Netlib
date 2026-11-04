import Netlib.Security.ZeroTrust

/-!
# Session guards

A session records identity checks, a credential, and a clock.
Each request uses the current state.
Time changes and credential changes clear the previous admission.
The identity and integrity results are supplied observations.
-/

namespace Netlib.Protocol

structure Scope where
  resource : String
  operation : String
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure Context where
  consumer : String
  producer : String
  issuer : String
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure Credential where
  issuer : String
  subject : String
  audience : String
  scopes : List Scope
  expiresAt : Nat
  integrity : Bool
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

structure Session where
  authenticated : Bool := false
  credential : Option Credential := none
  now : Nat := 0
  admitted : Option Scope := none
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

namespace Session

def initial : Session := {}

/-- The credential must match its issuer, subject, audience, scope, and clock. -/
def claims (context : Context) (state : Session) (scope : Scope) : Bool :=
  match state.credential with
  | none => false
  | some token =>
    token.integrity && decide (token.issuer = context.issuer) &&
    decide (token.subject = context.consumer) && decide (token.audience = context.producer) &&
    decide (scope ∈ token.scopes) && decide (state.now < token.expiresAt)

def permits (context : Context) (state : Session) (scope : Scope) : Bool :=
  state.authenticated && claims context state scope

/-- These conditions give the independent meaning of a valid credential. -/
def Valid (context : Context) (state : Session) (scope : Scope) : Prop :=
  state.authenticated = true ∧ ∃ token, state.credential = some token ∧
    token.integrity = true ∧ token.issuer = context.issuer ∧
    token.subject = context.consumer ∧ token.audience = context.producer ∧
    scope ∈ token.scopes ∧ state.now < token.expiresAt

theorem permits_iff (context : Context) (state : Session) (scope : Scope) :
    permits context state scope = true ↔ Valid context state scope := by
  cases token : state.credential <;> simp [permits, claims, Valid, token, and_assoc]

/-- Every recorded admission satisfies the current session guard. -/
def Safe (context : Context) (state : Session) : Prop :=
  ∀ scope, state.admitted = some scope → state.permits context scope = true

theorem initial_safe (context : Context) : Safe context initial := by
  simp [Safe, initial]

end Session

inductive Event where
  | authenticate (success : Bool)
  | install (credential : Credential)
  | advance (now : Nat)
  | request (scope : Scope)
  | revoke
  | close
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

namespace Session

/-- Local revocation clears a credential. It is separate from each standards profile. -/
def step (context : Context) (state : Session) : Event → Session
  | .authenticate success => { state with authenticated := success, credential := none, admitted := none }
  | .install token => { state with credential := some token, admitted := none }
  | .advance now => { state with now := max state.now now, admitted := none }
  | .request scope => { state with admitted := if permits context state scope then some scope else none }
  | .revoke => { state with credential := none, admitted := none }
  | .close => { state with authenticated := false, credential := none, admitted := none }

theorem step_safe (context : Context) (state : Session) (event : Event) :
    Safe context (step context state event) := by
  cases event with
  | authenticate success => simp [Safe, step]
  | install token => simp [Safe, step]
  | advance now => simp [Safe, step]
  | revoke => simp [Safe, step]
  | close => simp [Safe, step]
  | request requested =>
    intro scope accepted
    cases guard : permits context state requested with
    | false => simp [step, guard] at accepted
    | true =>
      have same : requested = scope := by simpa [step, guard] using accepted
      subst scope
      simpa [step, permits, claims] using guard

def run (context : Context) (state : Session) (events : List Event) : Session :=
  events.foldl (step context) state

theorem run_safe (context : Context) (state : Session) (events : List Event)
    (safe : Safe context state) : Safe context (run context state events) := by
  induction events generalizing state with
  | nil => exact safe
  | cons event events ih =>
    exact ih (step context state event) (step_safe context state event)

theorem admitted_valid (context : Context) (state : Session) (events : List Event)
    (safe : Safe context state) (scope : Scope)
    (accepted : (run context state events).admitted = some scope) :
    Valid context (run context state events) scope :=
  (permits_iff _ _ _).mp (run_safe context state events safe scope accepted)

theorem clock_mono (context : Context) (state : Session) (event : Event) :
    state.now ≤ (step context state event).now := by
  cases event <;> simp [step, Nat.le_max_left]

theorem expired_denied (context : Context) (state : Session) (scope : Scope)
    (token : Credential) (installed : state.credential = some token)
    (expired : token.expiresAt ≤ state.now) : permits context state scope = false := by
  simp [permits, claims, installed, Nat.not_lt.mpr expired]

theorem revoked_denied (context : Context) (state : Session) (scope : Scope) :
    permits context (step context state .revoke) scope = false := by
  simp [permits, claims, step]

theorem closed_denied (context : Context) (state : Session) (scope : Scope) :
    permits context (step context state .close) scope = false := by
  simp [permits, step]

/-- A valid token can serve more than one request during its validity period. -/
theorem request_preserves_guard (context : Context) (state : Session)
    (first second : Scope) :
    permits context (step context state (.request first)) second = permits context state second := rfl

/-- This policy connects session guards to the existing request enforcement model. -/
def policy (context : Context) (state : Session) : ZeroTrust.Policy String String String where
  authenticated principal := decide (principal = context.consumer) && state.authenticated
  authorized request := claims context state ⟨request.resource, request.operation⟩

theorem policy_allows (context : Context) (state : Session) (scope : Scope) :
    (policy context state).allows ⟨context.consumer, scope.resource, scope.operation⟩ =
      permits context state scope := by
  simp [policy, ZeroTrust.Policy.allows, permits]

end Session
end Netlib.Protocol
