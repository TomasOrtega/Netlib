import Netlib.Protocol.EAP
import Netlib.Protocol.Transition

/-!
# Local EAP authentication guard

RFC 3748 sections 4.1 and 4.2 supply identifier and terminal correlation.
Opaque method data does not prove TLS completion or certificate validity.
Accepted external evidence must bind the selected method, expected subject, and current local round.
Outer Identity bytes are retained without assigning them an authenticated principal.
Matching Failure and trusted negative evidence close the round under the local fail-closed policy.
Resets and new conversations fail closed; this is not a complete EAP peer implementation.
-/

namespace Netlib.Protocol.EAPAuth

def sourceURL : String := "https://www.rfc-editor.org/rfc/rfc3748.html#section-4.2"

structure Context where
  subject : String
  method : UInt8 := 13
  deriving Repr, BEq, DecidableEq

def Context.MethodAllowed (context : Context) : Prop :=
  4 ≤ context.method.toNat ∧ context.method.toNat < 254

instance (context : Context) : Decidable context.MethodAllowed := by
  unfold Context.MethodAllowed
  infer_instance

structure Evidence where
  round : Nat
  subject : String
  method : UInt8
  accepted : Bool
  source : Option String := none
  deriving Repr, BEq, DecidableEq

def Evidence.ValidFor (evidence : Evidence) (context : Context) (round : Nat) : Prop :=
  evidence.round = round ∧ evidence.subject = context.subject ∧ evidence.method = context.method ∧ evidence.accepted = true

instance (evidence : Evidence) (context : Context) (round : Nat) : Decidable (evidence.ValidFor context round) := by
  unfold Evidence.ValidFor
  infer_instance

def Evidence.belongs (evidence : Evidence) (context : Context) (round : Nat) : Bool :=
  decide (evidence.round = round ∧ evidence.subject = context.subject ∧ evidence.method = context.method)

structure Message where
  identifier : UInt8
  kind : UInt8
  data : List UInt8
  deriving Repr, BEq, DecidableEq

structure State where
  round : Nat := 0
  authorized : Bool := false
  latestRequest : Option Message := none
  latestResponse : Option Message := none
  success : Option UInt8 := none
  evidence : Option Evidence := none
  outerIdentity : Option (List UInt8) := none
  deriving Repr, BEq, DecidableEq

namespace State

def initial : State := {}

def Correlated (context : Context) (state : State) : Prop :=
  match state.latestRequest, state.latestResponse, state.success with
  | some request, some response, some identifier =>
    request.identifier = response.identifier ∧ request.kind = response.kind ∧
      response.kind = context.method ∧ identifier = response.identifier
  | _, _, _ => False

def CurrentEvidence (context : Context) (state : State) : Prop :=
  match state.evidence with
  | some evidence => evidence.ValidFor context state.round
  | none => False

def Ready (context : Context) (state : State) : Prop :=
  context.MethodAllowed ∧ context.subject.isEmpty = false ∧ state.Correlated context ∧ state.CurrentEvidence context

instance (context : Context) (state : State) : Decidable (state.Ready context) := by
  unfold Ready Correlated CurrentEvidence
  split <;> split <;> infer_instance

def Safe (context : Context) (state : State) : Prop := state.authorized = true → state.Ready context

def reset (state : State) : State := { round := state.round + 1 }

def refresh (context : Context) (state : State) : State :=
  { state with authorized := decide (state.Ready context) }

theorem reset_safe (context : Context) (state : State) : (state.reset).Safe context := by
  intro impossible
  cases impossible

theorem refresh_safe (context : Context) (state : State) : (state.refresh context).Safe context := by
  intro authorized
  exact of_decide_eq_true authorized

end State

inductive Event where
  | begin
  | restart
  | start
  | logoff
  | disconnect
  | server (packet : EAP.Packet)
  | peer (packet : EAP.Packet)
  | method (evidence : Evidence)
  deriving Repr, BEq, DecidableEq

def request (context : Context) (state : State) (message : Message) : State :=
  if state.latestRequest = some message then state
  else if (state.latestRequest.map (·.identifier)) = some message.identifier then state
  else
    let methodChanged := match state.latestRequest with
      | some prior => decide (4 ≤ prior.kind.toNat ∧ prior.kind ≠ message.kind)
      | none => false
    let base := if state.success.isSome || methodChanged then state.reset else state
    ({ base with latestRequest := some message, latestResponse := none, success := none }).refresh context

def response (context : Context) (state : State) (message : Message) : State :=
  match state.latestRequest with
  | none => state
  | some outstanding =>
    if outstanding.identifier = message.identifier ∧ outstanding.kind = message.kind then
      if state.latestResponse.isSome then state
      else
        let identity := if message.kind = 1 then some message.data else state.outerIdentity
        ({ state with latestResponse := some message, success := none, outerIdentity := identity }).refresh context
    else state

def terminalSuccess (context : Context) (state : State) (identifier : UInt8) : State :=
  if state.success = some identifier then state
  else match state.latestResponse with
    | none => state
    | some last =>
      if last.identifier = identifier ∧ last.kind = context.method then
        ({ state with success := some identifier }).refresh context
      else state

def terminalFailure (state : State) (identifier : UInt8) : State :=
  match state.latestResponse with
  | some last => if last.identifier = identifier then state.reset else state
  | none => state

def methodEvidence (context : Context) (state : State) (evidence : Evidence) : State :=
  if state.evidence = some evidence then state
  else if evidence.belongs context state.round then
    if evidence.accepted then ({ state with evidence := some evidence }).refresh context else state.reset
  else state

def step (context : Context) (state : State) : Event → State
  | .begin | .restart | .start | .logoff | .disconnect => state.reset
  | .server (.request identifier kind data) => request context state ⟨identifier, kind, data⟩
  | .server (.success identifier) => terminalSuccess context state identifier
  | .server (.failure identifier) => terminalFailure state identifier
  | .server (.response ..) => state
  | .peer (.response identifier kind data) => response context state ⟨identifier, kind, data⟩
  | .peer _ => state
  | .method evidence => methodEvidence context state evidence

theorem initial_safe (context : Context) : State.initial.Safe context := by
  intro impossible
  cases impossible

theorem request_safe (context : Context) (state : State) (message : Message) (safe : state.Safe context) :
    (request context state message).Safe context := by
  unfold request
  repeat' first | exact safe | exact State.refresh_safe _ _ | split

theorem response_safe (context : Context) (state : State) (message : Message) (safe : state.Safe context) :
    (response context state message).Safe context := by
  unfold response
  repeat' first | exact safe | exact State.refresh_safe _ _ | split

theorem terminalSuccess_safe (context : Context) (state : State) (identifier : UInt8) (safe : state.Safe context) :
    (terminalSuccess context state identifier).Safe context := by
  unfold terminalSuccess
  repeat' first | exact safe | exact State.refresh_safe _ _ | split

theorem terminalFailure_safe (context : Context) (state : State) (identifier : UInt8) (safe : state.Safe context) :
    (terminalFailure state identifier).Safe context := by
  unfold terminalFailure
  repeat' first | exact safe | exact State.reset_safe _ _ | split

theorem methodEvidence_safe (context : Context) (state : State) (evidence : Evidence) (safe : state.Safe context) :
    (methodEvidence context state evidence).Safe context := by
  unfold methodEvidence
  repeat' first | exact safe | exact State.refresh_safe _ _ | exact State.reset_safe _ _ | split

theorem step_safe (context : Context) (state : State) (event : Event) (safe : state.Safe context) :
    (step context state event).Safe context := by
  cases event with
  | begin | restart | start | logoff | disconnect => exact State.reset_safe _ _
  | method evidence => exact methodEvidence_safe _ _ _ safe
  | server packet =>
    cases packet with
    | request => exact request_safe _ _ _ safe
    | response => exact safe
    | success => exact terminalSuccess_safe _ _ _ safe
    | failure => exact terminalFailure_safe _ _ _ safe
  | peer packet =>
    cases packet with
    | response => exact response_safe _ _ _ safe
    | request | success | failure => exact safe

def run (context : Context) (initial : State) (events : List Event) : State := events.foldl (step context) initial

theorem run_safe (context : Context) (initial : State) (events : List Event) (safe : initial.Safe context) :
    (run context initial events).Safe context := by
  induction events generalizing initial with
  | nil => exact safe
  | cons event events ih => exact ih _ (step_safe context initial event safe)

def transition (context : Context) : Transition State Event := Transition.ofFunction (step context)

theorem invariant (context : Context) : (transition context).Invariant (State.Safe context) := by
  intro before event after safe same
  cases same
  exact step_safe context before event safe

theorem trace_safe (context : Context) (trace : (transition context).Trace initial events final)
    (safe : initial.Safe context) : final.Safe context := (invariant context).trace safe trace

theorem authorized_evidence (context : Context) (state : State) (safe : state.Safe context)
    (authorized : state.authorized = true) :
    ∃ evidence, state.evidence = some evidence ∧ evidence.ValidFor context state.round := by
  have current := (safe authorized).2.2.2
  cases found : state.evidence with
  | none => simp [State.CurrentEvidence, found] at current
  | some evidence => exact ⟨evidence, rfl, by simpa [State.CurrentEvidence, found] using current⟩

theorem authorized_response (context : Context) (state : State) (safe : state.Safe context)
    (authorized : state.authorized = true) :
    ∃ outstanding last identifier, state.latestRequest = some outstanding ∧ state.latestResponse = some last ∧
      state.success = some identifier ∧ outstanding.identifier = last.identifier ∧ outstanding.kind = last.kind ∧
      last.kind = context.method ∧ identifier = last.identifier := by
  have correlated := (safe authorized).2.2.1
  cases requested : state.latestRequest <;> cases responded : state.latestResponse <;> cases terminal : state.success
  all_goals try simp [State.Correlated, requested, responded, terminal] at correlated
  exact ⟨_, _, _, rfl, rfl, rfl, correlated⟩

theorem authorized_not_identity (context : Context) (state : State) (safe : state.Safe context)
    (authorized : state.authorized = true) : context.method ≠ 1 := by
  have selected := (safe authorized).1
  intro same
  unfold Context.MethodAllowed at selected
  rw [same] at selected
  have impossible : ¬(4 ≤ (1 : UInt8).toNat) := by decide
  exact impossible selected.1

theorem stale_evidence_ignored (context : Context) (state : State) (evidence : Evidence)
    (stale : evidence.round ≠ state.round) : step context state (.method evidence) = state := by
  simp [step, methodEvidence, Evidence.belongs, stale]

theorem reset_unauthorized (state : State) : state.reset.authorized = false ∧ state.reset.evidence = none := ⟨rfl, rfl⟩

theorem old_evidence_after_reset (context : Context) (state : State) (evidence : Evidence)
    (oldRound : evidence.round = state.round) : (step context state.reset (.method evidence)).authorized = false := by
  have stale : evidence.round ≠ state.reset.round := by simp [State.reset, oldRound]
  rw [stale_evidence_ignored context state.reset evidence stale]
  rfl

theorem duplicate_request (context : Context) (state : State) (message : Message)
    (same : state.latestRequest = some message) : request context state message = state := by simp [request, same]

theorem duplicate_response (context : Context) (state : State) (message : Message)
    (same : state.latestResponse = some message) : response context state message = state := by
  cases found : state.latestRequest <;> simp [response, found, same]

theorem wrong_response_ignored (context : Context) (state : State) (message outstanding : Message)
    (pending : state.latestRequest = some outstanding)
    (wrong : outstanding.identifier ≠ message.identifier ∨ outstanding.kind ≠ message.kind) :
    response context state message = state := by
  rcases wrong with identifier | kind <;> simp [response, *]

theorem wrong_success_ignored (context : Context) (state : State) (identifier : UInt8) (last : Message)
    (responded : state.latestResponse = some last) (wrong : last.identifier ≠ identifier) :
    terminalSuccess context state identifier = state := by
  simp [terminalSuccess, responded, wrong]

end Netlib.Protocol.EAPAuth
