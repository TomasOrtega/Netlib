import Netlib.Check.CampusDeployment
import Netlib.Theory.Queue

/-!
# Current campus policies and a wire-output FIFO

Each campus action uses the existing step at its actual embedded state.
Ordinary packets use the same stored gateway policy and tracker.
Queue service is separate from route-ticket processing.
-/

namespace Netlib.Check.CampusRevocationModel

open Packet Protocol
open StatefulFailover (Gateway)

abbrev Input := CampusDeployment.Input

structure Datagram where
  gateway : Gateway
  input : UDP.DecodedIPv4
  emission : Protocol.WireForwarding.Emission input

def Datagram.header (value : Datagram) : Header := value.emission.target
def Datagram.bytes (value : Datagram) : List UInt8 := value.emission.bytes

structure State where
  campus : CampusDeployment.State
  queue : Theory.Queue.State Datagram := {}

def State.Safe (input : Input) (state : State) : Prop := state.campus.Safe input
def State.check (input : Input) (state : State) : Bool := state.campus.check input

theorem State.check_correct (input : Input) (state : State) :
    state.check input = true ↔ state.Safe input := CampusDeployment.State.check_correct input state.campus

def Input.initial (input : Input) : State := ⟨CampusDeployment.Input.initial input, {}⟩

structure PacketCall where
  gateway : Gateway
  zone : Nat
  source : SafeHandoff.Source
  candidate : Option NetfilterNAT.Entry := none

def PacketCall.input (call : PacketCall) : Protocol.WireForwarding.Input :=
  ⟨call.zone, call.source.packet, call.candidate⟩

def State.packet (before : State) (call : PacketCall) :
    Except Protocol.WireForwarding.Error (Protocol.WireForwarding.Outcome call.source.packet) :=
  Protocol.WireForwarding.step (before.campus.deployment.handoff.configurations call.gateway).pipeline
    (before.campus.deployment.handoff.gateways.table call.gateway) call.input

def State.packetAllowed (before : State) (gateway : Gateway) : Bool :=
  !before.campus.deployment.handoff.gateways.isFenced gateway &&
    match gateway with
    | .primary => !before.campus.deployment.withdrawn
    | .standby => true

def packetState (before : CampusDeployment.State) (gateway : Gateway) (tracker : ConntrackLifecycle.State) :
    CampusDeployment.State :=
  { before with deployment := { before.deployment with handoff := { before.deployment.handoff with
    gateways := { (before.deployment.handoff.gateways.write gateway tracker) with
      epoch := before.deployment.handoff.gateways.epoch + 1 } } } }

inductive Event where
  | campus (observation : CampusDeployment.Observation)
  | packet (call : PacketCall)
  | deliver (capacity : Nat)
  | idle

inductive Payload (input : Input) (budget : Nat) (before : State) where
  | campus (observation : CampusDeployment.Observation) (result : CampusDeployment.Result input)
      (computed : CampusDeployment.step input budget before.campus observation = .ok result)
  | packet (call : PacketCall) (outcome : Protocol.WireForwarding.Outcome call.source.packet)
      (computed : before.packet call = .ok outcome)
      (certificate : SessionInstallation.Checked input.authentication input.requirements before.campus.authentication
        (before.campus.deployment.handoff.configurations call.gateway))
  | deliver (capacity : Nat)
  | idle

def campusDatagrams (result : CampusDeployment.Result input) : List Datagram :=
  match result.payload with
  | .network evidence =>
    match evidence.model.served, evidence.model.established with
    | some served, _ => (served.outcome.output.map fun emission =>
        ⟨served.ticket.value.gateway, served.ticket.value.source.packet, emission⟩).toList
    | none, some established => (established.outcome.output.map fun emission =>
        ⟨established.call.gateway, established.call.input.packet, emission⟩).toList
    | none, none => []
  | _ => []

def Payload.arrivals : Payload input budget before → List Datagram
  | .campus _ result _ => campusDatagrams result
  | .packet call outcome _ _ => (outcome.output.map fun emission =>
      ⟨call.gateway, call.source.packet, emission⟩).toList
  | .deliver _ | .idle => []

def Payload.capacity : Payload input budget before → Nat
  | .deliver capacity => capacity
  | _ => 0

def Payload.tick (payload : Payload input budget before) : Theory.Queue.Tick Datagram :=
  ⟨payload.arrivals, payload.capacity⟩

def Payload.campusState : Payload input budget before → CampusDeployment.State
  | .campus _ result _ => result.state
  | .packet call outcome _ _ => packetState before.campus call.gateway outcome.state
  | .deliver _ | .idle => before.campus

def Payload.state (payload : Payload input budget before) : State :=
  ⟨payload.campusState, Theory.Queue.advance before.queue payload.tick⟩

def Payload.event : Payload input budget before → Event
  | .campus observation _ _ => .campus observation
  | .packet call _ _ _ => .packet call
  | .deliver capacity => .deliver capacity
  | .idle => .idle

def Payload.rawPassed : Payload input budget before → Bool
  | .campus _ result _ => match result.payload with
    | .authentication evidence => evidence.finding.passed
    | .network evidence => Check.SafeHandoff.packetMatches evidence.source evidence.model &&
        Check.SafeHandoff.stateMatches evidence.source evidence.model.state
    | .withdraw _ => true
  | _ => true

def Payload.policyPassed : Payload input budget before → Option Bool
  | .campus _ result _ => some result.payload.passed
  | .packet _ _ _ certificate => some certificate.passed
  | .deliver _ | .idle => none

structure Effect (input : Input) (budget : Nat) (before : State) where
  payload : Payload input budget before
  safe : payload.state.Safe input

def Effect.state (effect : Effect input budget before) : State := effect.payload.state
def Effect.served (effect : Effect input budget before) : List Datagram :=
  (Theory.Queue.step before.queue effect.payload.tick).served

def process (input : Input) (budget : Nat) (before : State) :
    Event → Except String (Payload input budget before)
  | .campus observation => do
    match computed : CampusDeployment.step input budget before.campus observation with
    | .error reason => throw reason
    | .ok result => return .campus observation result computed
  | .packet call => do
    if !before.packetAllowed call.gateway then throw "The selected gateway has no live packet execution."
    match computed : before.packet call with
    | .error reason => throw reason.describe
    | .ok outcome =>
      let certificate ← SessionInstallation.check input.authentication input.requirements before.campus.authentication
        (before.campus.deployment.handoff.configurations call.gateway) input.handoff.configs budget
      return .packet call outcome computed certificate
  | .deliver capacity => return .deliver capacity
  | .idle => return .idle

def step (input : Input) (budget : Nat) (before : State) (event : Event) :
    Except String (Effect input budget before) := do
  if before.check input then
    let payload ← process input budget before event
    if safe : payload.state.check input = true then
      return ⟨payload, (State.check_correct _ _).mp safe⟩
    else throw "The packet changes the protected campus state."
  else throw "The campus state violates its contract."

structure Step (input : Input) (budget : Nat) where
  before : State
  event : Event
  effect : Effect input budget before
  computed : step input budget before event = .ok effect

inductive Trace (input : Input) (budget : Nat) : State → List (Step input budget) → State → Prop
  | nil (state : State) : Trace input budget state [] state
  | cons (head : Step input budget) (rest : Trace input budget head.effect.state tail final) :
      Trace input budget head.before (head :: tail) final

structure Run (input : Input) (budget : Nat) (initial : State) (events : List Event) where
  final : State
  steps : List (Step input budget)
  trace : Trace input budget initial steps final
  covered : steps.map (·.event) = events

def run (input : Input) (budget : Nat) (initial : State) :
    (events : List Event) → Except String (Run input budget initial events)
  | [] => return ⟨initial, [], .nil initial, rfl⟩
  | event :: events => do
    match computed : step input budget initial event with
    | .error reason => throw reason
    | .ok effect =>
      let rest ← run input budget effect.state events
      let head : Step input budget := ⟨initial, event, effect, computed⟩
      return ⟨rest.final, head :: rest.steps, .cons head rest.trace, by simp [head, rest.covered]⟩

abbrev Report (input : Input) (budget : Nat) (events : List Event) := Run input budget input.initial events

def check (input : Input) (events : List Event) (budget : Nat := 100000) :
    Except String (Report input budget events) := run input budget input.initial events

def Report.rawPassed (report : Report input budget events) : Bool :=
  report.steps.all (·.effect.payload.rawPassed)

end Netlib.Check.CampusRevocationModel
