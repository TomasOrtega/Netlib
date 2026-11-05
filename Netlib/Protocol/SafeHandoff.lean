import Netlib.Protocol.StatefulFailover
import Netlib.Protocol.TrackedFlow
import Netlib.Theory.Outstanding
import Netlib.Protocol.WireSource

/-!
# Handoff with outstanding route assignments

Admission records the gateway selected by an endpoint route read.
Later processing uses that assignment and the gateway's current pipeline.
Route changes do not erase outstanding assignments.
Fencing requires both endpoint routes elsewhere and no outstanding assignment to the fenced gateway.
-/

namespace Netlib.Protocol.SafeHandoff

open Packet
open StatefulFailover (Gateway Leg)
namespace Work
export Netlib.Theory.Outstanding (Item State Completed newItem enqueue complete)
end Work

abbrev Source := WireSource UDP.DecodedIPv4 UDP.decodeIPv4

theorem Source.encoded (source : Source) : UDP.encodeIPv4 source.packet = .ok source.bytes :=
  UDP.encodeIPv4_decodeIPv4 _ _ source.decoded

theorem Source.valid (source : Source) : UDPRewrite.SourceValid source.packet :=
  UDPRewrite.sourceValid_of_encoded _ _ source.encoded

def leg : FlowNAT.Direction → Leg
  | .original => .client
  | .reply => .server

structure Configuration where
  id : String
  pipeline : ConntrackLifecycle.Pipeline

structure Ticket where
  gateway : Gateway
  direction : FlowNAT.Direction
  entry : NetfilterNAT.Entry
  source : Source
  selected : source.packet.header = entry.flow.input direction
  routeEpoch : Nat

structure State where
  gateways : StatefulFailover.State
  configurations : Gateway → Configuration
  binding : Option NetfilterNAT.Entry
  work : Work.State Ticket

def State.initial (primary standby : Configuration) : State :=
  ⟨StatefulFailover.State.initial, (fun gateway => match gateway with
    | .primary => primary | .standby => standby), none, {}⟩

def State.uses (state : State) (gateway : Gateway) : Bool :=
  decide (state.gateways.owners.client = gateway) || decide (state.gateways.owners.server = gateway) ||
    state.work.pending.any (fun item => decide (item.value.gateway = gateway))

def State.outstanding (state : State) (gateway : Gateway) : Nat :=
  (state.work.pending.filter (fun item => decide (item.value.gateway = gateway))).length

def State.Unfenced (state : State) : Prop :=
  (state.uses .primary = true → state.gateways.isFenced .primary = false) ∧
    (state.uses .standby = true → state.gateways.isFenced .standby = false)

def FlowSupported (entry : NetfilterNAT.Entry) : Prop :=
  entry.Compatible ∧ ConntrackReplication.Profile ⟨entry, false⟩

instance (entry : NetfilterNAT.Entry) : Decidable (FlowSupported entry) := by
  unfold FlowSupported
  infer_instance

def State.FlowSafe (state : State) (entry : NetfilterNAT.Entry) : Prop :=
  FlowSupported entry ∧ TrackedFlow.Ready state.gateways.primary entry ∧
    (∀ item ∈ state.work.pending, item.value.entry = entry) ∧
    (state.uses .standby = true → TrackedFlow.Ready state.gateways.standby entry)

def State.Safe (state : State) : Prop :=
  state.gateways.Valid ∧ state.work.Valid ∧ state.Unfenced ∧
    match state.binding with
    | none => state.work.pending = []
    | some entry => state.FlowSafe entry

private def implies (condition conclusion : Bool) : Bool := !condition || conclusion

private theorem implies_correct (condition conclusion : Bool) :
    implies condition conclusion = true ↔ (condition = true → conclusion = true) := by
  cases condition <;> cases conclusion <;> decide

def State.check (state : State) : Bool :=
  state.gateways.primary.check && state.gateways.standby.check && state.work.check &&
    implies (state.uses .primary) (!state.gateways.isFenced .primary) &&
    implies (state.uses .standby) (!state.gateways.isFenced .standby) &&
    match state.binding with
    | none => state.work.pending.isEmpty
    | some entry => decide (FlowSupported entry) && TrackedFlow.ready state.gateways.primary entry &&
      state.work.pending.all (fun item => decide (item.value.entry = entry)) &&
      implies (state.uses .standby) (TrackedFlow.ready state.gateways.standby entry)

theorem State.check_correct (state : State) : state.check = true ↔ state.Safe := by
  cases binding : state.binding <;>
    simp [State.check, State.Safe, State.Unfenced, State.FlowSafe, StatefulFailover.State.Valid,
      ConntrackLifecycle.State.check_correct, Theory.Outstanding.State.check_correct,
      implies_correct, TrackedFlow.ready_correct, List.all_eq_true, binding, and_assoc]

theorem State.Safe.flow {state : State} {entry : NetfilterNAT.Entry} (safe : state.Safe) (binding : state.binding = some entry) :
    state.FlowSafe entry := by
  simpa only [binding] using safe.2.2.2

theorem State.Safe.table_valid {state : State} (safe : state.Safe) (gateway : Gateway) :
    (state.gateways.table gateway).Valid := by
  cases gateway
  · exact safe.1.1
  · exact safe.1.2

theorem State.Safe.ready {state : State} {entry : NetfilterNAT.Entry} (safe : state.Safe) (binding : state.binding = some entry)
    (gateway : Gateway) (used : state.uses gateway = true) :
    TrackedFlow.Ready (state.gateways.table gateway) entry := by
  have flow := safe.flow binding
  cases gateway
  · exact flow.2.1
  · exact flow.2.2.2 used

theorem State.Safe.unfenced {state : State} (safe : state.Safe) (gateway : Gateway) (used : state.uses gateway = true) :
    state.gateways.isFenced gateway = false := by
  cases gateway
  · exact safe.2.2.1.1 used
  · exact safe.2.2.1.2 used

theorem State.uses_owner (state : State) (direction : FlowNAT.Direction) :
    state.uses (state.gateways.owners.get (leg direction)) = true := by
  cases direction <;> simp [State.uses, leg, StatefulFailover.Owners.get]

theorem State.uses_pending (state : State) (item : Work.Item Ticket) (member : item ∈ state.work.pending) :
    state.uses item.value.gateway = true := by
  simp only [State.uses, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨item, member, rfl⟩

theorem State.initial_safe (primary standby : Configuration) : (State.initial primary standby).Safe := by
  refine ⟨StatefulFailover.State.initial_valid, Theory.Outstanding.State.initial_valid, ?_, rfl⟩
  constructor <;> intro _ <;> rfl

structure PacketResult where
  ticket : Work.Item Ticket
  configuration : Configuration
  outcome : WireForwarding.Outcome ticket.value.source.packet

structure RawResult where
  state : State
  admitted : Option (Work.Item Ticket)
  served : Option PacketResult
  established : Option StatefulFailover.PacketResult

structure Result extends RawResult where
  safe : state.Safe

inductive Event where
  | establish (input : WireForwarding.Input)
  | stage (zone : Nat) (key : Header)
  | commit (timeout : Nat)
  | handoff (leg : Leg) (gateway : Gateway)
  | fence (gateway : Gateway)
  | forget
  | install (gateway : Gateway) (configuration : Configuration)
  | assign (direction : FlowNAT.Direction) (source : Source)
  | serve (id : Nat)

private def advance (state : State) : State :=
  { state with gateways := { state.gateways with epoch := state.gateways.epoch + 1 } }

private def control (before : State) (event : StatefulFailover.Event) : Except String RawResult := do
  let result ← StatefulFailover.step before.gateways event
  return ⟨{ before with gateways := result.state }, none, none, result.packet⟩

def core (before : State) : Event → Except String RawResult
  | .establish input => do
    if before.binding.isSome || !before.work.pending.isEmpty then
      throw "Establishment precedes protected-flow staging and outstanding admissions."
    control before (.packet ⟨.primary, .client, (before.configurations .primary).pipeline, input⟩)
  | .stage zone key => do
    let result ← StatefulFailover.step before.gateways (.stage zone key)
    let some selected := result.state.cache | throw "The source stage did not select a primary record."
    if let some binding := before.binding then
      if binding ≠ selected.record.entry then throw "A protected flow cannot be replaced by another cached binding."
    return ⟨{ before with gateways := result.state, binding := some selected.record.entry }, none, none, none⟩
  | .commit timeout => do
    let some binding := before.binding | throw "Stage the protected flow before kernel commitment."
    let some selected := before.gateways.cache | throw "The external cache has no selected source record."
    if binding ≠ selected.record.entry then throw "The cached binding differs from the protected flow."
    control before (.commit timeout)
  | .handoff selectedLeg gateway => do
    let some binding := before.binding | throw "Stage a protected flow before changing its endpoint routes."
    if !TrackedFlow.ready (before.gateways.table gateway) binding then
      throw "The target gateway has no ready protected binding."
    if before.gateways.isFenced gateway then throw "The target route owner is fenced."
    control before (.handoff selectedLeg gateway)
  | .fence gateway => do
    if before.gateways.owners.client = gateway ∨ before.gateways.owners.server = gateway then
      throw "Move both endpoint routes away before fencing a gateway."
    if before.outstanding gateway != 0 then throw "Drain the gateway's outstanding route assignments before fencing it."
    control before (.fence gateway)
  | .forget => control before .forget
  | .install gateway configuration =>
    .ok ⟨advance { before with configurations := fun selected =>
      if selected = gateway then configuration else before.configurations selected }, none, none, none⟩
  | .assign direction source => do
    let some binding := before.binding | throw "Stage the protected flow before route admission."
    if selected : source.packet.header = binding.flow.input direction then
      let gateway := before.gateways.owners.get (leg direction)
      if before.gateways.isFenced gateway then throw "The selected route owner is fenced."
      if !TrackedFlow.ready (before.gateways.table gateway) binding then
        throw "The selected route owner has no ready protected binding."
      let ticket : Ticket := ⟨gateway, direction, binding, source, selected, before.gateways.epoch⟩
      return ⟨advance { before with work := Work.enqueue before.work ticket },
        some (Work.newItem before.work ticket), none, none⟩
    else throw "The admission bytes do not identify the protected flow direction."
  | .serve id => do
    let completed ← (Work.complete before.work id).mapError (·.describe)
    let ticket := completed.item.value
    let some binding := before.binding | throw "A pending ticket has no protected flow."
    if _different : ticket.entry ≠ binding then throw "The pending ticket belongs to another protected flow."
    if before.gateways.isFenced ticket.gateway then throw "An outstanding ticket targets a fenced gateway."
    if !TrackedFlow.ready (before.gateways.table ticket.gateway) binding then
      throw "The ticket's assigned gateway has no ready protected binding."
    let configuration := before.configurations ticket.gateway
    let outcome ← (WireForwarding.step configuration.pipeline (before.gateways.table ticket.gateway)
      (TrackedFlow.wireInput ticket.entry ticket.direction ticket.source.packet)).mapError (·.describe)
    let state := { before with
      gateways := before.gateways.write ticket.gateway outcome.state
      work := completed.state }
    return ⟨advance state, none, some ⟨completed.item, configuration, outcome⟩, none⟩

def step (before : State) (event : Event) : Except String Result := do
  if _checked : before.check = true then
    let result ← core before event
    if after : result.state.check = true then
      return { result with safe := (State.check_correct _).mp after }
    else throw "The operation violates the protected-flow handoff contract."
  else throw "The handoff state violates the protected-flow contract."

theorem step_safe (before : State) (event : Event) (result : Result)
    (_accepted : step before event = .ok result) : result.state.Safe := result.safe

end Netlib.Protocol.SafeHandoff
