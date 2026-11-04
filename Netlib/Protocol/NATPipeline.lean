import Netlib.Protocol.NAT
import Netlib.Packet.ProcessorTrace

/-!
# Composable NAPT processing

The adapters retain NAT state changes even when a later filter drops the packet.
They use the local NAPT model, not native kernel semantics.
-/

namespace Netlib.Protocol.NAT

open Packet

def outboundProcessor (allocation : Endpoint) (expiresAt : Nat) (rules : Packet.ACL) : Processor State :=
  ⟨fun state packet =>
    let result := step state (.outbound packet allocation (rules.allows packet) expiresAt)
    (result.state, result.output)⟩

def inboundProcessor : Processor State := ⟨fun state packet => (state, inbound state packet)⟩

theorem outboundProcessor_safe (allocation : Endpoint) (expiresAt : Nat) (rules : Packet.ACL) :
    (outboundProcessor allocation expiresAt rules).Preserves State.Safe := by
  intro state packet safe
  exact step_safe state (.outbound packet allocation (rules.allows packet) expiresAt) safe

theorem inboundProcessor_safe : inboundProcessor.Preserves State.Safe := by
  intro state _ safe
  exact safe

theorem processor_roundtrip (state after : State) (packet wire : Header)
    (allocation : Endpoint) (expiresAt : Nat) (rules : Packet.ACL)
    (accepted : (outboundProcessor allocation expiresAt rules).run state packet = (after, some wire)) :
    inboundProcessor.run after wire.reverse = (after, some packet.reverse) := by
  have changed := congrArg Prod.fst accepted
  have output := congrArg Prod.snd accepted
  change (step state (.outbound packet allocation (rules.allows packet) expiresAt)).state = after at changed
  change (step state (.outbound packet allocation (rules.allows packet) expiresAt)).output = some wire at output
  have returned := accepted_roundtrip state packet wire allocation (rules.allows packet) expiresAt output
  rw [changed] at returned
  exact Prod.ext rfl returned

private theorem postACL_state (processor : Processor State) (rules : Packet.ACL) (state : State) (packet : Header) :
    ((processor.seq (Processor.acl rules)).run state packet).1 = (processor.run state packet).1 := by
  cases result : processor.run state packet with
  | mk next output =>
    cases output <;> simp [Processor.seq, Processor.acl, Processor.guard, result]

theorem prefilter_denied_unchanged (allocation : Endpoint) (expiresAt : Nat)
    (filter rules : Packet.ACL) (state : State) (packet : Header)
    (denied : filter.allows packet = false) :
    (((Processor.acl filter).seq (outboundProcessor allocation expiresAt rules)).run state packet) =
      (state, none) := by
  simp [Processor.seq, Processor.acl, Processor.guard, Processor.stateless, denied]

/-- A postfilter drop does not roll back the installed return-flow grant. -/
theorem postfilter_drop_keeps_reply (allocation : Endpoint) (expiresAt : Nat)
    (rules filter : Packet.ACL) (state after : State) (packet wire : Header)
    (accepted : (outboundProcessor allocation expiresAt rules).run state packet = (after, some wire))
    (denied : filter.allows wire = false) :
    ((outboundProcessor allocation expiresAt rules).seq (Processor.acl filter)).run state packet =
      (after, none) ∧ inboundProcessor.run after wire.reverse = (after, some packet.reverse) := by
  constructor
  · simp [Processor.seq, Processor.acl, Processor.guard, Processor.stateless, accepted, denied]
  · exact processor_roundtrip state after packet wire allocation expiresAt rules accepted

theorem tandem_roundtrip (left right leftAfter rightAfter : State)
    (packet middle wire : Header) (leftAlias rightAlias : Endpoint)
    (leftDeadline rightDeadline : Nat) (leftRules rightRules : Packet.ACL)
    (first : (outboundProcessor leftAlias leftDeadline leftRules).run left packet = (leftAfter, some middle))
    (second : (outboundProcessor rightAlias rightDeadline rightRules).run right middle = (rightAfter, some wire)) :
    ((inboundProcessor.liftRight).seq (inboundProcessor.liftLeft)).run
      (leftAfter, rightAfter) wire.reverse = ((leftAfter, rightAfter), some packet.reverse) := by
  have outer := processor_roundtrip right rightAfter middle wire rightAlias rightDeadline rightRules second
  have inner := processor_roundtrip left leftAfter packet middle leftAlias leftDeadline leftRules first
  simp [Processor.seq, Processor.liftLeft, Processor.liftRight, outer, inner]

inductive Direction where
  | outbound (allocation : Endpoint) (expiresAt : Nat)
  | inbound
  deriving Repr, DecidableEq

def pipeline (rules outboundFilter inboundFilter : Packet.ACL) : Direction → Processor State
  | .outbound allocation expiresAt =>
    (outboundProcessor allocation expiresAt rules).seq (Processor.acl outboundFilter)
  | .inbound => inboundProcessor.seq (Processor.acl inboundFilter)

def modelEvent (rules : Packet.ACL) (event : Processor.Observation Direction) : Event :=
  match event.kind with
  | .outbound allocation expiresAt => .outbound event.packet allocation (rules.allows event.packet) expiresAt
  | .inbound => .inbound event.packet

theorem pipeline_state (rules outboundFilter inboundFilter : Packet.ACL) (direction : Direction)
    (state : State) (packet : Header) :
    ((pipeline rules outboundFilter inboundFilter direction).run state packet).1 =
      (step state (modelEvent rules ⟨direction, packet, none⟩)).state := by
  cases direction <;> exact postACL_state _ _ _ _

def pipelineRefinement (rules outboundFilter inboundFilter : Packet.ACL) :
    TraceRefinement (Processor.transition (pipeline rules outboundFilter inboundFilter)) transition where
  project := id
  labels event := [modelEvent rules event]
  simulate before event after edge := by
    have changed := congrArg Prod.fst edge
    change ((pipeline rules outboundFilter inboundFilter event.kind).run before event.packet).1 = after at changed
    rw [pipeline_state] at changed
    exact .cons changed (.nil after)

theorem pipeline_safe (rules outboundFilter inboundFilter : Packet.ACL) :
    (Processor.transition (pipeline rules outboundFilter inboundFilter)).Invariant State.Safe :=
  (pipelineRefinement rules outboundFilter inboundFilter).invariant transition_safe

theorem pipeline_trace_state (rules outboundFilter inboundFilter : Packet.ACL)
    {before after : State} {events : List (Processor.Observation Direction)}
    (execution : (Processor.transition (pipeline rules outboundFilter inboundFilter)).Trace before events after) :
    after = run before (events.map (modelEvent rules)) := by
  have refined := (pipelineRefinement rules outboundFilter inboundFilter).trace execution
  have unique := Transition.function_trace_unique (fun state event => (step state event).state) refined
  simpa [pipelineRefinement, run, ← List.map_eq_flatMap] using unique

/-- The earlier policy-permitted packet need not have survived the postfilter. -/
theorem pipeline_reply_origin (rules outboundFilter inboundFilter : Packet.ACL)
    {after : State} {events : List (Processor.Observation Direction)}
    (execution : (Processor.transition (pipeline rules outboundFilter inboundFilter)).Trace State.initial events after)
    (packet restored : Header) (accepted : inbound after packet = some restored) :
    ∃ event ∈ events, ∃ allocation expiresAt,
      event.kind = .outbound allocation expiresAt ∧ rules.allows event.packet = true ∧
      event.packet.reverse = restored := by
  rw [pipeline_trace_state rules outboundFilter inboundFilter execution] at accepted
  obtain ⟨flow, allocation, expiresAt, origin, reverse⟩ := trace_reply_origin _ packet restored accepted
  obtain ⟨event, member, same⟩ := List.mem_map.mp origin
  cases direction : event.kind with
  | outbound selected expiry =>
    simp only [modelEvent, direction, Event.outbound.injEq] at same
    rcases same with ⟨rfl, rfl, allowed, rfl⟩
    exact ⟨event, member, selected, expiry, direction, allowed, reverse⟩
  | inbound => simp [modelEvent, direction] at same

end Netlib.Protocol.NAT
