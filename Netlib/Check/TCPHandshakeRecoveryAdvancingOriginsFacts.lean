import Netlib.Check.TCPHandshakeRecoveryFacts
import Netlib.Check.TCPHandshakeRecoveryAdvancingOrigins

/-!
# Advancing receipts from the actual startup trace

The milestones retain the actual receive steps and their earlier retry sources.
Source occurrence indices remain distinct from canonical milestone times.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {before final : State active passive} {actual : Step active passive}
variable {events : List Event} {steps : List (Step active passive)} {receipt : Receipt}
variable {stamp : Nat} {template received : H.Input} {actor : Side} {kind : Kind}

theorem AdvancingOrigins.step (prior : AdvancingOrigins actual.before) : AdvancingOrigins actual.result.state :=
  evaluate_advancing_origins prior actual.computed

theorem Trace.advancing_origins (trace : Trace before events steps final) (prior : AdvancingOrigins before) :
    AdvancingOrigins final := by
  induction trace with
  | done => exact prior
  | next actual tail ih => exact ih prior.step

theorem Reachable.advancing_origins (reachable : Reachable final) : AdvancingOrigins final :=
  reachable.trace.advancing_origins AdvancingOrigins.initial

theorem Step.receipt_event (recorded : actual.result.receipt = some receipt) :
    ∃ source bytes path policy, actual.event = .receive source bytes path policy ∧
      actual.before.source source = some receipt.source ∧ receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes :=
  evaluate_receipt_event actual.computed recorded

theorem ReceiptOrigin.event (origin : ReceiptOrigin steps receipt) :
    ∃ source bytes path policy, origin.actual.event = .receive source bytes path policy ∧
      origin.actual.before.source source = some receipt.source ∧ receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes :=
  origin.actual.receipt_event origin.recorded

structure AdvancingReceiptOrigin (steps : List (Step active passive)) (stamp : Nat) (template received : H.Input) (actor : Side) (kind : Kind) where
  receipt : Receipt
  origin : ReceiptOrigin steps receipt
  index : receipt.index = stamp
  templateEq : receipt.source.packet = template
  received : receipt.delivery.input = received
  actorEq : receipt.source.actor = actor
  kindEq : receipt.source.kind = kind

theorem AdvancingReceipt.origin (reachable : Reachable final)
    (milestone : AdvancingReceipt final.receipts stamp template received actor kind) :
    Nonempty (AdvancingReceiptOrigin reachable.steps stamp template received actor kind) := by
  obtain ⟨receipt, member, index, templateEq, input, actorEq, kindEq⟩ := milestone
  obtain ⟨origin⟩ := reachable.receipt_origin member
  exact ⟨⟨receipt, origin, index, templateEq, input, actorEq, kindEq⟩⟩

theorem AdvancingReceiptOrigin.actual_member (value : AdvancingReceiptOrigin steps stamp template received actor kind) :
    value.origin.actual ∈ steps := by
  exact (congrArg (fun current => value.origin.actual ∈ current) value.origin.history).mpr
    (List.mem_append_right _ List.mem_cons_self)

theorem AdvancingReceiptOrigin.actual_index (value : AdvancingReceiptOrigin steps stamp template received actor kind) :
    value.origin.actual.index = stamp := value.origin.index.symm.trans value.index

theorem AdvancingReceiptOrigin.source_earlier (value : AdvancingReceiptOrigin steps stamp template received actor kind) :
    value.origin.producer.index < stamp := by
  exact lt_of_lt_of_eq value.origin.source_earlier value.actual_index

theorem AdvancingReceiptOrigin.event (value : AdvancingReceiptOrigin steps stamp template received actor kind) :
    ∃ source path policy, value.origin.actual.event = .receive source received.bytes path policy ∧
      value.origin.actual.before.source source = some value.receipt.source ∧ value.receipt.source.index = source := by
  obtain ⟨source, bytes, path, policy, event, selected, index, raw⟩ := value.origin.event
  rw [value.received] at raw
  rw [← raw] at event
  exact ⟨source, path, policy, event, selected, index⟩

structure CompleteAdvancingOrigins (steps : List (Step active passive)) (complete : O.Completed active passive) where
  syn : AdvancingReceiptOrigin steps complete.input.times.synReceived complete.certificate.activePending.output complete.certificate.syn.input .active .syn
  synAck : AdvancingReceiptOrigin steps complete.input.times.synAckReceived complete.certificate.passivePending.output complete.certificate.synAck.input .passive .synAck
  ack : AdvancingReceiptOrigin steps complete.input.times.ackReceived complete.certificate.active.output complete.certificate.ack.input .active .finalAck

theorem Reachable.complete_advancing_origins (reachable : Reachable final) {complete : O.Completed active passive}
    {client : PreData complete.certificate.activeSeed} {server : PreData complete.certificate.passiveSeed}
    (phase : final.phase = .complete complete client server) : Nonempty (CompleteAdvancingOrigins reachable.steps complete) := by
  have milestones : CompleteMilestones final.receipts complete := by
    simpa only [AdvancingOrigins, phase] using reachable.advancing_origins
  obtain ⟨syn⟩ := AdvancingReceipt.origin reachable milestones.1
  obtain ⟨synAck⟩ := AdvancingReceipt.origin reachable milestones.2.1
  obtain ⟨ack⟩ := AdvancingReceipt.origin reachable milestones.2.2
  exact ⟨⟨syn, synAck, ack⟩⟩

end Netlib.Check.TCPHandshakeRecovery
