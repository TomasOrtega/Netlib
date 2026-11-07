import Netlib.Check.TCPHandshakeRecovery

/-!
# Actual advancing startup receipts

Milestone times identify receiver events, not canonical source occurrences.
Each witness retains its actual retry source and checked received input.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

def AdvancingReceipt (receipts : List Receipt) (stamp : Nat) (template received : H.Input) (actor : Side) (kind : Kind) : Prop :=
  ∃ actual ∈ receipts, actual.index = stamp ∧ actual.source.packet = template ∧ actual.delivery.input = received ∧
    actual.source.actor = actor ∧ actual.source.kind = kind

def AnsweredMilestones (receipts : List Receipt) (answered : O.Answered active passive) : Prop :=
  AdvancingReceipt receipts answered.index answered.opened.pending.output answered.delivery.input .active .syn

def AcknowledgedMilestones (receipts : List Receipt) (acknowledged : O.Acknowledged active passive) : Prop :=
  AnsweredMilestones receipts acknowledged.answered ∧
    AdvancingReceipt receipts acknowledged.index acknowledged.answered.pending.output acknowledged.delivery.input .passive .synAck

def CompleteMilestones (receipts : List Receipt) (complete : O.Completed active passive) : Prop :=
  AdvancingReceipt receipts complete.input.times.synReceived complete.certificate.activePending.output complete.certificate.syn.input .active .syn ∧
    AdvancingReceipt receipts complete.input.times.synAckReceived complete.certificate.passivePending.output complete.certificate.synAck.input .passive .synAck ∧
      AdvancingReceipt receipts complete.input.times.ackReceived complete.certificate.active.output complete.certificate.ack.input .active .finalAck

def AdvancingOrigins (state : State active passive) : Prop :=
  match state.phase with
  | .idle | .opened _ => True
  | .answered value => AnsweredMilestones state.receipts value
  | .acknowledged value _ => AcknowledgedMilestones state.receipts value
  | .complete value _ _ => CompleteMilestones state.receipts value

variable {active passive : H.Local}
variable {before after : State active passive} {receipts more : List Receipt}
variable {stamp : Nat} {template received : H.Input} {actor : Side} {kind : Kind}

theorem AdvancingReceipt.mono (prior : AdvancingReceipt receipts stamp template received actor kind) (retained : receipts <+: more) :
    AdvancingReceipt more stamp template received actor kind := by
  obtain ⟨actual, member, fields⟩ := prior
  exact ⟨actual, retained.subset member, fields⟩

theorem AdvancingReceipt.append (prior : AdvancingReceipt receipts stamp template received actor kind) (extra : List Receipt) :
    AdvancingReceipt (receipts ++ extra) stamp template received actor kind := prior.mono (List.prefix_append _ _)

theorem AdvancingReceipt.fresh (actual : Receipt) (same : actual.source.packet = template)
    (actorEq : actual.source.actor = actor) (kindEq : actual.source.kind = kind) :
    AdvancingReceipt (receipts ++ [actual]) actual.index template actual.delivery.input actor kind :=
  ⟨actual, List.mem_append_right _ (List.mem_singleton_self _), rfl, same, rfl, actorEq, kindEq⟩

private theorem delivery_cast_input {source target : H.Input} {spec : X.DeliverySpec}
    (delivery : X.Delivery source spec) (same : source = target) : (same ▸ delivery).input = delivery.input := by
  cases same
  rfl

theorem AdvancingReceipt.fresh_cast (actual : Receipt) (same : actual.source.packet = template)
    (actorEq : actual.source.actor = actor) (kindEq : actual.source.kind = kind) :
    AdvancingReceipt (receipts ++ [actual]) actual.index template (same ▸ actual.delivery).input actor kind := by
  rw [delivery_cast_input actual.delivery same]
  exact AdvancingReceipt.fresh actual same actorEq kindEq

theorem AnsweredMilestones.mono (prior : AnsweredMilestones receipts answered) (retained : receipts <+: more) :
    AnsweredMilestones more answered := AdvancingReceipt.mono prior retained

theorem AcknowledgedMilestones.mono (prior : AcknowledgedMilestones receipts acknowledged) (retained : receipts <+: more) :
    AcknowledgedMilestones more acknowledged := ⟨prior.1.mono retained, prior.2.mono retained⟩

theorem CompleteMilestones.mono (prior : CompleteMilestones receipts complete) (retained : receipts <+: more) :
    CompleteMilestones more complete := ⟨prior.1.mono retained, prior.2.1.mono retained, prior.2.2.mono retained⟩

theorem AdvancingOrigins.initial : AdvancingOrigins (State.initial (active := active) (passive := passive)) := trivial

theorem AdvancingOrigins.frame (prior : AdvancingOrigins before) (phase : after.phase = before.phase)
    (retained : before.receipts <+: after.receipts) : AdvancingOrigins after := by
  unfold AdvancingOrigins at prior ⊢
  rw [phase]
  cases current : before.phase with
  | idle | opened value => trivial
  | answered value => simp only [current] at prior ⊢; exact prior.mono retained
  | acknowledged value client => simp only [current] at prior ⊢; exact prior.mono retained
  | complete value client server => simp only [current] at prior ⊢; exact prior.mono retained

theorem AcknowledgedMilestones.finish (acknowledged : O.Acknowledged active passive) (index : Nat)
    (spec : X.DeliverySpec) (ack : X.Delivery acknowledged.ready.output spec)
    (ready : H.PassiveEstablished acknowledged.answered.pending ack.input)
    (computed : Handshake.synReceivedAck acknowledged.answered.pending ack.input = .ok ready)
    (ordered : acknowledged.answered.opened.index < acknowledged.answered.index ∧
      acknowledged.answered.index < acknowledged.index ∧ acknowledged.index < index)
    (prior : AcknowledgedMilestones receipts acknowledged) (retained : receipts <+: more)
    (current : AdvancingReceipt more index acknowledged.ready.output ack.input .active .finalAck) :
    CompleteMilestones more (finish acknowledged index spec ack ready computed ordered) :=
  ⟨prior.1.mono retained, prior.2.mono retained, current⟩

end Netlib.Check.TCPHandshakeRecovery
