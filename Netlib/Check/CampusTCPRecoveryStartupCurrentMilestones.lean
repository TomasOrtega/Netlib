import Netlib.Check.CampusTCPRecoveryStartupReceiptSteps
import Netlib.Check.TCPHandshakeRecoveryAdvancingOriginsFacts

/-!
# Advancing startup receipts at the current phase

Each milestone retains its actual campus delivery and service.
No later completed handshake is needed.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentMilestones

open Protocol.TCP CampusTCPModel

namespace R
export CampusTCPRecoveryStartupReceiptSteps (ActualReceipt)
end R

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive}

structure MilestoneService (report : Report input events) (stamp : Nat) (template received : EstablishedReceive.Input)
    (actor : TCPHandshakeRecovery.Side) (kind : TCPHandshakeRecovery.Kind) where
  receipt : C.Receipt
  origin : TCPHandshakeRecovery.ReceiptOrigin (report.steps.filterMap (·.result.recovery)) receipt
  actual : R.ActualReceipt report origin.actual receipt
  index : receipt.index = stamp
  templateEq : receipt.source.packet = template
  receivedEq : receipt.delivery.input = received
  actorEq : receipt.source.actor = actor
  kindEq : receipt.source.kind = kind

private def occurrenceOf : Produced active passive → Option C.Emission
  | .recovery _ occurrence _ => some occurrence
  | _ => none

theorem MilestoneService.occurrence (value : MilestoneService report stamp template received actor kind)
    (control : C.Step input.active input.passive) (occurrence : C.Emission) (present : control.result.output = some occurrence)
    (production : value.actual.delivery.receipt.served.ticket.value.produced = .recovery control occurrence present) :
    occurrence = value.receipt.source := by
  have same := production.symm.trans value.actual.delivery.production
  have selected : occurrence = value.actual.delivery.occurrence := Option.some.inj (congrArg occurrenceOf same)
  have sourceEq := value.actual.source.sourceEq
  rw [value.actual.receiptEq] at sourceEq
  exact selected.trans sourceEq.symm

theorem MilestoneService.packet (value : MilestoneService report stamp template received actor kind) :
    value.actual.delivery.receipt.served.ticket.value.source.asInput = template := by
  change value.actual.delivery.receipt.served.ticket.value.produced.output = template
  rw [value.actual.delivery.production]
  have sourceEq := value.actual.source.sourceEq
  rw [value.actual.receiptEq] at sourceEq
  change value.actual.delivery.occurrence.packet = template
  rw [← sourceEq]
  exact value.templateEq

theorem Report.milestone_service (report : Report input events) (connected : report.final.connection = .recovering current)
    (past : TCPHandshakeRecovery.AdvancingReceipt current.receipts stamp template received actor kind) :
    Nonempty (MilestoneService report stamp template received actor kind) := by
  obtain ⟨receipt, member, index, source, receivedEq, actorEq, kindEq⟩ := past
  let reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  obtain ⟨origin⟩ := reachable.receipt_origin member
  have controlMember : origin.actual ∈ report.steps.filterMap (·.result.recovery) := by
    change origin.actual ∈ reachable.steps
    have inside : origin.actual ∈ origin.prior ++ origin.actual :: origin.later :=
      List.mem_append_right _ List.mem_cons_self
    exact (congrArg (fun steps => origin.actual ∈ steps) origin.history).mpr inside
  obtain ⟨selected, bytes, path, policy, event, _, _, _⟩ :=
    TCPHandshakeRecovery.evaluate_receipt_event origin.actual.computed origin.recorded
  obtain ⟨actual⟩ := CampusTCPRecoveryStartupReceiptSteps.Report.actual_receipt report origin.actual controlMember receipt origin.recorded event
  exact ⟨⟨receipt, origin, actual, index, source, receivedEq, actorEq, kindEq⟩⟩

theorem Report.answered_syn (report : Report input events) (connected : report.final.connection = .recovering current)
    (phase : current.phase = .answered answered) :
    Nonempty (MilestoneService report answered.index answered.opened.pending.output answered.delivery.input .active .syn) := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).advancing_origins
  apply Report.milestone_service report connected
  simpa only [TCPHandshakeRecovery.AdvancingOrigins, TCPHandshakeRecovery.AnsweredMilestones, phase] using prior

theorem Report.acknowledged_syn (report : Report input events) (connected : report.final.connection = .recovering current)
    (phase : current.phase = .acknowledged acknowledged client) :
    Nonempty (MilestoneService report acknowledged.answered.index acknowledged.answered.opened.pending.output
      acknowledged.answered.delivery.input .active .syn) := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).advancing_origins
  have milestones : TCPHandshakeRecovery.AcknowledgedMilestones current.receipts acknowledged := by
    simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using prior
  exact Report.milestone_service report connected milestones.1

theorem Report.acknowledged_synAck (report : Report input events) (connected : report.final.connection = .recovering current)
    (phase : current.phase = .acknowledged acknowledged client) :
    Nonempty (MilestoneService report acknowledged.index acknowledged.answered.pending.output acknowledged.delivery.input .passive .synAck) := by
  have prior := (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).advancing_origins
  have milestones : TCPHandshakeRecovery.AcknowledgedMilestones current.receipts acknowledged := by
    simpa only [TCPHandshakeRecovery.AdvancingOrigins, phase] using prior
  exact Report.milestone_service report connected milestones.2

end Netlib.Check.CampusTCPRecoveryStartupCurrentMilestones
