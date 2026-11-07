import Netlib.Check.CampusTCPRecoveryStartupReceiptSteps
import Netlib.Check.CampusTCPRecoveredSetup
import Netlib.Check.TCPHandshakeRecoveryAdvancingOrigins

/-!
# Stored gateway services for actual startup milestones

The source may be any retained retry occurrence. Its exact actor and kind
come from the advancing receive, and its service remains in the same report.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupMilestones

open Protocol.TCP CampusTCPModel
open CampusTCPRecoveredSetup (DrainReady)

namespace R
export CampusTCPRecoveryStartupReceiptSteps (ActualReceipt)
end R

variable {input : Input} {events : List Event} {report : Report input events} {ready : DrainReady report}

structure MilestoneService (ready : DrainReady report) (stamp : Nat) (template received : EstablishedReceive.Input)
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

theorem MilestoneService.occurrence (value : MilestoneService ready stamp template received actor kind)
    (control : C.Step input.active input.passive) (occurrence : C.Emission) (present : control.result.output = some occurrence)
    (production : value.actual.delivery.receipt.served.ticket.value.produced = .recovery control occurrence present) :
    occurrence = value.receipt.source := by
  have same := production.symm.trans value.actual.delivery.production
  have selected : occurrence = value.actual.delivery.occurrence := Option.some.inj (congrArg occurrenceOf same)
  have sourceEq := value.actual.source.sourceEq
  rw [value.actual.receiptEq] at sourceEq
  exact selected.trans sourceEq.symm

theorem MilestoneService.packet (value : MilestoneService ready stamp template received actor kind) :
    value.actual.delivery.receipt.served.ticket.value.source.asInput = template := by
  change value.actual.delivery.receipt.served.ticket.value.produced.output = template
  rw [value.actual.delivery.production]
  have sourceEq := value.actual.source.sourceEq
  rw [value.actual.receiptEq] at sourceEq
  change value.actual.delivery.occurrence.packet = template
  rw [← sourceEq]
  exact value.templateEq

theorem DrainReady.milestone_service (ready : DrainReady report)
    (past : TCPHandshakeRecovery.AdvancingReceipt ready.current.receipts stamp template received actor kind) :
    Nonempty (MilestoneService ready stamp template received actor kind) := by
  obtain ⟨receipt, member, index, source, receivedEq, actorEq, kindEq⟩ := past
  obtain ⟨origin⟩ := ready.reachable.receipt_origin member
  have controlMember : origin.actual ∈ report.steps.filterMap (·.result.recovery) := by
    change origin.actual ∈ ready.reachable.steps
    have inside : origin.actual ∈ origin.prior ++ origin.actual :: origin.later :=
      List.mem_append_right _ List.mem_cons_self
    exact (congrArg (fun steps => origin.actual ∈ steps) origin.history).mpr inside
  obtain ⟨selected, bytes, path, policy, event, _, _, _⟩ :=
    TCPHandshakeRecovery.evaluate_receipt_event origin.actual.computed origin.recorded
  obtain ⟨actual⟩ := CampusTCPRecoveryStartupReceiptSteps.Report.actual_receipt report origin.actual controlMember receipt origin.recorded event
  exact ⟨⟨receipt, origin, actual, index, source, receivedEq, actorEq, kindEq⟩⟩

end Netlib.Check.CampusTCPRecoveryStartupMilestones
