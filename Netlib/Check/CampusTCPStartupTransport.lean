import Netlib.Check.CampusTCPStartupOrigins
import Netlib.Check.CampusTCPStartupAlignment
import Netlib.Check.CampusTCPPrimaryTransport

/-!
# Startup transport from the actual three gateway services

The past profile selects the three stored services through the primary gateway.
Their stored effects determine each preceding transport state.
-/

namespace Netlib.Check.CampusTCPStartupTransport

open Protocol CampusTCPModel
namespace F
export CampusTCPFacts (StartupHistory DeliveryAt GatewayService)
end F
namespace P
export CampusTCPPrimaryTransport (afterService serviceTransport)
end P

variable {input : Input} {report : CampusTCPModel.Report input events}
variable {complete : TCPHandshake.Completed input.active input.passive}

structure CleanServices (history : F.StartupHistory report complete) : Prop where
  records : report.steps.filterMap (·.result.service) =
    [history.syn.receive.receipt.served, history.synAck.receive.receipt.served, history.ack.receive.receipt.served]
  synPrimary : history.syn.receive.receipt.served.ticket.value.gateway = .primary
  synAckPrimary : history.synAck.receive.receipt.served.ticket.value.gateway = .primary
  ackPrimary : history.ack.receive.receipt.served.ticket.value.gateway = .primary

private theorem prefix_positions (prior later : List α) (a b c selected : α)
    (split : prior ++ selected :: later = [a, b, c]) :
    (selected = a ∧ prior = []) ∨ (selected = b ∧ prior = [a]) ∨
      (selected = c ∧ prior = [a, b]) := by
  cases prior with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at split
    exact .inl ⟨split.1, rfl⟩
  | cons x rest =>
    cases rest with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
      exact .inr (.inl ⟨split.2.1, by rw [split.1]⟩)
    | cons y rest =>
      cases rest with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
        exact .inr (.inr ⟨split.2.2.1, by rw [split.1, split.2.1]⟩)
      | cons z rest =>
        have lengths := congrArg List.length split
        simp only [List.length_append, List.length_cons, List.length_nil] at lengths
        omega

private theorem service_before (delivery : F.DeliveryAt report time actor) (service : F.GatewayService delivery)
    (primary : delivery.receipt.served.ticket.value.gateway = .primary) :
    ∃ prior later, report.steps.filterMap (·.result.service) = prior ++ delivery.receipt.served :: later ∧
      (⟨delivery.receipt.served.before.tracker, delivery.receipt.served.before.admission⟩ : TCP.Checkpoint.Gateway) =
        P.serviceTransport .initial prior := by
  obtain ⟨prior, later, records, before⟩ :=
    CampusTCPPrimaryTransport.Report.before_service report service.joint.step service.joint.member
      delivery.receipt.served service.present
  refine ⟨prior, later, records, ?_⟩
  rw [service.before, primary]
  exact before

private theorem distinct_services (history : F.StartupHistory report complete) :
    history.syn.receive.receipt.served ≠ history.synAck.receive.receipt.served ∧
      history.syn.receive.receipt.served ≠ history.ack.receive.receipt.served ∧
      history.synAck.receive.receipt.served ≠ history.ack.receive.receipt.served := by
  refine ⟨?_, ?_, ?_⟩
  · intro same
    have kind := history.syn.sourceKind
    rw [same, history.synAck.sourceKind] at kind
    cases kind
  · intro same
    have kind := history.syn.sourceKind
    rw [same, history.ack.sourceKind] at kind
    cases kind
  · intro same
    have kind := history.synAck.sourceKind
    rw [same, history.ack.sourceKind] at kind
    cases kind

theorem CleanServices.slice (history : F.StartupHistory report complete) (clean : CleanServices history) :
    CampusTCPStartupAlignment.Slice history := by
  have distinct := distinct_services history
  obtain ⟨synPrior, synLater, synRecords, synBefore⟩ :=
    service_before history.syn.receive history.syn.service clean.synPrimary
  obtain ⟨synAckPrior, synAckLater, synAckRecords, synAckBefore⟩ :=
    service_before history.synAck.receive history.synAck.service clean.synAckPrimary
  obtain ⟨ackPrior, ackLater, ackRecords, ackBefore⟩ :=
    service_before history.ack.receive history.ack.service clean.ackPrimary
  have synPosition := prefix_positions synPrior synLater _ _ _ _ (synRecords.symm.trans clean.records)
  have synAckPosition := prefix_positions synAckPrior synAckLater _ _ _ _ (synAckRecords.symm.trans clean.records)
  have ackPosition := prefix_positions ackPrior ackLater _ _ _ _ (ackRecords.symm.trans clean.records)
  have synEmpty : synPrior = [] := by
    rcases synPosition with ⟨_, prior⟩ | ⟨same, _⟩ | ⟨same, _⟩
    · exact prior
    · exact False.elim (distinct.1 same)
    · exact False.elim (distinct.2.1 same)
  have synAckOne : synAckPrior = [history.syn.receive.receipt.served] := by
    rcases synAckPosition with ⟨same, _⟩ | ⟨_, prior⟩ | ⟨same, _⟩
    · exact False.elim (distinct.1 same.symm)
    · exact prior
    · exact False.elim (distinct.2.2 same)
  have ackTwo : ackPrior = [history.syn.receive.receipt.served, history.synAck.receive.receipt.served] := by
    rcases ackPosition with ⟨same, _⟩ | ⟨same, _⟩ | ⟨_, prior⟩
    · exact False.elim (distinct.2.1 same.symm)
    · exact False.elim (distinct.2.2 same.symm)
    · exact prior
  rw [synEmpty] at synBefore
  rw [synAckOne] at synAckBefore
  rw [ackTwo] at ackBefore
  simp only [P.serviceTransport, P.afterService, List.foldl_cons, List.foldl_nil,
    clean.synPrimary, clean.synAckPrimary] at synBefore synAckBefore ackBefore
  have synAdmission := congrArg TCP.Checkpoint.Gateway.admission synBefore
  have synTracker := congrArg TCP.Checkpoint.Gateway.tracker synBefore
  exact ⟨congrArg TCP.Admission.State.phase synAdmission, congrArg ConntrackLifecycle.State.records synTracker,
    congrArg TCP.Checkpoint.Gateway.admission synAckBefore, congrArg TCP.Checkpoint.Gateway.admission ackBefore,
    congrArg TCP.Checkpoint.Gateway.tracker synAckBefore, congrArg TCP.Checkpoint.Gateway.tracker ackBefore⟩

theorem CleanServices.final_transport (history : F.StartupHistory report complete) (clean : CleanServices history) :
    report.final.primary.transport =
      ⟨history.ack.receive.receipt.served.evidence.tracker, history.ack.receive.receipt.served.evidence.admission⟩ := by
  rw [CampusTCPPrimaryTransport.Report.primary_transport report, clean.records]
  simp only [P.serviceTransport, P.afterService, List.foldl_cons, List.foldl_nil,
    clean.synPrimary, clean.synAckPrimary, clean.ackPrimary]

theorem CleanServices.aligned (history : F.StartupHistory report complete) (clean : CleanServices history) :
    ∃ entry session, report.final.primary.transport.admission.phase = .data session ∧
      CampusTCPStartupAlignment.Alignment input complete entry session ∧
      report.final.primary.transport.tracker.records = [⟨entry, true⟩] := by
  obtain ⟨entry, session, phase, aligned, records⟩ := (clean.slice history).aligned history
  rw [clean.final_transport history]
  exact ⟨entry, session, phase, aligned, records⟩

end Netlib.Check.CampusTCPStartupTransport
