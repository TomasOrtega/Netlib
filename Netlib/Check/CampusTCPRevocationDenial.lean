import Netlib.Check.CampusTCPRevocationTargets
import Netlib.Check.CampusTCPOrigins

/-!
# Denial by the stored TCP revocation targets

These lemmas use each actual service and its stored native source.
They permit a stale verdict in the earlier report.
-/

namespace Netlib.Check.CampusTCPRevocationTargets

open Packet Protocol
open CampusTCPModel (Input State Gateway)

theorem Target.wire_output_none (target : Target input cut gateway)
    (closed : revoked input cut.authentication = true)
    (tracker : Protocol.ConntrackLifecycle.State) (packet : TCP.WireForwarding.Input)
    (outcome : TCP.WireForwarding.Outcome packet.packet)
    (accepted : TCP.WireForwarding.step (active input gateway target.configuration).pipeline tracker packet = .ok outcome) :
    outcome.output = none := by
  cases output : outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨model, processed, emitted, _⟩ :=
      TCP.WireForwarding.step_output _ _ _ _ accepted emission output
    have permitted := Examples.SessionFirewallDeployment.output_compiled_permit target.forward.compiled
      (active input gateway target.configuration).pipeline
      (target.forward.forward_equivalent target.forwardPassed) tracker packet.lifecycle model emission.target processed emitted
    obtain ⟨requirement, member, allowed, _⟩ :=
      (target.forward.compiled.permits_iff model.afterDestination).mp permitted
    simp [revoked_denied input cut.authentication closed requirement.scope] at allowed

theorem Target.ingress_denies (target : Target input cut gateway)
    (closed : revoked input cut.authentication = true) (index : Nat) (header : Header) :
    target.guard.source.permits index header = false := by
  have inactive (attachment : IngressAttachment.ExpectedAttachment) :
      Compile.IngressAttachment.activeAttachment (current input cut gateway)
        (input.contextFor gateway).executionNS attachment = false := by
    have denied := revoked_denied input cut.authentication closed attachment.scope
    simp only [Compile.IngressAttachment.activeAttachment, current, CampusTCPService.current,
      CampusTCPModel.beforeService, Input.contextFor_authentication, denied, Bool.and_false, Bool.false_and]
  have expected : target.ingress.expected.allows index header = false := by
    apply Bool.eq_false_iff.mpr
    intro allowed
    obtain application | maintenance :=
      (Compile.IngressAttachment.compile_numeric_allows (current input cut gateway)
        (input.contextFor gateway).executionNS (attachments cut gateway) [] index header).mp allowed
    · obtain ⟨attachment, member, selected, _⟩ := application
      simp only [inactive attachment, Bool.false_eq_true] at selected
    · obtain ⟨entry, member, _⟩ := maintenance
      cases member
  have equivalent := (IngressPolicy.check_correct target.ingress.source.compile target.ingress.expected).mp target.ingressPassed
  rw [← target.ingressSource, ← Import.NftablesIngress.Snapshot.compile_allows]
  exact (equivalent index header).trans expected

theorem Target.service_output_none (target : Target input cut gateway)
    (closed : revoked input cut.authentication = true)
    (actual : CampusTCPModel.Step input) (served : CampusTCPModel.Served input)
    (present : actual.result.service = some served)
    (installed : target.ForwardInstalled actual.before)
    (selected : served.ticket.value.gateway = gateway) : served.evidence.output = none := by
  obtain ⟨id, observed, completed, event, finished, ticket, before, time⟩ :=
    CampusTCPOrigins.service_origin actual served present
  have configuration : served.before.configuration = target.configuration := by
    rw [before]
    change (actual.before.resident served.ticket.value.gateway).configuration = _
    rw [selected]
    exact installed
  cases output : served.evidence.output with
  | none => rfl
  | some emission =>
    obtain ⟨processing, processed, emitted⟩ := served.evidence.processed_of_output emission output
    have accepted := processing.wire_step
    have pipeline : served.before.configuration.pipeline (input.contextFor served.ticket.value.gateway).routing =
        (active input gateway target.configuration).pipeline := by
      simp only [active, configuration, selected]
    rw [pipeline] at accepted
    have denied := target.wire_output_none closed served.before.tracker
      (CampusTCPService.packetInput served.before served.ticket.value.source input.zone) processing.outcome accepted
    rw [denied] at emitted
    cases emitted

theorem Target.service_early_preserves (target : Target input cut gateway)
    (closed : revoked input cut.authentication = true)
    (actual : CampusTCPModel.Step input) (served : CampusTCPModel.Served input)
    (present : actual.result.service = some served)
    (installed : target.IngressInstalled actual.before)
    (selected : served.ticket.value.gateway = gateway) :
    served.evidence.tracker = served.before.tracker ∧
      served.evidence.admission = served.before.admission ∧ served.evidence.output = none := by
  obtain ⟨id, observed, completed, event, finished, ticket, before, time⟩ :=
    CampusTCPOrigins.service_origin actual served present
  have guard : served.before.guard = target.guard.source := by
    rw [before]
    change (actual.before.resident served.ticket.value.gateway).guard.source = _
    rw [selected, installed]
  apply served.evidence.early_preserves
  rw [served.evidence.checks.actual_decision, guard]
  exact target.ingress_denies closed _ _

theorem Targets.service_output_none (targets : Targets input cut)
    (closed : revoked input cut.authentication = true)
    (actual : CampusTCPModel.Step input) (served : CampusTCPModel.Served input)
    (present : actual.result.service = some served) (installed : targets.Installed actual.before) :
    served.evidence.output = none :=
  (targets.get served.ticket.value.gateway).service_output_none closed actual served present
    (installed served.ticket.value.gateway).1 rfl

end Netlib.Check.CampusTCPRevocationTargets
