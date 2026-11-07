import Netlib.Check.CampusTCPRecoveryReceipts
import Netlib.Check.CampusTCPPrimaryTransport

/-!
# Actual campus delivery for a recovery receipt

The bridge uses the recorded recovery operation and its actual receive event.
It keeps the same campus receipt, gateway service, and earlier occurrence.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupReceiptSteps

open Protocol.TCP CampusTCPModel

variable {input : Input} {control : C.Step input.active input.passive}

def NonRecoveryEvent : Event → Prop
  | .openRecovering .. | .startupClock .. | .startupTimeout .. | .deliver .. => False
  | _ => True

private theorem application_none (computed : applyApplication input before actor event = .ok effect) : effect.recovery = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem startup_none (computed : startup input before event = .ok effect) : effect.recovery = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_none (computed : enableAck input before actor = .ok effect) : effect.recovery = none := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_none computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem handoff_none (computed : enableStartupRecovery input before actor = .ok effect) : effect.recovery = none := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; rfl
  · exact application_none computed

private theorem drain_none (computed : finishStartup input before = .ok effect) : effect.recovery = none := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem process_none (computed : processCore input before event = .ok effect) (quiet : NonRecoveryEvent event) :
    effect.recovery = none := by
  cases event with
  | openRecovering remote policy | startupClock actor millis | startupTimeout actor generation policy | deliver index bytes policy =>
    cases quiet
  | «open» remote policy => exact startup_none computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_none computed
  | enableAck actor => exact ack_none computed
  | enableStartupRecovery actor => exact handoff_none computed
  | finishStartup => exact drain_none computed
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id
  | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.recovery_none (actual : Step input) (quiet : NonRecoveryEvent actual.event) : actual.result.recovery = none := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  simpa only [final] using process_none computed quiet

theorem Step.receive_delivered (actual : Step input) (recorded : actual.result.recovery = some control)
    (received : control.event = .receive source bytes path policy) :
    ∃ index raw permission, actual.event = .deliver index raw permission := by
  cases event : actual.event
  all_goals first
    | exact ⟨_, _, _, rfl⟩
    | (solve |
      have current := CampusTCPRecoveryReceipts.Step.recovery_open actual recorded event
      rw [received] at current
      cases current)
    | (solve |
      have current := CampusTCPRecoveryReceipts.Step.recovery_clock actual recorded event
      rw [received] at current
      cases current)
    | (solve |
      have current := CampusTCPRecoveryReceipts.Step.recovery_timeout actual recorded event
      rw [received] at current
      cases current)
    | (solve |
      have absent := Step.recovery_none actual (by rw [event]; trivial)
      rw [absent] at recorded
      cases recorded)

structure ActualReceipt (report : Report input events) (control : C.Step input.active input.passive) (receipt : C.Receipt) where
  joint : Step input
  member : joint ∈ report.steps
  recorded : joint.result.recovery = some control
  delivery : CampusTCPRecoveryReceipts.Delivery joint control
  receiptEq : delivery.received = receipt
  source : CampusTCPRecoveryReceipts.Source report delivery
  serviceMember : delivery.receipt.served ∈ report.final.services

theorem Report.actual_receipt (report : Report input events) (control : C.Step input.active input.passive)
    (member : control ∈ report.steps.filterMap (·.result.recovery)) (receipt : C.Receipt)
    (recorded : control.result.receipt = some receipt) (received : control.event = .receive source bytes path policy) :
    Nonempty (ActualReceipt report control receipt) := by
  obtain ⟨joint, jointMember, selected, _⟩ := CampusTCPRecoveryStartupOrigins.Report.recovery_step_origin report member
  obtain ⟨index, raw, permission, event⟩ := Step.receive_delivered joint selected received
  obtain ⟨delivery⟩ := CampusTCPRecoveryReceipts.Step.recovery_delivery joint selected event
  have same := Option.some.inj (delivery.receivedAt.symm.trans recorded)
  obtain ⟨source⟩ := delivery.report_source report jointMember
  obtain ⟨service⟩ := CampusTCPStartupOrigins.DeliveryAt.service_exists (delivery.at report jointMember)
  have serviceMember : delivery.receipt.served ∈ report.final.services := by
    rw [CampusTCPPrimaryTransport.Report.services report]
    exact List.mem_filterMap.mpr ⟨service.joint.step, service.joint.member, service.present⟩
  exact ⟨⟨joint, jointMember, selected, delivery, same, source, serviceMember⟩⟩

end Netlib.Check.CampusTCPRecoveryStartupReceiptSteps
