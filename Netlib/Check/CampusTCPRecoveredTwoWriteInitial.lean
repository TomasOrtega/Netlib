import Netlib.Check.CampusTCPRecoveryStartupFold
import Netlib.Check.CampusTCPRecoveredTwoWriteGeometry

/-!
# The actual two-record task after recovered startup

The cold report derives its gateway session and retained startup source.
The task uses the actual prepared writer and inherited timer states.
-/

namespace Netlib.Check.CampusTCPRecoveredTwoWriteInitial

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend CampusTCPTwoProgressStart
open CampusTCPRecoveryStartupCold CampusTCPRecoveryStartupTransport

namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut Reserves)
end E

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {lower upper : List UInt8}

private def basis (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (aligned : Aligned ready) : StartupBasis (E.cut value) where
  events := _
  report := drained.next.report
  supported := drained.next.supported
  finished := drained.next.finished
  endpoints := drained.next.endpoints
  connection := drained.next.connection
  origin := .recovered ready archive drained
  retained := ⟨value.joints, value.history⟩
  entry := aligned.entry
  session := aligned.session
  aligned := by
    rw [drained.complete]
    exact aligned.static
  phase := by
    change (beforeService input drained.next.report.final .primary).admission.phase = .data aligned.session
    rw [CampusTCPRecoveredSetupAppend.Drained.gateway_frame drained .primary]
    exact aligned.phase

private def gateway (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (aligned : Aligned ready) : GatewayStart (E.cut value) (basis drained value aligned) .primary := by
  have frame := (value.gateway_frame .primary).trans (CampusTCPRecoveredSetupAppend.Drained.gateway_frame drained .primary)
  exact {
    session := aligned.session
    identity := CampusTCPGapProgressStart.Identity.refl _
    phase := by
      change (beforeService input value.next.report.final .primary).admission.phase = .data aligned.session
      rw [frame]
      exact aligned.phase
    trackerValid := by
      change (beforeService input value.next.report.final .primary).tracker.Valid
      rw [frame]
      exact aligned.trackerValid
    record := aligned.record
    member := by
      change aligned.record ∈ (beforeService input value.next.report.final .primary).tracker.records
      rw [frame]
      exact aligned.member
    entry := aligned.recordEntry
    confirmed := aligned.confirmed }

structure Built (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper)) where
  initial : TwoWriteInitial (E.cut value) .client .primary lower upper
  writer : initial.write.writer = value.written.operation
  basisReport : initial.basis.report.steps = drained.next.report.steps
  gatewayShape : CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive initial.gatewayState.session
  senderTimer : initial.senderState.idle.recovery.now = archive.activeData.now ∧
    initial.senderState.idle.recovery.rto = archive.activeData.rto ∧
    initial.senderState.idle.recovery.estimator = archive.activeData.estimator
  receiverTimer : initial.receiverState.idle.recovery.now = archive.passiveData.now ∧
    initial.receiverState.idle.recovery.rto = archive.passiveData.rto ∧
    initial.receiverState.idle.recovery.estimator = archive.passiveData.estimator

private def fromAligned (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (reserves : E.Reserves archive lower upper) (aligned : Aligned ready) : Built drained value := by
  let endpoints := CampusTCPRecoveredTwoWriteEndpoints.ofPrepared drained value reserves
  let selected := gateway drained value aligned
  let initial : TwoWriteInitial (E.cut value) .client .primary lower upper := {
    basis := basis drained value aligned
    lowerNonempty := endpoints.lowerNonempty
    upperNonempty := endpoints.upperNonempty
    write := endpoints.write
    senderState := endpoints.sender
    receiverState := endpoints.receiver
    gatewayState := selected
    geometry := CampusTCPRecoveredTwoWriteGeometry.geometry drained value reserves selected (by
      change CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive aligned.session
      exact aligned.geometry) }
  exact ⟨initial, rfl, rfl, (by
      change CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive aligned.session
      exact aligned.geometry),
    CampusTCPRecoveredTwoWriteEndpoints.idle_timer_fields drained value .client,
    CampusTCPRecoveredTwoWriteEndpoints.idle_timer_fields drained value .server⟩

theorem ofPrepared (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (reserves : E.Reserves archive lower upper) (cold : ColdProfile report) (primary : PrimaryServices report) :
    Nonempty (Built drained value) := by
  obtain ⟨aligned⟩ := CampusTCPRecoveryStartupTransport.aligned ready cold primary
  exact ⟨fromAligned drained value reserves aligned⟩

end Netlib.Check.CampusTCPRecoveredTwoWriteInitial
