import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Check.CampusTCPRoundLocal

/-!
# Accepted writes at the current campus cut

The write extends the actual report and local application history.
Its endpoint and gateway frames retain the prior state.
-/

namespace Netlib.Check.CampusTCPWriteEnabled

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : Cut input complete} {actor : Actor} {bytes : List UInt8} {actual : Step input}

structure WriteMove (current : Cut input complete) (actor : Actor) (bytes : List UInt8) (actual : Step input) where
  move : Move current actual
  event : actual.event = .write actor bytes
  operation : T.Step
  recorded : actual.result.application = some (actor, operation)
  localBefore : operation.before = endpoint current.endpoints actor
  localEvent : operation.event = .write bytes
  localStamp : operation.stamp = current.report.final.time
  accepted : operation.result.decision = .accepted (.write bytes.length)
  selected : endpoint move.after.endpoints actor = Endpoint.writeState (endpoint current.endpoints actor) bytes
  peer : endpoint move.after.endpoints actor.other = endpoint current.endpoints actor.other
  selectedSteps : applicationSteps move.after.endpoints actor = applicationSteps current.endpoints actor ++ [operation]
  peerSteps : applicationSteps move.after.endpoints actor.other = applicationSteps current.endpoints actor.other
  quiet : actual.result.output = none
  read : actual.result.read = []
  gateway : ∀ gateway, beforeService input move.after.report.final gateway = beforeService input current.report.final gateway
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final

theorem write_at (current : Cut input complete) (actor : Actor) (bytes : List UInt8)
    (fits : (endpoint current.endpoints actor).pending.length + bytes.length ≤ (endpoint current.endpoints actor).pendingLimit) :
    ∃ actual : Step input, Nonempty (WriteMove current actor bytes actual) := by
  have chronology := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  have earlier : ∀ old ∈ applicationSteps current.endpoints actor, old.stamp < current.report.final.time := by
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨effect, computed, supported, quiet, read, application⟩ :=
    CampusTCPEnabled.write_enabled current.report.final complete current.endpoints current.connection actor bytes earlier fits
  let actual : Step input := ⟨current.report.final, .write actor bytes, effect, computed⟩
  let operation := ApplicationTrace.Step.make (endpoint current.endpoints actor) (endpoint_valid current.endpoints actor)
    (.write bytes) current.report.final.time
  have recorded : actual.result.application = some (actor, operation) := application
  have written := Endpoint.write_of_fits (endpoint current.endpoints actor) bytes (endpoint_valid current.endpoints actor) fits
  have accepted : operation.result.decision = .accepted (.write bytes.length) := by
    change (Endpoint.write (endpoint current.endpoints actor) bytes).decision = _
    rw [written]
  have state : operation.result.state = Endpoint.writeState (endpoint current.endpoints actor) bytes := by
    change (Endpoint.write (endpoint current.endpoints actor) bytes).state = _
    rw [written]
  obtain ⟨after, connected, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete current.endpoints current.connection actor (.write bytes)
      (.write bytes) operation recorded
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual rfl supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, after, connected⟩
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual actor (.write bytes) (.write bytes)
  let move : Move current actual := ⟨next, rfl, supported, passed, rfl, rfl⟩
  exact ⟨actual, ⟨{
    move, event := rfl, operation, recorded, localBefore, localEvent, localStamp, accepted
    selected := selected.trans state, peer, selectedSteps, peerSteps
    quiet, read
    gateway := fun gateway => CampusTCPRoundLocal.step_service_nonservice actual trivial gateway
    environment := CampusTCPRoundEnvironment.Step.environment actual trivial }⟩⟩

def WriteMove.batch (value : WriteMove current actor bytes actual)
    (pending : (endpoint current.endpoints actor).pending = [])
    (sent : (endpoint current.endpoints actor).core.sent = []) :
    CampusTCPTwoProgressStart.WrittenBatch value.move.after actor bytes :=
  CampusTCPTwoProgressStart.WrittenBatch.ofLast value.operation (applicationSteps current.endpoints actor)
    value.selectedSteps value.localEvent value.accepted (value.localBefore.symm ▸ pending) (value.localBefore.symm ▸ sent)

theorem Step.write (actual : Step input) (current : Cut input complete) (actor : Actor) (bytes : List UInt8)
    (before : actual.before = current.report.final) (event : actual.event = .write actor bytes)
    (fits : (endpoint current.endpoints actor).pending.length + bytes.length ≤ (endpoint current.endpoints actor).pendingLimit) :
    Nonempty (WriteMove current actor bytes actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := write_at current actor bytes fits
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.move.beforeEq.trans before.symm) (value.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPWriteEnabled
