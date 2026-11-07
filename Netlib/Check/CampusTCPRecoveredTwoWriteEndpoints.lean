import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Check.CampusTCPRecoveredSetupAppend

/-!
# Two-record endpoints after the actual recovery setup

The cut and writer come from the same prepared report.
Startup clocks, RTOs, estimators, and early operations remain in that report.
-/

namespace Netlib.Check.CampusTCPRecoveredTwoWriteEndpoints

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPTwoProgressStart
open CampusTCPRound (Cut)

variable {input : Input} {events : List Event} {report : Report input events}
variable {archive : RecoveryArchive input.active input.passive} {ready : DrainReady report}
variable {start : Prefix input events archive} {bytes lower upper : List UInt8}

def cut (value : Prepared start bytes) : Cut input archive.complete :=
  ⟨_, value.next.report, value.next.supported, value.next.finished, value.next.endpoints, value.next.connection⟩

private theorem client_start (drained : Drained ready archive) :
    endpoint drained.next.endpoints .client = archive.client.current := drained.cursors.1

private theorem server_start (drained : Drained ready archive) :
    endpoint drained.next.endpoints .server = archive.server.current := drained.cursors.2.1

private theorem writer_before (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    value.written.operation.before = ackState (Endpoint.startupRecoveryState archive.client.current archive.activeData) := by
  have ackPeer : endpoint value.serverAck.next.endpoints .client = endpoint value.clientAck.next.endpoints .client :=
    value.serverAck.peer
  have recoveryPeer : endpoint value.serverRecovery.next.endpoints .client = endpoint value.clientRecovery.next.endpoints .client :=
    value.serverRecovery.peer
  rw [value.written.localBefore, ackPeer, value.clientAck.selected,
    recoveryPeer, value.clientRecovery.selected, client_start drained]
  rfl

def written_batch (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    WrittenBatch (cut value) .client bytes :=
  WrittenBatch.ofLast value.written.operation (applicationSteps value.serverAck.next.endpoints .client)
    value.written.selectedSteps value.written.localEvent value.written.accepted
    (by rw [writer_before drained value]; exact drained.next.archive_clean.1.fields.2.2.2.1)
    (by rw [writer_before drained value]; exact drained.next.archive_clean.1.fields.2.2.2.2.1)

theorem written_batch_writer (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    (written_batch drained value).writer = value.written.operation := rfl

theorem writer_recorded (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    value.written.actual ∈ (cut value).report.steps ∧
      value.written.actual.result.application = some (.client, (written_batch drained value).writer) := by
  constructor
  · change value.written.actual ∈ value.written.next.report.steps
    rw [value.written.last]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact value.written.recorded

theorem cut_history (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    (cut value).report.steps = report.steps ++ drained.actual :: value.joints := by
  change value.next.report.steps = _
  rw [value.history, drained.history]
  simp only [List.append_assoc, List.singleton_append]

def idle (drained : Drained ready archive) (value : Prepared drained.next bytes) (actor : Actor) :
    IdleEndpoint (endpoint (cut value).endpoints actor) where
  recovery := Endpoint.startupRecovery (endpoint drained.next.endpoints actor).effectiveMSS (archive.data actor)
  reaction := AckReaction.initial (endpoint drained.next.endpoints actor).core.receiveNext
    (endpoint drained.next.endpoints actor).core.capacity (endpoint drained.next.endpoints actor).localReceiveMSS.limit
  runtime := by cases actor <;> first | exact value.runtime.1 | exact value.runtime.2
  ackRuntime := by
    dsimp only [cut]
    cases actor <;> first | (rw [value.client_state]; rfl) | (rw [value.server_state]; rfl)
  outstanding := rfl
  sent := by
    dsimp only [cut]
    have geometry := prepared_geometry drained value
    cases actor
    · rw [geometry.1]
      exact drained.next.archive_clean.1.fields.2.2.2.2.1
    · rw [geometry.2.1]
      exact drained.next.archive_clean.2.fields.2.2.2.2.1
  deadline := rfl
  timedOut := rfl
  timeoutCount := rfl
  duplicate := rfl
  valid := endpoint_valid value.next.endpoints actor
  coherent := (prepared_guards drained value actor).1
  prepared := (prepared_guards drained value actor).2.1
  storage := (prepared_guards drained value actor).2.2

structure Reserves (archive : RecoveryArchive input.active input.passive) (lower upper : List UInt8) : Prop where
  lowerNonempty : lower ≠ []
  upperNonempty : upper ≠ []
  window : lower.length + upper.length ≤ archive.client.current.sendWindow
  mss : lower.length + upper.length ≤ archive.client.current.effectiveMSS
  space : (lower ++ upper).length ≤ archive.server.current.core.capacity

structure Endpoints (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper)) where
  lowerNonempty : lower ≠ []
  upperNonempty : upper ≠ []
  write : WrittenBatch (cut value) .client (lower ++ upper)
  sender : WrittenSender (cut value) .client lower upper
  receiver : EmptyReceiver (cut value) .server (lower ++ upper)

def ofPrepared (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (reserves : Reserves archive lower upper) : Endpoints drained value where
  lowerNonempty := reserves.lowerNonempty
  upperNonempty := reserves.upperNonempty
  write := written_batch drained value
  sender := {
    idle := idle drained value .client
    pending := (prepared_geometry drained value).2.2.1
    held := by dsimp only [cut]; rw [(prepared_geometry drained value).2.2.2.2.1]; rfl
    window := by dsimp only [cut]; rw [value.client_state, client_start drained]; exact reserves.window
    mss := by dsimp only [cut]; rw [value.client_state, client_start drained]; exact reserves.mss }
  receiver := {
    idle := idle drained value .server
    pending := (prepared_geometry drained value).2.2.2.1
    unread := by
      dsimp only [cut]
      rw [(prepared_geometry drained value).2.1]
      exact drained.next.archive_clean.2.fields.2.2.2.2.2.1
    held := by dsimp only [cut]; rw [(prepared_geometry drained value).2.2.2.2.2]; rfl
    space := by
      dsimp only [cut]
      rw [value.server_state, server_start drained]
      change (lower ++ upper).length ≤ archive.server.current.core.capacity
      exact reserves.space }

theorem idle_timer_fields (drained : Drained ready archive) (value : Prepared drained.next bytes) (actor : Actor) :
    (idle drained value actor).recovery.now = (archive.data actor).now ∧
      (idle drained value actor).recovery.rto = (archive.data actor).rto ∧
      (idle drained value actor).recovery.estimator = (archive.data actor).estimator := ⟨rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPRecoveredTwoWriteEndpoints
