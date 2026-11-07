import Netlib.Check.CampusTCPRecoveredDrainReady
import Netlib.Check.CampusTCPRecoveredTransferTask

/-!
# The task from six actual recorded setup operations

Determinism identifies each operation with the same stored report step.
No new execution, step index, or endpoint history replaces the actual prefix.
-/

namespace Netlib.Check.CampusTCPRecoveredActualSetup

open CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend

namespace P
export CampusTCPRecoveredTransferTask (RawReserves Task prepare)
end P
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut cut_history)
end E

variable {input : Input} {events : List Event} {report : Report input events}

structure Sequence (report : Report input events) (bytes : List UInt8) where
  finish : Step input
  finishBefore : finish.before = report.final
  finishEvent : finish.event = .finishStartup
  finishSupported : finish.result.supported = true
  clientRecovery : Step input
  clientRecoveryBefore : clientRecovery.before = finish.result.state
  clientRecoveryEvent : clientRecovery.event = .enableStartupRecovery .client
  serverRecovery : Step input
  serverRecoveryBefore : serverRecovery.before = clientRecovery.result.state
  serverRecoveryEvent : serverRecovery.event = .enableStartupRecovery .server
  clientAck : Step input
  clientAckBefore : clientAck.before = serverRecovery.result.state
  clientAckEvent : clientAck.event = .enableAck .client
  serverAck : Step input
  serverAckBefore : serverAck.before = clientAck.result.state
  serverAckEvent : serverAck.event = .enableAck .server
  written : Step input
  writtenBefore : written.before = serverAck.result.state
  writtenEvent : written.event = .write .client bytes

def Sequence.steps (value : Sequence report bytes) : List (Step input) :=
  [value.finish, value.clientRecovery, value.serverRecovery, value.clientAck, value.serverAck, value.written]

variable {lower upper reverseLower reverseUpper : List UInt8}

theorem from_sequence (value : Sequence report (lower ++ upper))
    (supported : report.supported = true) (finished : report.remaining = [])
    (raw : P.RawReserves input lower upper reverseLower reverseUpper)
    (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) :
    ∃ ready : DrainReady report, ∃ task : P.Task ready lower upper reverseLower reverseUpper,
      (E.cut task.prepared).report.steps = report.steps ++ value.steps ∧
        (E.cut task.prepared).report.final = value.written.result.state := by
  obtain ⟨ready⟩ := CampusTCPRecoveredDrainReady.Report.drain_ready report supported finished
    value.finish value.finishBefore value.finishEvent value.finishSupported
  obtain ⟨task⟩ := P.prepare ready raw cold primary
  have finishEq : task.drained.actual = value.finish := CampusTCPRecoveredDrainReady.Step.determined _ _
    (task.drained.before.trans value.finishBefore.symm) (task.drained.event.trans value.finishEvent.symm)
  have clientEq : task.prepared.clientRecovery.actual = value.clientRecovery := by
    apply CampusTCPRecoveredDrainReady.Step.determined
    · rw [task.prepared.clientRecovery.before, task.drained.final, finishEq]
      exact value.clientRecoveryBefore.symm
    · exact task.prepared.clientRecovery.eventEq.trans value.clientRecoveryEvent.symm
  have serverEq : task.prepared.serverRecovery.actual = value.serverRecovery := by
    apply CampusTCPRecoveredDrainReady.Step.determined
    · rw [task.prepared.serverRecovery.before, task.prepared.clientRecovery.final, clientEq]
      exact value.serverRecoveryBefore.symm
    · exact task.prepared.serverRecovery.eventEq.trans value.serverRecoveryEvent.symm
  have clientAckEq : task.prepared.clientAck.actual = value.clientAck := by
    apply CampusTCPRecoveredDrainReady.Step.determined
    · rw [task.prepared.clientAck.before, task.prepared.serverRecovery.final, serverEq]
      exact value.clientAckBefore.symm
    · exact task.prepared.clientAck.eventEq.trans value.clientAckEvent.symm
  have serverAckEq : task.prepared.serverAck.actual = value.serverAck := by
    apply CampusTCPRecoveredDrainReady.Step.determined
    · rw [task.prepared.serverAck.before, task.prepared.clientAck.final, clientAckEq]
      exact value.serverAckBefore.symm
    · exact task.prepared.serverAck.eventEq.trans value.serverAckEvent.symm
  have writtenEq : task.prepared.written.actual = value.written := by
    apply CampusTCPRecoveredDrainReady.Step.determined
    · rw [task.prepared.written.before, task.prepared.serverAck.final, serverAckEq]
      exact value.writtenBefore.symm
    · exact task.prepared.written.eventEq.trans value.writtenEvent.symm
  refine ⟨ready, task, ?_, ?_⟩
  · rw [E.cut_history task.drained task.prepared]
    simp only [Prepared.joints, Sequence.steps, finishEq, clientEq, serverEq, clientAckEq, serverAckEq, writtenEq]
  · change task.prepared.written.next.report.final = _
    rw [task.prepared.written.final, writtenEq]

end Netlib.Check.CampusTCPRecoveredActualSetup
