import Netlib.Check.CampusTCPRecoveredTransferTask
import Netlib.Check.CampusTCPStartupClockBounds
import Netlib.Protocol.TCP.HandshakeDataBounds

/-!
# Data intervals from the same recovered report

The actual setup length bounds both inherited timers and their fresh samples.
The finite estimator maximum also covers later bounded data samples.
-/

namespace Netlib.Check.CampusTCPRecoveredTimerBound

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend

namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E
namespace P
export CampusTCPRecoveredTransferTask (Task)
end P
namespace H
export HandshakeTimer (dataCapacity dataCapacity_bound dataCapacity_mono)
end H

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {lower upper reverseLower reverseUpper : List UInt8}
variable (task : P.Task ready lower upper reverseLower reverseUpper)
variable {quantum setupSlots span : Nat}

theorem Task.timer_capacity
    (actions : CampusTCPStartupClockBounds.Actions quantum (E.cut task.prepared).report.steps)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots) (actor : Actor) :
    max (task.archive.data actor).rto (RTO.sampleCap (task.archive.data actor).estimator span) ≤
      H.dataCapacity (quantum * setupSlots) span := by
  obtain ⟨_, interval, recorded⟩ := CampusTCPStartupClockBounds.Report.archive_handoff_bounds
    (E.cut task.prepared).report actions task.prepared.next.archived actor
  have actual := H.dataCapacity_bound (task.archive.data actor) interval recorded (span := span)
  exact Nat.le_trans actual (H.dataCapacity_mono (Nat.mul_le_mul_left quantum within) (Nat.le_refl _))

theorem Task.sender_capacity
    (actions : CampusTCPStartupClockBounds.Actions quantum (E.cut task.prepared).report.steps)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots) :
    max task.built.initial.senderState.idle.recovery.rto
      (RTO.sampleCap task.built.initial.senderState.idle.recovery.estimator span) ≤
      H.dataCapacity (quantum * setupSlots) span := by
  rw [task.built.senderTimer.2.1, task.built.senderTimer.2.2]
  exact Task.timer_capacity task actions within .client

theorem Task.receiver_capacity
    (actions : CampusTCPStartupClockBounds.Actions quantum (E.cut task.prepared).report.steps)
    (within : (E.cut task.prepared).report.steps.length ≤ setupSlots) :
    max task.built.initial.receiverState.idle.recovery.rto
      (RTO.sampleCap task.built.initial.receiverState.idle.recovery.estimator span) ≤
      H.dataCapacity (quantum * setupSlots) span := by
  rw [task.built.receiverTimer.2.1, task.built.receiverTimer.2.2]
  exact Task.timer_capacity task actions within .server

end Netlib.Check.CampusTCPRecoveredTimerBound
