import Netlib.Check.CampusTCPStartupSetupInterval
import Netlib.Check.CampusTCPStartupPrimaryServices
import Netlib.Check.CampusTCPStartupActionsProfile
import Netlib.Check.CampusTCPStartupDropBound
import Netlib.Check.CampusTCPRecoveredTransferComplete

/-!
# The actual transfer task at the first data entry

The six recorded steps determine the task without a supplied ready state.
Cold sources, primary service, clocks, and loss funding come from whole Actions.
-/

namespace Netlib.Check.CampusTCPStartupEntryTask

open CampusTCPModel CampusTCPStartupEntry CampusTCPStartupSetupInterval

namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace W
export CampusTCPStartupTransferExecution (initial actions)
end W
namespace P
export CampusTCPRecoveredTransferTask (RawReserves Task)
end P
namespace C
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end C
namespace B
export CampusTCPStartupClockBounds (Actions)
end B
namespace T
export CampusTCPStartupTransferConfig (Handoff)
end T

variable {input : Input} {events : List Event} {config : M.Config} {whole : Report input events} {slot : Nat}

structure Realized (entry : Entry config whole slot) where
  located : Located entry
  ready : CampusTCPRecoveredSetup.DrainReady (CampusTCPSchedule.Report.cut whole located.start located.within)
  task : P.Task ready config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper
  history : (C.cut task.prepared).report.steps = whole.steps.take (slot + 1)
  final : (C.cut task.prepared).report.final = CampusTCPSchedule.stateAt input.initial whole.steps (slot + 1)
  placed : CampusTCPRecoveredTransferComplete.At task whole
  clocks : B.Actions config.transfer.quantum (C.cut task.prepared).report.steps
  drops : (C.cut task.prepared).report.final.custody.dropped ≤ config.transfer.lossAllowance

private theorem handoff_eq {active passive : Protocol.TCP.Handshake.Local} {first second : T.Handoff active passive}
    (archive : first.archive = second.archive) (drops : first.startupDrops = second.startupDrops) : first = second := by
  cases first
  cases second
  cases archive
  cases drops
  rfl

theorem from_entry (entry : Entry config whole slot) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : W.actions config input.initial (W.initial config) whole.steps = true)
    (raw : P.RawReserves input config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper) :
    Nonempty (Realized entry) := by
  obtain ⟨located⟩ := locate entry
  have before : located.start < whole.steps.length := by
    have interval := located.count
    have available := entry.within
    omega
  have supported := CampusTCPSchedule.Report.cut_supported whole located.start before
  have cold := CampusTCPStartupProfileFacts.Report.cut_cold_profile whole prep actions located.within located.before
    (by rw [located.mode]; trivial)
  have primary := CampusTCPStartupPrimaryServices.Report.cut_primary_services whole prep actions located.within located.before
    (by rw [located.mode]; trivial)
  obtain ⟨ready, task, taskHistory, taskFinal⟩ := CampusTCPRecoveredActualSetup.from_sequence located.sequence supported rfl raw cold primary
  have history : (C.cut task.prepared).report.steps = whole.steps.take (slot + 1) := taskHistory.trans located.history
  have final : (C.cut task.prepared).report.final = CampusTCPSchedule.stateAt input.initial whole.steps (slot + 1) :=
    taskFinal.trans located.final
  have actualFinal : (C.cut task.prepared).report.final = entry.actual.result.state := by
    simpa only [located.written] using taskFinal
  have length : (C.cut task.prepared).report.steps.length = slot + 1 := by
    rw [history, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt entry.within)]
  have snapshot := CampusTCPStartupTransferSuffix.observe_startup_snapshot entry.actual entry.startup entry.observed
  have archived : entry.actual.result.state.recoveryArchive = some task.archive := by
    rw [← actualFinal]
    exact task.prepared.next.archived
  have archiveEq : entry.handoff.archive = task.archive := Option.some.inj (snapshot.1.symm.trans archived)
  have dropsEq : entry.handoff.startupDrops = (C.cut task.prepared).report.final.custody.dropped :=
    snapshot.2.trans (congrArg (fun state : State input => state.custody.dropped) actualFinal).symm
  have retainedHandoff : entry.handoff = ⟨task.archive, (C.cut task.prepared).report.final.custody.dropped⟩ :=
    handoff_eq archiveEq dropsEq
  have placed : CampusTCPRecoveredTransferComplete.At task whole := {
    retained := ⟨whole.steps.drop (slot + 1), by rw [history, List.take_append_drop]⟩
    monitor := by
      rw [length]
      have entered := entry.after
      rw [entry.initial_monitor, retainedHandoff] at entered
      exact entered }
  have clocks : B.Actions config.transfer.quantum (C.cut task.prepared).report.steps := by
    rw [history]
    exact (CampusTCPStartupActionsProfile.Report.clock_actions whole prep actions).take (slot + 1)
  have drops : (C.cut task.prepared).report.final.custody.dropped ≤ config.transfer.lossAllowance := by
    rw [CampusTCPRecoveredTransferTask.Task.drop_count task]
    exact CampusTCPStartupDropBound.Report.cut_drop_bound whole prep actions located.within located.before
  exact ⟨⟨located, ready, task, history, final, placed, clocks, drops⟩⟩

end Netlib.Check.CampusTCPStartupEntryTask
