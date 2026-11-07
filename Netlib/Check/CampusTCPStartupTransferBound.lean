import Netlib.Check.CampusTCPStartupDataEntryBound
import Netlib.Check.CampusTCPStartupEntryNative
import Netlib.Check.CampusTCPRecoveredTransferHorizon
import Netlib.Check.CampusTCPRecoveredTransferLedger

/-!
# One bounded execution from cold startup through both transfer directions

The actual startup entry supplies the task, native paths, timers, and loss ledger.
One whole action check and service check cover the complete retained history.
-/

namespace Netlib.Check.CampusTCPStartupTransferBound

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial actions check)
end E
namespace S
export CampusTCPStartupDataEntryBound (setupSlots)
end S
namespace N
export CampusTCPStartupEntryNative (Native)
end N
namespace C
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end C
namespace R
export CampusTCPTwoTransferExchangeResult (Result)
end R

variable {input : Input} {events : List CampusTCPModel.Event}
variable {config : CampusTCPStartupTransferMonitor.Config} {whole : Report input events} {bound : Nat}

def totalSlots (config : CampusTCPStartupTransferMonitor.Config) (bound : Nat) : Nat :=
  S.setupSlots config bound + CampusTCPRecoveredTransferBound.slots config.transfer.quantum
    config.transfer.lossAllowance (S.setupSlots config bound) bound

theorem preparation_within (within : totalSlots config bound ≤ whole.steps.length) :
    config.startup.preparation.length ≤ whole.steps.length := by
  have start : CampusTCPStartupBound.start config ≤ CampusTCPStartupBound.base config bound := Nat.le_add_right _ _
  have base : CampusTCPStartupBound.base config bound ≤ CampusTCPStartupBound.completionBound config bound :=
    Theory.FiniteLossProgress.base_le_horizon _ _ _
  have setup := CampusTCPStartupDataEntryBound.completion_le_setup (config := config) (bound := bound)
  have total : S.setupSlots config bound ≤ totalSlots config bound := Nat.le_add_right _ _
  unfold CampusTCPStartupBound.start at start
  omega

def preparation (whole : Report input events) (config : CampusTCPStartupTransferMonitor.Config) (bound : Nat)
    (within : totalSlots config bound ≤ whole.steps.length) :
    Report input ((whole.steps.take config.startup.preparation.length).map (·.event)) :=
  CampusTCPSchedule.Report.cut whole config.startup.preparation.length (preparation_within within)

structure Result (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (bound : Nat) where
  entrySlot : Nat
  entry : CampusTCPStartupEntry.Entry config whole entrySlot
  withinSetup : entrySlot + 1 ≤ S.setupSlots config bound
  native : N.Native entry
  transfer : R.Result native.realized.task.built.initial native.checks native.routing config.transfer.quantum
    (config.transfer.lossAllowance -
      (CampusTCPSchedule.Report.cut whole native.realized.located.start native.realized.located.within).final.custody.dropped)
    config.transfer.reverseLower config.transfer.reverseUpper bound (whole.steps.drop (entrySlot + 1))

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem complete (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (checked : E.check config input.initial (E.initial config) whole.steps bound = true)
    (budget : config.transfer.lossAllowance ≤ 2) (positive : 0 < config.transfer.quantum) (boundPositive : 0 < bound)
    (within : totalSlots config bound ≤ whole.steps.length)
    (paths : CampusTCPRecoveredNative.DataPaths (base := preparation whole config bound within) config profile)
    (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (raw : CampusTCPRecoveredTransferTask.RawReserves input config.transfer.lower config.transfer.upper
      config.transfer.reverseLower config.transfer.reverseUpper)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS) :
    Nonempty (Result config whole bound) := by
  have dataPositive : 0 < CampusTCPRecoveredTransferBound.slots config.transfer.quantum
      config.transfer.lossAllowance (S.setupSlots config bound) bound := by
    unfold CampusTCPRecoveredTransferBound.slots
    apply Nat.mul_pos
    · omega
    · exact boundPositive
  have available : S.setupSlots config bound < whole.steps.length := by unfold totalSlots at within; omega
  obtain ⟨slot, entry, entryWithin⟩ := CampusTCPStartupDataEntryBound.entry_by_checked profile prep actions checked
    paths.primary valid target positive boundPositive available
  obtain ⟨native⟩ := CampusTCPStartupEntryNative.from_entry profile entry prep actions paths raw
  have length : (C.cut native.realized.task.prepared).report.steps.length = slot + 1 := by
    rw [native.realized.history, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt entry.within)]
  have setupWithin : (C.cut native.realized.task.prepared).report.steps.length ≤ S.setupSlots config bound := by
    rw [length]
    exact entryWithin
  obtain ⟨transfer⟩ := CampusTCPRecoveredTransferHorizon.complete_from_whole native.realized.task native.realized.placed
    native.checks native.routing native.ingress namespaceEq prep budget positive actions checked setupWithin within
  refine ⟨⟨slot, entry, entryWithin, native, ?_⟩⟩
  simpa only [length] using transfer

variable (value : Result config whole bound)

theorem Result.streams :
    value.transfer.readWrite.read.actual.result.read = config.transfer.lower ++ config.transfer.upper ∧
      value.transfer.reverse.value.completed.reader.result.read = config.transfer.reverseLower ++ config.transfer.reverseUpper :=
  value.transfer.streams

theorem Result.controls : value.transfer.monitor.controls.map (·.1) =
    [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] := value.transfer.controls

theorem Result.history : value.transfer.current.report.steps = whole.steps.take (value.entrySlot + 1 + value.transfer.slot) := by
  rw [value.transfer.history, value.native.realized.history]
  exact (List.take_add (l := whole.steps) (i := value.entrySlot + 1) (j := value.transfer.slot)).symm

theorem Result.whole_budget : value.transfer.current.report.final.custody.dropped ≤ config.transfer.lossAllowance := by
  have earlier : (CampusTCPSchedule.Report.cut whole value.native.realized.located.start
      value.native.realized.located.within).final.custody.dropped ≤ config.transfer.lossAllowance := by
    rw [← CampusTCPRecoveredTransferTask.Task.drop_count value.native.realized.task]
    exact value.native.realized.drops
  exact CampusTCPRecoveredTransferLedger.Result.whole_budget value.native.realized.task value.transfer
    config.transfer.lossAllowance earlier rfl

theorem Result.drop_ids : value.transfer.current.report.final.custody.droppedIDs =
    (CampusTCPSchedule.Report.cut whole value.native.realized.located.start value.native.realized.located.within).final.custody.droppedIDs ++
      value.transfer.monitor.exchange.drops :=
  CampusTCPRecoveredTransferLedger.Result.drop_ids value.native.realized.task value.transfer

theorem Result.ids_disjoint :
    ∀ old ∈ (CampusTCPSchedule.Report.cut whole value.native.realized.located.start
      value.native.realized.located.within).final.custody.droppedIDs,
      ∀ later ∈ value.transfer.monitor.exchange.drops, old ≠ later :=
  CampusTCPRecoveredTransferLedger.Result.ids_disjoint value.native.realized.task value.transfer

theorem Result.deadline : value.entrySlot + 1 + value.transfer.slot ≤ totalSlots config bound := by
  have length : (C.cut value.native.realized.task.prepared).report.steps.length = value.entrySlot + 1 := by
    rw [value.native.realized.history, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt value.entry.within)]
  have within : (C.cut value.native.realized.task.prepared).report.steps.length ≤ S.setupSlots config bound := by
    rw [length]
    exact value.withinSetup
  have capacity := CampusTCPRecoveredTransferBound.Task.whole_slots_le value.native.realized.task
    value.native.realized.clocks within (allowance := config.transfer.lossAllowance) (bound := bound)
  have deadline := value.transfer.deadline
  change value.transfer.slot ≤ _ at deadline
  unfold totalSlots
  omega

end Netlib.Check.CampusTCPStartupTransferBound
