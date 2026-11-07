import Netlib.Check.CampusTCPStartupTransferBound
import Netlib.Check.CampusTCPStartupTransferObservedExchange

/-!
# Cold startup and transfer at an actual completed prefix

Observed completion retains the same native setup, endpoint histories, and
physical loss ledger. It does not require padding to a service horizon.
-/

namespace Netlib.Check.CampusTCPStartupTransferObserved

open Packet Protocol Protocol.TCP CampusTCPModel

namespace E
export CampusTCPStartupTransferExecution (Monitor initial observe monitorAt actions)
end E
namespace N
export CampusTCPStartupEntryNative (Native)
end N
namespace C
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end C
namespace O
export CampusTCPStartupTransferObservedExchange (Result)
end O
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {events : List CampusTCPModel.Event}
variable {config : CampusTCPStartupTransferMonitor.Config} {whole : Report input events}

def doneAt (config : CampusTCPStartupTransferMonitor.Config) (steps : List (Step input)) (slot : Nat) : Bool :=
  match E.monitorAt config (E.initial config) steps slot with
  | .data _ monitor => decide (monitor.exchange.mode = .done)
  | _ => false

private theorem entry_of_data (count : Nat) (within : count ≤ whole.steps.length)
    (atData : E.monitorAt config (E.initial config) whole.steps count = .data handoff monitor) :
    ∃ slot, slot < count ∧ Nonempty (CampusTCPStartupEntry.Entry config whole slot) := by
  induction count generalizing handoff monitor with
  | zero =>
    rw [CampusTCPStartupTransferSuffix.monitorAt_zero] at atData
    cases atData
  | succ count ih =>
    obtain ⟨actual, found, _, _, _⟩ := CampusTCPSchedule.Trace.at whole.trace count (by omega)
    have next := CampusTCPStartupEntry.monitorAt_next config (E.initial config) whole.steps found
    cases before : E.monitorAt config (E.initial config) whole.steps count with
    | startup prior =>
      exact ⟨count, by omega, ⟨⟨by omega, prior, before, handoff, monitor, atData⟩⟩⟩
    | data old oldMonitor =>
      obtain ⟨slot, earlier, entry⟩ := ih (by omega) before
      exact ⟨slot, by omega, entry⟩
    | invalid =>
      rw [before] at next
      simp only [E.observe] at next
      rw [next] at atData
      cases atData

theorem entry_before (slot : Nat) (within : slot ≤ whole.steps.length)
    (done : doneAt config whole.steps slot = true) :
    ∃ entrySlot, entrySlot < slot ∧ Nonempty (CampusTCPStartupEntry.Entry config whole entrySlot) := by
  unfold doneAt at done
  cases ending : E.monitorAt config (E.initial config) whole.steps slot with
  | startup monitor => rw [ending] at done; cases done
  | invalid => rw [ending] at done; cases done
  | data handoff monitor => exact entry_of_data slot within ending

def preparation (whole : Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (within : config.startup.preparation.length ≤ whole.steps.length) :
    Report input ((whole.steps.take config.startup.preparation.length).map (·.event)) :=
  CampusTCPSchedule.Report.cut whole config.startup.preparation.length within

structure Result (config : CampusTCPStartupTransferMonitor.Config) (whole : Report input events) (slot : Nat) where
  within : slot ≤ whole.steps.length
  entrySlot : Nat
  before : entrySlot + 1 ≤ slot
  entry : CampusTCPStartupEntry.Entry config whole entrySlot
  native : N.Native entry
  transfer : O.Result native.realized.task.built.initial native.checks native.routing config.transfer.quantum
    (config.transfer.lossAllowance -
      (CampusTCPSchedule.Report.cut whole native.realized.located.start native.realized.located.within).final.custody.dropped)
    config.transfer.reverseLower config.transfer.reverseUpper (whole.steps.drop (entrySlot + 1)) (slot - (entrySlot + 1))

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (S.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem complete_at (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (budget : config.transfer.lossAllowance ≤ 2)
    (prepared : config.startup.preparation.length ≤ whole.steps.length)
    (paths : CampusTCPRecoveredNative.DataPaths (base := preparation whole config prepared) config profile)
    (raw : CampusTCPRecoveredTransferTask.RawReserves input config.transfer.lower config.transfer.upper
      config.transfer.reverseLower config.transfer.reverseUpper)
    (namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS)
    (slot : Nat) (within : slot ≤ whole.steps.length) (done : doneAt config whole.steps slot = true) :
    Nonempty (Result config whole slot) := by
  obtain ⟨entrySlot, earlier, ⟨entry⟩⟩ := entry_before slot within done
  have entryPaths : CampusTCPRecoveredNative.DataPaths (base := CampusTCPStartupEntryNative.preparation entry) config profile := paths
  obtain ⟨native⟩ := CampusTCPStartupEntryNative.from_entry profile entry prep actions entryPaths raw
  let task := native.realized.task
  let base := C.cut task.prepared
  have length : base.report.steps.length = entrySlot + 1 := by
    rw [native.realized.history, List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt entry.within)]
  have placed := native.realized.placed
  have dataActions := CampusTCPStartupTransferSuffix.data_actions_suffix placed.retained.length_le placed.monitor actions
  have sameConfig := CampusTCPStartupTransferConfigBuilt.Built.data_config task.drained config.transfer task.prepared
    task.built native.checks native.routing native.ingress namespaceEq
  have remaining : config.transfer.lossAllowance - task.prepared.next.report.final.custody.dropped =
      config.transfer.lossAllowance -
        (CampusTCPSchedule.Report.cut whole native.realized.located.start native.realized.located.within).final.custody.dropped :=
    congrArg (fun count => config.transfer.lossAllowance - count) (CampusTCPRecoveredTransferTask.Task.drop_count task)
  rw [remaining] at sameConfig
  change config.transfer.data ⟨task.archive, base.report.final.custody.dropped⟩ =
    CampusTCPTwoTransferLocatedCore.config task.built.initial native.checks native.routing config.transfer.quantum
      (config.transfer.lossAllowance -
        (CampusTCPSchedule.Report.cut whole native.realized.located.start native.realized.located.within).final.custody.dropped)
      config.transfer.reverseLower config.transfer.reverseUpper at sameConfig
  have dataDone : (CampusTCPTwoTransferMonitor.monitorAt (config.transfer.data
      ⟨task.archive, base.report.final.custody.dropped⟩) .initial (whole.steps.drop base.report.steps.length)
      (slot - base.report.steps.length)).exchange.mode = .done := by
    unfold doneAt at done
    have joined : base.report.steps.length + (slot - base.report.steps.length) = slot := by rw [length]; omega
    rw [← joined, CampusTCPStartupTransferSuffix.data_monitor_suffix placed.monitor] at done
    exact of_decide_eq_true done
  rw [sameConfig, CampusTCPRecoveredTransferComplete.At.state task placed] at dataActions
  rw [sameConfig] at dataDone
  have trace := CampusTCPTraceSlices.Trace.drop whole.trace placed.retained.length_le
  rw [CampusTCPRecoveredTransferComplete.At.state task placed] at trace
  obtain ⟨transfer⟩ := CampusTCPStartupTransferObservedExchange.complete_at task.primaryEmpty task.standbyEmpty
    (CampusTCPRecoveredTransferTask.Task.target_namespace task native.checks) task.reverseEndpoints task.reverseGateway
    task.reverseLowerNonempty task.reverseUpperNonempty (Nat.le_trans (Nat.sub_le _ _) budget) trace dataActions
    (slot - base.report.steps.length) (by
      change slot - base.report.steps.length ≤ (whole.steps.drop base.report.steps.length).length
      rw [List.length_drop]
      exact Nat.sub_le_sub_right within _) dataDone
  refine ⟨⟨within, entrySlot, by omega, entry, native, ?_⟩⟩
  rw [← length]
  exact transfer

variable {slot : Nat} (value : Result config whole slot)

theorem Result.streams :
    value.transfer.readWrite.read.actual.result.read = config.transfer.lower ++ config.transfer.upper ∧
      value.transfer.value.completed.reader.result.read = config.transfer.reverseLower ++ config.transfer.reverseUpper :=
  value.transfer.streams

theorem Result.controls : value.transfer.monitor.controls.map (·.1) =
    [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] := value.transfer.controls

theorem Result.history : value.transfer.current.report.steps = whole.steps.take slot := by
  rw [value.transfer.history, value.native.realized.history, ← List.take_add, Nat.add_sub_of_le value.before]


theorem Result.final_state : value.transfer.current.report.final = S.stateAt input.initial whole.steps slot := by
  change value.transfer.point.current.report.final = _
  rw [value.transfer.point.final, value.native.realized.final, CampusTCPTraceSlices.stateAt_drop,
    Nat.add_sub_of_le value.before]

theorem Result.drop_ids : value.transfer.current.report.final.custody.droppedIDs =
    (CampusTCPSchedule.Report.cut whole value.native.realized.located.start
      value.native.realized.located.within).final.custody.droppedIDs ++ value.transfer.monitor.exchange.drops := by
  have dataIDs : CampusTCPReportLoss.dropIDs
      ((whole.steps.drop (value.entrySlot + 1)).take (slot - (value.entrySlot + 1))) =
      value.transfer.monitor.exchange.drops := value.transfer.accounting.1.symm
  rw [CampusTCPReportLoss.Report.drop_ids, value.transfer.history, CampusTCPReportLoss.dropIDs_append,
    ← CampusTCPReportLoss.Report.drop_ids, dataIDs,
    CampusTCPRecoveredTransferLedger.Task.drop_ids value.native.realized.task]

theorem Result.drop_count : value.transfer.current.report.final.custody.dropped =
    (CampusTCPSchedule.Report.cut whole value.native.realized.located.start
      value.native.realized.located.within).final.custody.dropped + value.transfer.monitor.exchange.drops.length := by
  have count := congrArg List.length value.drop_ids
  rw [List.length_append] at count
  have current := CampusTCPReportLoss.Report.drop_ids_count value.transfer.current.report
  have prior := CampusTCPReportLoss.Report.drop_ids_count
    (CampusTCPSchedule.Report.cut whole value.native.realized.located.start value.native.realized.located.within)
  rw [← CampusTCPReportLoss.Report.drop_ids] at current prior
  omega

theorem Result.whole_budget : value.transfer.current.report.final.custody.dropped ≤ config.transfer.lossAllowance := by
  have prior := value.native.realized.drops
  rw [CampusTCPRecoveredTransferTask.Task.drop_count value.native.realized.task] at prior
  have later := value.transfer.shared_budget.2
  have counted := value.drop_count
  omega

theorem Result.ids_disjoint :
    ∀ old ∈ (CampusTCPSchedule.Report.cut whole value.native.realized.located.start
      value.native.realized.located.within).final.custody.droppedIDs,
      ∀ later ∈ value.transfer.monitor.exchange.drops, old ≠ later := by
  have distinct := CampusTCPReportLoss.Report.drop_ids_distinct value.transfer.current.report
  rw [← CampusTCPReportLoss.Report.drop_ids, value.drop_ids] at distinct
  exact (List.nodup_append.mp distinct).2.2

end Netlib.Check.CampusTCPStartupTransferObserved
