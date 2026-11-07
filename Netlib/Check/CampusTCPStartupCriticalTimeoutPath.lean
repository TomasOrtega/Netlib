import Netlib.Check.CampusTCPStartupCriticalClockFrame
import Netlib.Check.CampusTCPRecoveryStartupTimeoutEnabled

/-!
# A fresh timeout output preserves an older protected path

The retry uses the fresh output-list index. It cannot mask any current job
selected by an earlier index, including a pending work ticket.
-/

namespace Netlib.Check.CampusTCPStartupCriticalTimeoutPath

open CampusTCPModel

namespace J
export CampusTCPStartupJobs (Job Source inventory packetJob ticketJob)
end J
namespace P
export CampusTCPStartupSelection (path retain phaseRank useful demand)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace T
export CampusTCPRecoveryStartupTimeoutEnabled (Timeout)
end T

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive} {actor : Actor}
variable {flight : Protocol.TCP.HandshakeTimer.Flight} {generation index : Nat} {actual : Step input}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor} {job : J.Job input}

private theorem Timeout.custody (value : T.Timeout report current actor generation flight actual) :
    actual.result.state.custody = Theory.PacketCustody.mint actual.before.custody
      (.ingress actual.before.outputs.length (.recovery value.control value.occurrence value.emitted)) := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have source : effect.output = some (.recovery value.control value.occurrence value.emitted) := by
    simpa only [final] using value.produced
  have service : effect.service = none := by simpa only [final] using value.service
  have same : custody = actual.before.custody := by
    simpa only [value.event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
  rw [final, same]
  simp only [finishCustody, source, service]

private theorem find_insert {rows tail : List α} {fresh : α} {predicate : α → Bool}
    (different : predicate fresh = false) :
    (rows ++ fresh :: tail).find? predicate = (rows ++ tail).find? predicate := by
  simp only [List.find?_append, List.find?_cons, different]

theorem Timeout.path_frame (value : T.Timeout report current actor generation flight actual)
    (found : P.path actual.before index = some job) : P.path actual.result.state index = P.path actual.before index := by
  have member : job ∈ J.inventory report.final := by
    rw [← value.before]
    exact CampusTCPStartupSelection.selected_member found
  have source := CampusTCPStartupJobSource.Report.job_lookup report job member
  have selectedIndex := CampusTCPStartupSelection.selected_index found
  have past : index < actual.before.outputs.length := by
    have bound := (List.getElem?_eq_some_iff.mp source).1
    rw [value.before]
    omega
  let produced : Produced input.active input.passive := .recovery value.control value.occurrence value.emitted
  let fresh := Theory.PacketCustody.newItem actual.before.custody (.ingress actual.before.outputs.length produced)
  let freshSource : J.Source input := ⟨value.control, value.occurrence, value.emitted⟩
  let freshJob : J.Job input := .ingress fresh actual.before.outputs.length freshSource rfl
  have freshAt : J.packetJob fresh = some freshJob := rfl
  have work : actual.result.state.work = actual.before.work := value.work.trans (congrArg State.work value.before).symm
  have custody : actual.result.state.custody.pending = actual.before.custody.pending ++ [fresh] := by
    rw [Timeout.custody value]
    rfl
  have inventory : J.inventory actual.result.state =
      actual.before.custody.pending.filterMap J.packetJob ++ freshJob :: actual.before.work.pending.filterMap J.ticketJob := by
    simp only [J.inventory, custody, work, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, freshAt, List.singleton_append, List.append_assoc]
  have different : decide (freshJob.outputIndex = index) = false := by
    change decide (actual.before.outputs.length = index) = false
    exact decide_eq_false (by omega)
  unfold P.path
  rw [inventory]
  exact find_insert different

theorem Timeout.phase (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current) :
    P.phaseRank actual.result.state = P.phaseRank actual.before := by
  simp only [P.phaseRank, value.connection, value.phase, value.before, connected]

theorem Timeout.persistent (value : T.Timeout report current actor generation flight actual)
    (connected : report.final.connection = .recovering current)
    (held : P.retain actual.before monitor.protection = some (.path index))
    (found : P.path actual.before index = some job) :
    M.advanceProtection config monitor actual = some (.path index) ∧
      R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) =
        R.rank config.transfer.quantum actual.before monitor.protection ∧
      P.demand config actual.result.state (M.advanceProtection config monitor actual) =
        P.demand config actual.before monitor.protection := by
  have useful := CampusTCPStartupCriticalClockFrame.Report.retained_useful report
    (by simpa only [value.before] using held) (by simpa only [value.before] using found)
  have relevant : P.useful (P.phaseRank actual.before) job = true := by simpa only [value.before] using useful
  have phase := Timeout.phase value connected
  have path := Timeout.path_frame value found
  have afterFound : P.path actual.result.state index = some job := path.trans found
  have retained : P.retain actual.result.state (some (.path index)) = some (.path index) :=
    CampusTCPStartupSelection.retain_live_path afterFound (by simpa only [phase] using relevant)
  have protection : M.advanceProtection config monitor actual = some (.path index) := by
    simp only [M.advanceProtection, phase, Nat.lt_irrefl, ↓reduceIte, held, M.expired]
    exact retained
  refine ⟨protection, ?_, ?_⟩
  · simp only [R.rank, phase, protection, retained, held, afterFound, found]
  · simp only [P.demand, protection, retained, held, afterFound, found]

end Netlib.Check.CampusTCPStartupCriticalTimeoutPath
