import Netlib.Check.CampusTCPRecoveryRoundDemand
import Netlib.Check.CampusTCPRecoveryRoundPhaseForward
import Netlib.Check.CampusTCPRecoveryRoundPhaseReverse
import Netlib.Check.CampusTCPRecoveryRoundRank

/-!
# Selected ordinary steps in a recovery round

Each current phase provides a real step for its primary demand event.
The observed phase has a smaller rank and retains actual evidence.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundSelected

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPRecoveryRoundPhaseBase (config)
open CampusTCPRecoveryRoundEvidence

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Demand nextDemand observe rank_ordinary)
end M
namespace F
export CampusTCPRecoveryRoundPhaseForward (send_at assign_data_at serve_data_at deliver_data_at emit_ack_at)
end F
namespace R
export CampusTCPRecoveryRoundPhaseReverse (assign_ack_at serve_ack_at deliver_ack_at read_at)
end R

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor} {demand : M.Demand}

structure Selected (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (demand : M.Demand) where
  actual : Step input
  move : Move current actual
  event : actual.event = demand.event
  evidence : Nonempty (Evidence initial native quantum move.after
    (M.observe (config initial native quantum) monitor actual))
  decreases : (M.observe (config initial native quantum) monitor actual).rank
    (config initial native quantum) move.after.report.final <
    monitor.rank (config initial native quantum) current.report.final

theorem packetDemand_event (monitor : M.Monitor) (action : CampusTCPRoundMonitor.Action) (packet : Nat) :
    (packetDemand monitor action packet).event = action.event := by
  unfold packetDemand
  split <;> rfl

theorem ordinary_selected (evidence : Evidence initial native quantum current monitor)
    (waiting : monitor.waiting = false)
    (pending : M.nextDemand (config initial native quantum) current.report.final monitor = some demand) :
    Nonempty (Selected initial native quantum current monitor demand) := by
  cases evidence with
  | needSend record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.send_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.dataIngress next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [next.retryCount, record.monitorEq]
        rfl
      · simp only [CampusTCPRoundMonitor.Monitor.rank]
        rw [next.phaseEq, record.monitorEq]
        decide
  | dataIngress record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.assign_data_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.dataTicket next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | dataTicket record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.serve_data_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.dataLink next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | dataLink record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.deliver_data_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.needAck next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | needAck record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.emit_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackIngress next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackIngress record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.assign_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackTicket next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackTicket record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.serve_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackLink next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackLink record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.deliver_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.needRead next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | waiting record =>
    rw [record.waiting] at waiting
    cases waiting
  | needRead record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.read_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.done next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [CampusTCPRoundMonitor.Monitor.rank, next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | done record =>
    rw [record.demand native quantum] at pending
    cases pending

end Netlib.Check.CampusTCPRecoveryRoundSelected
