import Netlib.Check.CampusTCPGapProgressDemand
import Netlib.Check.CampusTCPGapProgressPhaseForward
import Netlib.Check.CampusTCPGapProgressPhaseReverse
import Netlib.Check.CampusTCPGapProgressRank

/-!
# Selected ordinary steps in a held-gap task

Each current phase provides a real step for its primary demand event.
The observed phase has a smaller rank and retains actual evidence.
-/

namespace Netlib.Check.CampusTCPGapProgressSelected

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressWire (Geometry)
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPGapProgressSetup (config)
open CampusTCPGapProgressEvidence

namespace M
export CampusTCPGapProgressMonitor (Monitor Demand nextDemand observe rank_ordinary)
end M
namespace F
export CampusTCPGapProgressPhaseForward (assign_data_at serve_data_at deliver_data_at emit_ack_at)
end F
namespace R
export CampusTCPGapProgressPhaseReverse (assign_ack_at serve_ack_at deliver_ack_at read_at)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {quantum allowance : Nat} {monitor : M.Monitor} {demand : M.Demand}

structure Selected (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (quantum allowance : Nat) (current : Cut input complete) (monitor : M.Monitor) (demand : M.Demand) where
  actual : Step input
  move : Move current actual
  event : actual.event = demand.event
  evidence : Nonempty (Evidence initial native allowance move.after
    (M.observe (config initial native quantum allowance) monitor actual))
  decreases : (M.observe (config initial native quantum allowance) monitor actual).rank
    (config initial native quantum allowance) move.after.report.final <
    monitor.rank (config initial native quantum allowance) current.report.final

theorem ordinary_selected (wire : Geometry initial) (evidence : Evidence initial native allowance current monitor)
    (waiting : monitor.waiting = false)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    Nonempty (Selected initial native quantum allowance current monitor demand) := by
  cases evidence with
  | dataIngress record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.assign_data_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.dataTicket next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | dataTicket record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.serve_data_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.dataLink next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | dataLink record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.deliver_data_at wire native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.needAck next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | needAck record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := F.emit_ack_at wire native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackIngress next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackIngress record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.assign_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackTicket next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackTicket record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.serve_ack_at native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.ackLink next⟩, ?_⟩⟩
    · rw [selected]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
          CampusTCPRoundMonitor.Phase.rank]
        decide
  | ackLink record =>
    have selected := Option.some.inj (pending.symm.trans (record.demand native quantum))
    obtain ⟨actual, move, event, ⟨next⟩⟩ := R.deliver_ack_at wire native quantum record
    refine ⟨⟨actual, move, ?_, ⟨.needRead next⟩, ?_⟩⟩
    · rw [selected, packetDemand_event]
      exact event
    · apply M.rank_ordinary _ _ _ _ _ waiting next.waiting
      · rw [record.phaseEq]; decide
      · rw [record.phaseEq]; decide
      · exact next.retryCount.trans record.retryCount.symm
      · simp only [next.phaseEq, record.phaseEq,
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
    · simp only [CampusTCPGapProgressMonitor.Monitor.rank, waiting, next.waiting,
        Bool.false_eq_true, ite_false, record.phaseEq, next.phaseEq]
      decide
  | done record =>
    rw [record.demand native quantum] at pending
    cases pending

end Netlib.Check.CampusTCPGapProgressSelected
