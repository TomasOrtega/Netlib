import Netlib.Check.CampusTCPTwoTransferOriginalRankOrdinary
import Netlib.Check.CampusTCPTwoTransferOriginalRankPending
import Netlib.Check.CampusTCPTwoTransferEvidenceDrop

/-!
# Original rank and actual ordinary events

An actual action or selected drop reduces the current rank.
An allowed step with equal positive rank is a clock and keeps its demand.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)

namespace E
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand serves dropTarget)
end E
namespace F
export CampusTCPTwoProgressMonitorFacts (laneDemand_action originalChoice_branch allowed_iff freeClock_event)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : T.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private def OrdinaryOrDrop (event : Event) : Prop :=
  (∃ action : CampusTCPRoundMonitor.Action, event = action.event) ∨ ∃ id, event = .dropPacket id

private theorem lane_event (packetConfig : E.Config) (state : State input) (value : E.Monitor)
    (lane : E.Lane) (demand : CampusTCPGapProgressMonitor.Demand)
    (pending : E.laneDemand packetConfig state value lane = some demand)
    (served : CampusTCPGapProgressMonitor.serves demand event = true) : OrdinaryOrDrop event := by
  obtain ⟨action, _, kind⟩ := F.laneDemand_action packetConfig state value lane pending
  rcases kind with kind | ⟨id, kind⟩
  · cases kind
    exact .inl ⟨action, (CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served⟩
  · cases kind
    rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with ordinary | dropped
    · exact .inl ⟨action, ordinary⟩
    · exact .inr ⟨id, dropped⟩

private theorem mapped_lane_event (packetConfig : E.Config) (state : State input) (value : E.Monitor)
    (lane : E.Lane) (demand : E.Demand)
    (pending : (E.laneDemand packetConfig state value lane).map CampusTCPTwoProgressMonitor.Demand.single = some demand)
    (served : E.serves demand event = true) : OrdinaryOrDrop event := by
  cases found : E.laneDemand packetConfig state value lane with
  | none => rw [found] at pending; cases pending
  | some raw =>
    have same : CampusTCPTwoProgressMonitor.Demand.single raw = demand := by simpa only [found, Option.map_some, Option.some.injEq] using pending
    cases same
    exact lane_event packetConfig state value lane raw found served

private theorem original_event (packetConfig : E.Config) (state : State input) (value : E.Monitor)
    (mode : value.mode = .originals) (demand : E.Demand)
    (pending : E.nextDemand packetConfig state value = some demand) (served : E.serves demand event = true) :
    OrdinaryOrDrop event := by
  simp only [E.nextDemand, mode] at pending
  split at pending
  · have same : demand = .single (.operation (.send packetConfig.sender packetConfig.lowerCount true)) := (Option.some.inj pending).symm
    cases same
    exact .inl ⟨.send packetConfig.sender packetConfig.lowerCount true,
      (CampusTCPTwoProgressMonitorFacts.serves_operation _ _).mp served⟩
  · split at pending
    · have same : demand = .single (.operation (.send packetConfig.sender packetConfig.upperCount true)) := (Option.some.inj pending).symm
      cases same
      exact .inl ⟨.send packetConfig.sender packetConfig.upperCount true,
        (CampusTCPTwoProgressMonitorFacts.serves_operation _ _).mp served⟩
    · cases ack : value.ack with
      | some lane =>
        simp only [ack] at pending
        exact mapped_lane_event packetConfig state value lane demand pending served
      | none =>
        simp only [ack] at pending
        split at pending
        · have same : demand = .originalChoice (E.laneDemand packetConfig state value value.lower)
              (E.laneDemand packetConfig state value value.upper) := (Option.some.inj pending).symm
          cases same
          rcases F.originalChoice_branch _ _ _ served with ⟨raw, found, selected⟩ | ⟨raw, found, selected⟩
          · exact lane_event packetConfig state value value.lower raw found selected
          · exact lane_event packetConfig state value value.upper raw found selected
        · cases pending

private theorem local_allowed
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : Move current actual) (drainless : T.drainTicket current.report.final monitor = none)
    (control : T.controlDemand monitor = none) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    CampusTCPTwoProgressMonitor.Allowed ((cfg).at actual.before).forward actual.before monitor.exchange.forward actual.event := by
  have ordinary := ordinary_allowed evidence.healthy drainless control allowed
  simpa only [X.Allowed, CampusTCPTwoExchangeMonitor.allowed, evidence.forward.exchange,
    CampusTCPTwoProgressMonitor.Allowed, move.beforeEq] using ordinary

theorem ordinary_drop_strict
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (drainless : T.drainTicket current.report.final monitor = none) (control : T.controlDemand monitor = none)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) (id : Nat) (event : actual.event = .dropPacket id) :
    rank move.after.report.final (T.observe cfg monitor actual) < rank current.report.final monitor := by
  have localAllowed := local_allowed evidence move drainless control allowed
  obtain ⟨target, selected⟩ := CampusTCPTwoTransferEvidence.local_allowed_drop_target _ _ _ (by rw [← event]; exact localAllowed)
  have strict := CampusTCPTwoProgressOriginalRank.observed_drop_strict ((cfg).at actual.before).forward
    monitor.exchange.forward actual id (shape evidence mode) mode selected move.supported move.passed localAllowed event
  have positive := positive evidence mode
  rcases ordinary_frame move evidence.healthy evidence.forward.exchange drainless control allowed with invalid | ⟨sameMode, sameForward⟩
  · simpa only [rank, invalid, ne_eq, not_true_eq_false, false_and, ite_false] using positive
  · have reserveEq : reserve move.after.report.final (T.observe cfg monitor actual) = reserve current.report.final monitor := by
      rcases evidence.controls.ordinary_modes control with armed | finished
      · simp only [reserve, sameMode, armed]
      · simp only [reserve, sameMode, finished]
    rw [current_rank evidence mode]
    unfold rank
    split
    · rw [sameForward, reserveEq]
      omega
    · have original := local_positive evidence mode
      omega

theorem ordinary_equal_clock
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (drainless : T.drainTicket current.report.final monitor = none) (control : T.controlDemand monitor = none)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (equal : rank move.after.report.final (T.observe cfg monitor actual) = rank current.report.final monitor) :
    ∃ actor millis, actual.event = .advanceClock actor millis ∧
      T.nextDemand cfg move.after.report.final (T.observe cfg monitor actual) = T.nextDemand cfg current.report.final monitor := by
  have localAllowed := local_allowed evidence move drainless control allowed
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp localAllowed
  · obtain ⟨demand, pending, served⟩ := selected
    rcases original_event _ _ _ mode demand pending served with ⟨action, event⟩ | ⟨id, event⟩
    · have strict := ordinary_action_strict evidence mode move drainless control allowed pending action event
      omega
    · have strict := ordinary_drop_strict evidence mode move drainless control allowed id event
      omega
  · obtain ⟨id, target, event, _⟩ := dropped
    have strict := ordinary_drop_strict evidence mode move drainless control allowed id event
    omega
  · obtain ⟨actor, millis, event, _⟩ := F.freeClock_event _ _ _ _ free
    obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock evidence.core evidence.forward.exchange
      evidence.forward.not_done actual move.beforeEq event (by rw [← event]; exact allowed)
    refine ⟨actor, millis, event, ?_⟩
    have same := clock_pending evidence clocked mode
    rw [clocked.move.final] at same
    rw [move.final]
    exact same

end Netlib.Check.CampusTCPTwoTransferOriginalRank
