import Netlib.Check.CampusTCPTwoTransferOriginalRankEvents
import Netlib.Check.CampusTCPTwoTransferOriginalRankFrames

namespace Netlib.Check.CampusTCPTwoTransferOriginalRankStep

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)

namespace R
export CampusTCPTwoTransferOriginalRank
  (rank clock_same clock_pending control_strict drain_strict ordinary_nonincrease ordinary_equal_clock)
end R
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe controlDemand drainTicket nextDemand serves)
end W
namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand serves)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem no_drain (state : State input) (monitor : W.Monitor) (ordinary : W.controlDemand monitor = none) :
    W.drainTicket state monitor = none := by
  cases selected : W.drainTicket state monitor with
  | none => rfl
  | some ticket =>
    have mode := CampusTCPTwoTransferControlBound.drain_mode selected
    simp only [W.controlDemand, mode] at ordinary
    cases ordinary

private theorem drain_strict_at
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : Move current actual) (selected : W.drainTicket current.report.final monitor = some ticket)
    (event : actual.event = .serve ticket none) :
    R.rank move.after.report.final (W.observe cfg monitor actual) < R.rank current.report.final monitor := by
  have locationEq := evidence.drain_location selected
  subst location
  have scopeBefore := evidence.drain_scope selected
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    have empty : current.report.final.outstanding .primary = 0 :=
      state.core.primaryQueue.no_tickets_zero (CampusTCPOrigins.Report.work_valid current.report)
        (by rw [state.lowerPending]; decide) (by rw [state.upperPending]; decide)
    have absent := CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero current.report.final monitor empty
    rw [absent] at selected
    cases selected
  | pending state =>
    have absent := CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero current.report.final monitor state.primary_empty
    rw [absent] at selected
    cases selected
  | active state =>
    obtain ⟨value⟩ := CampusTCPTwoTransferDrainProgress.drain_step state controls scopeBefore.mode scopeBefore.resolved
      selected actual move.beforeEq event
    have strict := R.drain_strict ⟨sent, received, core, .active state, controls, scope, armed, recorded⟩ value selected
    simpa only [value.value.value.value.move.final, move.final] using strict
  | readable _ _ mode _ _ _ =>
    have impossible := scopeBefore.mode
    rw [mode] at impossible
    cases impossible

private theorem control_region
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : Move current actual) (selected : W.controlDemand monitor = some kind)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    (∃ actor millis, actual.event = .advanceClock actor millis) ∨
      R.rank move.after.report.final (W.observe cfg monitor actual) < R.rank current.report.final monitor := by
  cases event : actual.event
  all_goals first
    | exact Or.inl ⟨_, _, rfl⟩
    | (
      apply Or.inr
      cases drain : W.drainTicket current.report.final monitor with
      | some ticket =>
        have served : CampusTCPTwoTransferMonitor.drainServes ticket actual.event = true := by
          simpa [W.Allowed, CampusTCPTwoTransferMonitor.allowed, evidence.healthy, drain, event] using allowed
        exact drain_strict_at evidence move drain (CampusTCPTwoTransferControlBound.drain_serves_event.mp served)
      | none =>
        have served : kind.serves cfg actual.event = true := by
          simpa [W.Allowed, CampusTCPTwoTransferMonitor.allowed, evidence.healthy, drain, selected, event] using allowed
        obtain ⟨value⟩ := CampusTCPTwoTransferControlState.Step.control evidence.core evidence.controls selected drain actual
          move.beforeEq ((CampusTCPTwoTransferControlBound.serves_control_event actual.event).mp served)
        have strict := R.control_strict evidence value.value selected drain
        simpa only [value.value.move.final, move.final] using strict)

theorem nonincrease
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    R.rank move.after.report.final (W.observe cfg monitor actual) ≤ R.rank current.report.final monitor := by
  cases selected : W.controlDemand monitor with
  | none => exact R.ordinary_nonincrease evidence move (no_drain _ _ selected) selected allowed
  | some kind =>
    rcases control_region evidence move selected allowed with ⟨actor, millis, event⟩ | strict
    · obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock evidence.core evidence.forward.exchange
        evidence.forward.not_done actual move.beforeEq event (by rw [← event]; exact allowed)
      have same := R.clock_same evidence clocked
      rw [clocked.move.final, ← move.final] at same
      exact Nat.le_of_eq same
    · exact Nat.le_of_lt strict

theorem equal_clock
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (equal : R.rank move.after.report.final (W.observe cfg monitor actual) = R.rank current.report.final monitor) :
    ∃ actor millis, actual.event = .advanceClock actor millis ∧
      W.nextDemand cfg move.after.report.final (W.observe cfg monitor actual) = W.nextDemand cfg current.report.final monitor := by
  cases selected : W.controlDemand monitor with
  | none => exact R.ordinary_equal_clock evidence mode move (no_drain _ _ selected) selected allowed equal
  | some kind =>
    rcases control_region evidence move selected allowed with ⟨actor, millis, event⟩ | strict
    · obtain ⟨clocked⟩ := CampusTCPTwoTransferLocatedClock.Step.clock evidence.core evidence.forward.exchange
        evidence.forward.not_done actual move.beforeEq event (by rw [← event]; exact allowed)
      refine ⟨actor, millis, event, ?_⟩
      have same := R.clock_pending evidence clocked mode
      rw [clocked.move.final, ← move.final] at same
      exact same
    · omega

theorem persistent
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (equal : R.rank move.after.report.final (W.observe cfg monitor actual) = R.rank current.report.final monitor)
    (demand : CampusTCPTwoTransferMonitor.Demand) (pending : W.nextDemand cfg current.report.final monitor = some demand) :
    W.nextDemand cfg move.after.report.final (W.observe cfg monitor actual) = some demand := by
  obtain ⟨_, _, _, same⟩ := equal_clock evidence mode move allowed equal
  exact same.trans pending

private theorem action_not_clock (action : CampusTCPRoundMonitor.Action) (actor : Actor) (millis : Nat) :
    Event.advanceClock actor millis ≠ action.event := by
  cases action <;> intro impossible <;> cases impossible

private theorem lane_not_clock (config : M.Config) (state : State input) (monitor : M.Monitor)
    (lane : M.Lane) (selected : M.laneDemand config state monitor lane = some demand)
    (served : CampusTCPGapProgressMonitor.serves demand (.advanceClock actor millis) = true) : False := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ :=
    CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  · exact action_not_clock action actor millis
      ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp (operation ▸ served))
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp (resolution ▸ served) with same | drop
    · exact action_not_clock action actor millis same
    · cases drop

private theorem local_not_clock (config : M.Config) (state : State input) (monitor : M.Monitor)
    (mode : monitor.mode = .originals) (pending : M.nextDemand config state monitor = some demand)
    (served : M.serves demand (.advanceClock actor millis) = true) : False := by
  simp only [M.nextDemand, mode] at pending
  split at pending
  · cases pending; cases served
  · split at pending
    · cases pending; cases served
    · cases ack : monitor.ack with
      | some lane =>
        simp only [ack] at pending
        cases selected : M.laneDemand config state monitor lane with
        | none => simp only [selected, Option.map_none] at pending; cases pending
        | some laneDemand =>
          simp only [selected, Option.map_some] at pending
          cases pending
          exact lane_not_clock config state monitor lane selected served
      | none =>
        simp only [ack] at pending
        split at pending
        · cases pending
          rcases CampusTCPTwoProgressMonitorFacts.originalChoice_branch _ _ _ served with lower | upper
          · obtain ⟨laneDemand, selected, served⟩ := lower
            exact lane_not_clock config state monitor monitor.lower selected served
          · obtain ⟨laneDemand, selected, served⟩ := upper
            exact lane_not_clock config state monitor monitor.upper selected served
        · cases pending

private theorem pending_clock_false (config : CampusTCPTwoTransferMonitor.Config) (state : State input)
    (monitor : W.Monitor) (valid : monitor.mode ≠ .invalid) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .originals) (pending : W.nextDemand config state monitor = some demand) :
    W.serves config demand (.advanceClock actor millis) = false := by
  apply Bool.eq_false_iff.mpr
  intro served
  simp only [W.nextDemand, valid, decide_false, Bool.false_eq_true, ite_false] at pending
  cases drain : W.drainTicket state monitor with
  | some ticket => rw [drain] at pending; cases pending; cases served
  | none =>
    rw [drain] at pending
    cases control : W.controlDemand monitor with
    | some kind => rw [control] at pending; cases pending; cases kind <;> cases served
    | none =>
      rw [control] at pending
      cases next : M.nextDemand (config.at state).forward state monitor.exchange.forward with
      | none =>
        simp only [CampusTCPTwoExchangeMonitor.nextDemand, forward, next, Option.map_none] at pending
        cases pending
      | some selected =>
        simp only [CampusTCPTwoExchangeMonitor.nextDemand, forward, next, Option.map_some] at pending
        cases pending
        exact local_not_clock (config.at state).forward state monitor.exchange.forward mode next served

theorem served_strict
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (demand : CampusTCPTwoTransferMonitor.Demand) (pending : W.nextDemand cfg current.report.final monitor = some demand)
    (served : W.serves cfg demand actual.event = true) :
    R.rank move.after.report.final (W.observe cfg monitor actual) < R.rank current.report.final monitor := by
  have bound := nonincrease evidence move allowed
  by_cases strict : R.rank move.after.report.final (W.observe cfg monitor actual) < R.rank current.report.final monitor
  · exact strict
  · have equal : R.rank move.after.report.final (W.observe cfg monitor actual) = R.rank current.report.final monitor := by omega
    obtain ⟨actor, millis, event, _⟩ := equal_clock evidence mode move allowed equal
    rw [event, pending_clock_false cfg current.report.final monitor evidence.healthy evidence.forward.exchange mode pending] at served
    cases served

end Netlib.Check.CampusTCPTwoTransferOriginalRankStep
