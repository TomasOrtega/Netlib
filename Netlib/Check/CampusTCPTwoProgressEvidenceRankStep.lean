import Netlib.Check.CampusTCPTwoProgressEvidenceOriginalRank
import Netlib.Check.CampusTCPTwoProgressClock

/-!
# Actual rank steps for the original paths

Ordinary actions and drops reduce the current original rank.
An equal-rank allowed step is a clock and retains the current demand.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

namespace RankM
export CampusTCPTwoProgressMonitor (Config Monitor Demand nextDemand laneDemand serves observe dropTarget Allowed)
end RankM
namespace RankF
export CampusTCPTwoProgressMonitorFacts
  (laneDemand_action serves_operation originalChoice_branch allowed_iff freeClock_event observe_drop)
end RankF

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : RankM.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

private def OrdinaryOrDrop (event : Event) : Prop :=
  (∃ action : CampusTCPRoundMonitor.Action, event = action.event) ∨ ∃ id, event = .dropPacket id

private theorem lane_event (cfg : RankM.Config) (state : State input) (monitor : RankM.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (demand : CampusTCPGapProgressMonitor.Demand)
    (pending : RankM.laneDemand cfg state monitor lane = some demand)
    (served : CampusTCPGapProgressMonitor.serves demand event = true) : OrdinaryOrDrop event := by
  obtain ⟨action, _, kind⟩ := RankF.laneDemand_action cfg state monitor lane pending
  rcases kind with kind | ⟨id, kind⟩
  · cases kind
    exact .inl ⟨action, (CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served⟩
  · cases kind
    rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with ordinary | dropped
    · exact .inl ⟨action, ordinary⟩
    · exact .inr ⟨id, dropped⟩

private theorem mapped_lane_event (cfg : RankM.Config) (state : State input) (monitor : RankM.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : (RankM.laneDemand cfg state monitor lane).map CampusTCPTwoProgressMonitor.Demand.single = some demand)
    (served : RankM.serves demand event = true) : OrdinaryOrDrop event := by
  cases found : RankM.laneDemand cfg state monitor lane with
  | none => rw [found] at pending; cases pending
  | some raw =>
    have same : CampusTCPTwoProgressMonitor.Demand.single raw = demand := by
      simpa only [found, Option.map_some, Option.some.injEq] using pending
    cases same
    exact lane_event cfg state monitor lane raw found served

private theorem original_event (cfg : RankM.Config) (state : State input) (monitor : RankM.Monitor)
    (mode : monitor.mode = .originals) (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : RankM.nextDemand cfg state monitor = some demand) (served : RankM.serves demand event = true) :
    OrdinaryOrDrop event := by
  simp only [RankM.nextDemand, mode] at pending
  split at pending
  · have same : demand = .single (.operation (.send cfg.sender cfg.lowerCount true)) := (Option.some.inj pending).symm
    cases same
    exact .inl ⟨.send cfg.sender cfg.lowerCount true, (RankF.serves_operation _ _).mp served⟩
  · split at pending
    · have same : demand = .single (.operation (.send cfg.sender cfg.upperCount true)) := (Option.some.inj pending).symm
      cases same
      exact .inl ⟨.send cfg.sender cfg.upperCount true, (RankF.serves_operation _ _).mp served⟩
    · cases ack : monitor.ack with
      | some lane =>
        simp only [ack] at pending
        exact mapped_lane_event cfg state monitor lane demand pending served
      | none =>
        simp only [ack] at pending
        split at pending
        · have same : demand = .originalChoice (RankM.laneDemand cfg state monitor monitor.lower)
              (RankM.laneDemand cfg state monitor monitor.upper) := (Option.some.inj pending).symm
          cases same
          rcases RankF.originalChoice_branch _ _ _ served with ⟨raw, found, selected⟩ | ⟨raw, found, selected⟩
          · exact lane_event cfg state monitor monitor.lower raw found selected
          · exact lane_event cfg state monitor monitor.upper raw found selected
        · cases pending

private theorem lane_frame (clocked : CampusTCPTwoProgressClock.Clocked cut current cfg monitor actor millis actual)
    (lane : CampusTCPTwoProgressMonitor.Lane) :
    RankM.laneDemand cfg clocked.move.after.report.final monitor lane = RankM.laneDemand cfg current.report.final monitor lane := by
  unfold RankM.laneDemand
  rw [CampusTCPGapProgressMonitorFacts.Frame.nextAction clocked.placement.frame cfg.toConfig lane.toGap]

theorem original_clock_pending (clocked : CampusTCPTwoProgressClock.Clocked cut current cfg monitor actor millis actual)
    (mode : monitor.mode = .originals) :
    RankM.nextDemand cfg clocked.move.after.report.final (RankM.observe cfg monitor actual) =
      RankM.nextDemand cfg current.report.final monitor := by
  rw [clocked.observed]
  simp only [RankM.nextDemand, mode]
  split
  · rfl
  · split
    · rfl
    · cases ack : monitor.ack with
      | none => dsimp only; rw [lane_frame clocked monitor.lower, lane_frame clocked monitor.upper]
      | some lane => dsimp only; rw [lane_frame clocked lane]

theorem Evidence.original_step_nonincrease (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (actual : Step input) :
    CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) ≤
      CampusTCPTwoProgressOriginalRank.originalRank monitor :=
  CampusTCPTwoProgressOriginalRank.observe_nonincrease _ _ actual (value.original_shape mode)

theorem Evidence.original_action_strict (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (move : Move current actual)
    (allowed : RankM.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) :
    CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) <
      CampusTCPTwoProgressOriginalRank.originalRank monitor := by
  obtain ⟨demand, pending⟩ := value.original_pending mode
  exact CampusTCPTwoProgressOriginalRank.action_strict _ _ actual (value.original_shape mode) mode
    (by rw [move.beforeEq]; exact pending) move.supported move.passed
    (by rw [move.beforeEq]; exact allowed) action event

theorem Evidence.original_drop_strict (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (move : Move current actual)
    (allowed : RankM.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (id : Nat) (event : actual.event = .dropPacket id) :
    CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) <
      CampusTCPTwoProgressOriginalRank.originalRank monitor := by
  cases target : RankM.dropTarget (config initial native quantum allowance) current.report.final monitor id with
  | none =>
    rw [RankF.observe_drop _ _ _ move.supported move.passed (by rw [move.beforeEq]; exact allowed) event]
    simp only [CampusTCPTwoProgressMonitor.observeDrop, move.beforeEq, target,
      CampusTCPTwoProgressOriginalRank.invalid_rank]
    exact value.original_positive mode
  | some selected =>
    exact CampusTCPTwoProgressOriginalRank.observed_drop_strict _ _ actual id (value.original_shape mode) mode
      (by rw [move.beforeEq]; exact target) move.supported move.passed
      (by rw [move.beforeEq]; exact allowed) event

theorem Evidence.original_served_strict (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (move : Move current actual)
    (allowed : RankM.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : RankM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (served : RankM.serves demand actual.event = true) :
    CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) <
      CampusTCPTwoProgressOriginalRank.originalRank monitor := by
  rcases original_event _ _ _ mode demand pending served with ⟨action, event⟩ | ⟨id, event⟩
  · exact value.original_action_strict mode move allowed action event
  · exact value.original_drop_strict mode move allowed id event

theorem Evidence.original_equal_clock (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (move : Move current actual)
    (allowed : RankM.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (equal : CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) =
      CampusTCPTwoProgressOriginalRank.originalRank monitor) :
    ∃ actor millis, actual.event = .advanceClock actor millis ∧
      RankM.nextDemand (config initial native quantum allowance) move.after.report.final
        (RankM.observe (config initial native quantum allowance) monitor actual) =
          RankM.nextDemand (config initial native quantum allowance) current.report.final monitor := by
  obtain ⟨_, selected | dropped | free, _⟩ := (RankF.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    rcases original_event _ _ _ mode demand pending served with ⟨action, event⟩ | ⟨id, event⟩
    · have strict := value.original_action_strict mode move allowed action event
      rw [equal] at strict
      exact False.elim (Nat.lt_irrefl _ strict)
    · have strict := value.original_drop_strict mode move allowed id event
      rw [equal] at strict
      exact False.elim (Nat.lt_irrefl _ strict)
  · obtain ⟨id, target, event, _⟩ := dropped
    have strict := value.original_drop_strict mode move allowed id event
    rw [equal] at strict
    exact False.elim (Nat.lt_irrefl _ strict)
  · obtain ⟨actor, millis, event, _⟩ := RankF.freeClock_event _ _ _ _ free
    obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual value.anchor (config initial native quantum allowance) monitor actor millis
      move.beforeEq event (by rw [← event]; exact allowed)
    refine ⟨actor, millis, event, ?_⟩
    have pending := original_clock_pending clocked mode
    rw [clocked.move.final] at pending
    rw [move.final]
    exact pending

theorem Evidence.original_persistent (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) (move : Move current actual)
    (allowed : RankM.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (equal : CampusTCPTwoProgressOriginalRank.originalRank (RankM.observe (config initial native quantum allowance) monitor actual) =
      CampusTCPTwoProgressOriginalRank.originalRank monitor)
    (demand : CampusTCPTwoProgressMonitor.Demand)
    (pending : RankM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    RankM.nextDemand (config initial native quantum allowance) move.after.report.final
      (RankM.observe (config initial native quantum allowance) monitor actual) = some demand := by
  obtain ⟨_, _, _, same⟩ := value.original_equal_clock mode move allowed equal
  exact same.trans pending

end Netlib.Check.CampusTCPTwoProgressEvidence
