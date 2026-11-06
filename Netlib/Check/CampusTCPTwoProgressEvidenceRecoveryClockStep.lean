import Netlib.Check.CampusTCPTwoProgressRecoveryRankClock
import Netlib.Check.CampusTCPTwoProgressRecoveryRankTimer

/-!
# Served and equal-rank recovery clocks

A served clock is the current selected timer tick.
An allowed clock with equal rank retains the exact current demand.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryClockStep

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Config Demand nextDemand observe serves)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand)
end G
namespace K
export CampusTCPTwoProgressRecoveryRank (rank)
end K
namespace F
export CampusTCPTwoProgressMonitorFacts
  (serves_operation serves_resolution serves_tick serves_timeout allowed_iff)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

private theorem mapped_single (values : Option G.Demand) (demand : M.Demand)
    (pending : values.map CampusTCPTwoProgressMonitor.Demand.single = some demand) :
    ∃ raw, demand = .single raw := by
  cases values with
  | none => cases pending
  | some raw => exact ⟨raw, (Option.some.inj pending).symm⟩

private theorem nonoriginal_single (cfg : M.Config) (state : State input) (monitor : M.Monitor)
    (nonoriginal : monitor.mode ≠ .originals) (demand : M.Demand)
    (pending : M.nextDemand cfg state monitor = some demand) : ∃ raw, demand = .single raw := by
  cases mode : monitor.mode with
  | originals => exact False.elim (nonoriginal mode)
  | recovery =>
    simp only [M.nextDemand, mode] at pending
    cases ack : monitor.ack with
    | some lane =>
      simp only [ack] at pending
      exact mapped_single _ demand pending
    | none =>
      simp only [ack] at pending
      split at pending <;> exact mapped_single _ demand pending
  | needRead =>
    simp only [M.nextDemand, mode] at pending
    exact ⟨_, (Option.some.inj pending).symm⟩
  | done | invalid => simp only [M.nextDemand, mode] at pending; cases pending

private theorem served_clock_tick (raw : G.Demand) (actor : Actor) (millis : Nat)
    (served : CampusTCPGapProgressMonitor.serves raw (.advanceClock actor millis) = true) : raw = .tick actor millis := by
  cases raw with
  | operation action =>
    have event := (CampusTCPGapProgressMonitorFacts.serves_operation action (.advanceClock actor millis)).mp served
    cases action <;> cases event
  | resolution action id =>
    rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id (.advanceClock actor millis)).mp served with event | event
    · cases action <;> cases event
    · cases event
  | tick selected time =>
    have same := Event.advanceClock.inj ((CampusTCPGapProgressMonitorFacts.serves_tick selected time (.advanceClock actor millis)).mp served)
    cases same.1
    cases same.2
    rfl
  | timeout selected => cases (CampusTCPGapProgressMonitorFacts.serves_timeout selected (.advanceClock actor millis)).mp served

theorem clock_served_strict (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals) (bound : Nat) (positive : 0 < quantum)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) (demand : M.Demand)
    (pending : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (served : M.serves demand actual.event = true) :
    K.rank (config initial native quantum allowance) bound allowance clocked.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) <
      K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  obtain ⟨raw, same⟩ := nonoriginal_single _ _ _ nonoriginal demand pending
  subst demand
  have tick : raw = .tick actor millis := served_clock_tick raw actor millis (by rw [← clocked.event]; exact served)
  subst raw
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core active =>
    exact CampusTCPTwoProgressRecoveryRankTimer.selected_tick_strict active bound positive clocked allowed pending
  | ready _ ready => simp only [M.nextDemand, ready.mode, Option.some.injEq] at pending; cases pending
  | done done => simp only [M.nextDemand, done.mode] at pending; cases pending

theorem clock_equal_pending (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals) (bound : Nat) (positive : 0 < quantum)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis))
    (equal : K.rank (config initial native quantum allowance) bound allowance clocked.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor actual) =
      K.rank (config initial native quantum allowance) bound allowance current.report.final monitor) :
    M.nextDemand (config initial native quantum allowance) clocked.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor actual) =
      M.nextDemand (config initial native quantum allowance) current.report.final monitor := by
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    have strict := clock_served_strict value nonoriginal bound positive clocked allowed demand pending
      (by rw [clocked.event]; exact served)
    rw [equal] at strict
    exact False.elim (Nat.lt_irrefl _ strict)
  · obtain ⟨id, _, event, _⟩ := dropped
    cases event
  · exact CampusTCPTwoProgressRecoveryRankClock.free_clock_pending value nonoriginal clocked allowed free

end Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryClockStep
