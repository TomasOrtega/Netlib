import Netlib.Check.CampusTCPTwoTransferRecoveryRankTimer
import Netlib.Check.CampusTCPTwoTransferNonoriginal

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRankClockStep

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferLocatedClock (Clocked)

namespace R
export CampusTCPTwoTransferRecoveryRank (rank)
end R
namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Demand nextDemand serves)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand)
end G
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe nextDemand serves)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem mapped_single (values : Option G.Demand) (demand : M.Demand)
    (pending : values.map CampusTCPTwoProgressMonitor.Demand.single = some demand) : ∃ raw, demand = .single raw := by
  cases values with
  | none => cases pending
  | some raw => exact ⟨raw, (Option.some.inj pending).symm⟩

private theorem nonoriginal_single (packetConfig : M.Config) (state : State input) (monitor : M.Monitor)
    (nonoriginal : monitor.mode ≠ .originals) (demand : M.Demand)
    (pending : M.nextDemand packetConfig state monitor = some demand) : ∃ raw, demand = .single raw := by
  cases mode : monitor.mode with
  | originals => exact False.elim (nonoriginal mode)
  | recovery =>
    simp only [M.nextDemand, mode] at pending
    cases ack : monitor.ack with
    | some lane => simp only [ack] at pending; exact mapped_single _ demand pending
    | none => simp only [ack] at pending; split at pending <;> exact mapped_single _ demand pending
  | needRead => simp only [M.nextDemand, mode] at pending; exact ⟨_, (Option.some.inj pending).symm⟩
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

private theorem local_served_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (bound : Nat) (positive : 0 < quantum)
    (clocked : Clocked value.core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis)) (demand : M.Demand)
    (pending : M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward = some demand)
    (served : M.serves demand actual.event = true) :
    R.rank cfg bound allowance clocked.move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg bound allowance current.report.final monitor := by
  obtain ⟨raw, same⟩ := nonoriginal_single _ _ _ nonoriginal demand pending
  subst demand
  have tick : raw = .tick actor millis := served_clock_tick raw actor millis (by rw [← clocked.event]; exact served)
  subst raw
  rcases value with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active active =>
    exact CampusTCPTwoTransferRecoveryRankTimer.selected_tick_strict active (active.mode.resolve_left nonoriginal)
      bound positive clocked allowed pending
  | readable _ _ mode _ _ _ =>
    simp only [M.nextDemand, mode, Option.some.injEq] at pending
    cases pending

theorem served_strict
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (bound : Nat) (positive : 0 < quantum)
    (clocked : Clocked value.core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (demand : CampusTCPTwoTransferMonitor.Demand) (pending : W.nextDemand cfg current.report.final monitor = some demand)
    (served : W.serves cfg demand actual.event = true) :
    R.rank cfg bound allowance clocked.move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg bound allowance current.report.final monitor := by
  obtain ⟨control, drained⟩ := CampusTCPTwoTransferNonoriginal.ordinary value nonoriginal
  simp only [W.nextDemand, value.healthy, decide_false, Bool.false_eq_true, ite_false, drained, control,
    CampusTCPTwoExchangeMonitor.nextDemand, value.forward.exchange] at pending
  cases found : M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward with
  | none => rw [found] at pending; cases pending
  | some selected =>
    simp only [found, Option.map_some] at pending
    cases pending
    exact local_served_strict value nonoriginal bound positive clocked allowed selected found served

theorem equal_pending
    (value : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (bound : Nat) (positive : 0 < quantum)
    (clocked : Clocked value.core actor millis actual)
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (equal : R.rank cfg bound allowance clocked.move.after.report.final (W.observe cfg monitor actual) =
      R.rank cfg bound allowance current.report.final monitor) :
    W.nextDemand cfg clocked.move.after.report.final (W.observe cfg monitor actual) = W.nextDemand cfg current.report.final monitor := by
  have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed value nonoriginal (by rw [clocked.event]; exact allowed)
  obtain ⟨_, selected | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp localAllowed
  · obtain ⟨demand, pending, served⟩ := selected
    have strict := local_served_strict value nonoriginal bound positive clocked allowed demand pending served
    rw [equal] at strict
    exact False.elim (Nat.lt_irrefl _ strict)
  · obtain ⟨id, _, event, _⟩ := dropped
    rw [clocked.event] at event
    cases event
  · exact CampusTCPTwoTransferRecoveryRankClock.free_pending value nonoriginal clocked allowed (by rw [clocked.event] at free; exact free)

end Netlib.Check.CampusTCPTwoTransferRecoveryRankClockStep
