import Netlib.Check.CampusTCPStartupProfile
import Netlib.Check.CampusTCPStartupTransferExecution

/-!
# Whole-report startup clocks and packet-copy exclusion

The data guard rejects startup clocks and packet copies.
One raw preparation check and whole Actions certificate cover every stored step.
-/

namespace Netlib.Check.CampusTCPStartupActionsProfile

open CampusTCPModel CampusTCPStartupProfile

namespace G
export CampusTCPGapProgressMonitor (Config Monitor Demand serves freeClock clockAllowed)
end G
namespace L
export CampusTCPTwoProgressMonitor (Config Monitor Demand serves servesOption allowed nextDemand freeClock)
end L
namespace X
export CampusTCPTwoExchangeMonitor (Config Monitor allowed)
end X
namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Control allowed drainServes drainTicket controlDemand)
end W
namespace E
export CampusTCPStartupTransferExecution (Monitor allowed actions actions_correct)
end E
namespace M
export CampusTCPStartupTransferMonitor (Config)
end M
namespace B
export CampusTCPStartupClockBounds (ClockGuard Actions)
end B

def DataExcluded : Event → Prop
  | .startupClock _ _ | .copyPacket _ => True
  | _ => False

variable {input : Input} {event : Event} {state : State input}

theorem gap_serves_excluded (demand : G.Demand) (excluded : DataExcluded event) : G.serves demand event = false := by
  cases event <;> simp only [DataExcluded] at excluded
  all_goals cases demand <;> rfl

theorem two_serves_excluded (demand : L.Demand) (excluded : DataExcluded event) : L.serves demand event = false := by
  cases demand with
  | single demand => exact gap_serves_excluded demand excluded
  | originalChoice lower upper =>
    cases lower <;> cases upper <;>
      simp only [L.serves, L.servesOption, gap_serves_excluded _ excluded, Bool.false_or]

theorem gap_free_clock_excluded (config : G.Config) (monitor : G.Monitor) (excluded : DataExcluded event) :
    G.freeClock config state monitor event = false := by
  cases event <;> simp only [DataExcluded] at excluded
  all_goals cases connected : state.connection <;>
    simp only [G.freeClock, G.clockAllowed, CampusTCPRecoveryRoundMonitor.clockAllowed, connected, Bool.false_and]

theorem two_allowed_excluded (config : L.Config) (monitor : L.Monitor) (excluded : DataExcluded event) :
    L.allowed config state monitor event = false := by
  have free : L.freeClock config state monitor event = false :=
    gap_free_clock_excluded config.toConfig { waiting := monitor.waiting } excluded
  have served : ∀ demand, L.serves demand event = false := fun demand => two_serves_excluded demand excluded
  cases event <;> simp only [DataExcluded] at excluded
  all_goals
    unfold L.allowed
    split
    · rfl
    · cases selected : L.nextDemand config state monitor with
      | none => simp only [free, Bool.false_or, Bool.and_true]
      | some demand => simp only [served, free, Bool.false_or, Bool.and_true]

theorem exchange_allowed_excluded (config : X.Config) (monitor : X.Monitor) (excluded : DataExcluded event) :
    X.allowed config state monitor event = false := by
  have forward := two_allowed_excluded (state := state) config.forward monitor.forward excluded
  have reverse := two_allowed_excluded (state := state) (config.reverse monitor.forward.drops.length) monitor.reverse excluded
  cases event <;> simp only [DataExcluded] at excluded
  all_goals cases mode : monitor.mode <;> simp only [X.allowed, mode, forward, reverse]

theorem control_serves_excluded (config : W.Config) (control : W.Control) (excluded : DataExcluded event) :
    CampusTCPTwoTransferMonitor.Control.serves config control event = false := by
  cases event <;> simp only [DataExcluded] at excluded
  all_goals cases control <;> rfl

theorem drain_serves_excluded (ticket : Nat) (excluded : DataExcluded event) : W.drainServes ticket event = false := by
  cases event <;> simp only [DataExcluded] at excluded
  all_goals rfl

theorem data_allowed_excluded (config : W.Config) (monitor : W.Monitor) (excluded : DataExcluded event) :
    W.allowed config state monitor event = false := by
  have exchange := exchange_allowed_excluded (state := state) (config.at state) monitor.exchange excluded
  have controls : ∀ control, CampusTCPTwoTransferMonitor.Control.serves config control event = false :=
    fun control => control_serves_excluded config control excluded
  have drains : ∀ ticket, W.drainServes ticket event = false := fun ticket => drain_serves_excluded ticket excluded
  cases event <;> simp only [DataExcluded] at excluded
  all_goals
    unfold W.allowed
    split
    · rfl
    · cases drained : W.drainTicket state monitor with
      | some ticket => exact drains ticket
      | none =>
        cases selected : W.controlDemand monitor with
        | none => exact exchange
        | some control => exact controls control

variable {config : M.Config} {monitor : E.Monitor input}

theorem allowed_clock (prep : Prep config.startup) (permitted : E.allowed config state monitor event = true) :
    B.ClockGuard config.transfer.quantum state event := by
  cases monitor with
  | startup startup => exact CampusTCPStartupProfile.allowed_clock prep permitted
  | data handoff dataMonitor =>
    cases event <;> first
      | (solve |
        rw [E.allowed, data_allowed_excluded _ _ (by trivial)] at permitted
        cases permitted)
      | cases connected : state.connection <;> simp only [B.ClockGuard, connected]
  | invalid => cases permitted

theorem allowed_no_copy (prep : Prep config.startup) (permitted : E.allowed config state monitor event = true) (id : Nat) :
    event ≠ .copyPacket id := by
  intro same
  subst event
  cases monitor with
  | startup startup => exact CampusTCPStartupProfile.allowed_no_copy prep permitted id rfl
  | data handoff dataMonitor =>
    rw [E.allowed, data_allowed_excluded _ _ (by trivial)] at permitted
    cases permitted
  | invalid => cases permitted

theorem Trace.clock_actions (trace : Trace input initial events steps final remaining) (prep : Prep config.startup)
    (actions : E.actions config initial monitor steps = true) : B.Actions config.transfer.quantum steps := by
  apply (CampusTCPStartupClockBounds.Trace.actions_iff trace).mpr
  intro slot within
  exact allowed_clock prep ((E.actions_correct _ _ _ _).mp actions slot within)

theorem Trace.no_copy (trace : Trace input initial events steps final remaining) (prep : Prep config.startup)
    (actions : E.actions config initial monitor steps = true) : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id := by
  intro actual member id
  obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp member
  have within := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨same, found, before, event, _⟩ := CampusTCPSchedule.Trace.at trace slot within
  have equal : same = actual := Option.some.inj (found.symm.trans selected)
  subst same
  have excluded := allowed_no_copy prep ((E.actions_correct _ _ _ _).mp actions slot within) id
  simpa only [← event] using excluded

theorem Report.clock_actions (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (CampusTCPStartupTransferExecution.initial config) report.steps = true) :
    B.Actions config.transfer.quantum report.steps := Trace.clock_actions report.trace prep actions

theorem Report.no_copy (report : Report input events) (prep : Prep config.startup)
    (actions : E.actions config input.initial (CampusTCPStartupTransferExecution.initial config) report.steps = true) :
    ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id := Trace.no_copy report.trace prep actions

end Netlib.Check.CampusTCPStartupActionsProfile
