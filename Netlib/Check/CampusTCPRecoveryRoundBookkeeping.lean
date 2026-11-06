import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPRecoveryRoundServiceBound

namespace Netlib.Check.CampusTCPRecoveryRoundBookkeeping

open CampusTCPModel CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPRecoveryRoundEvidence (Evidence DropLog dropID)

namespace M
export CampusTCPRecoveryRoundMonitor (Config Monitor Demand observe serves Allowed)
end M

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
variable {current : Cut input complete} {monitor nextMonitor : M.Monitor} {actual : Step input}

theorem count_dropID (steps : List (Step input)) :
    steps.countP (fun actual => CampusTCPCustodyFacts.dropEvent actual.event) = (steps.filterMap dropID).length := by
  induction steps with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.countP_cons, List.filterMap_cons]
    rw [ih]
    cases event : head.event <;> simp [dropID, CampusTCPCustodyFacts.dropEvent, event]

theorem DropLog.drop_count (log : DropLog initial current ids) :
    current.report.final.custody.dropped = initial.state.custody.dropped + ids.length := by
  obtain ⟨suffix, history, drops⟩ := log
  rw [CampusTCPCustodyFacts.Report.drop_count current.report, history, List.countP_append,
    ← CampusTCPCustodyFacts.Report.drop_count initial.start.next.report, count_dropID, drops]
  rfl

theorem Evidence.drop_count (evidence : Evidence initial native quantum current monitor) :
    current.report.final.custody.dropped = initial.state.custody.dropped + monitor.drops.length :=
  DropLog.drop_count evidence.drop_log

theorem Evidence.drop_budget (evidence : Evidence initial native quantum current monitor) :
    current.report.final.custody.dropped ≤ initial.state.custody.dropped + 2 := by
  rw [Evidence.drop_count evidence]
  exact Nat.add_le_add_left evidence.drop_bound _

theorem Evidence.drop_mono (evidence : Evidence initial native quantum current monitor) :
    initial.state.custody.dropped ≤ current.report.final.custody.dropped := by
  rw [Evidence.drop_count evidence]
  exact Nat.le_add_right _ _

theorem Evidence.drop_delta (evidence : Evidence initial native quantum current monitor) :
    current.report.final.custody.dropped - initial.state.custody.dropped = monitor.drops.length := by
  rw [Evidence.drop_count evidence, Nat.add_sub_cancel_left]

theorem Step.drop_count (before : Evidence initial native quantum current monitor) (move : Move current actual)
    (after : Evidence initial native quantum move.after nextMonitor) :
    nextMonitor.drops.length = monitor.drops.length + if CampusTCPCustodyFacts.dropEvent actual.event then 1 else 0 := by
  have first := Evidence.drop_count before
  have last := Evidence.drop_count after
  have changed := CampusTCPCustodyFacts.Step.drop_count actual
  rw [move.beforeEq, ← move.final] at changed
  omega

theorem Step.drop_mono (before : Evidence initial native quantum current monitor) (move : Move current actual)
    (after : Evidence initial native quantum move.after nextMonitor) : monitor.drops.length ≤ nextMonitor.drops.length := by
  rw [Step.drop_count before move after]
  exact Nat.le_add_right _ _

theorem Step.drop_ordinary (before : Evidence initial native quantum current monitor) (move : Move current actual)
    (after : Evidence initial native quantum move.after nextMonitor)
    (ordinary : CampusTCPCustodyFacts.dropEvent actual.event = false) : nextMonitor.drops.length = monitor.drops.length := by
  simp only [Step.drop_count before move after, ordinary, Bool.false_eq_true, ite_false, Nat.add_zero]

theorem Step.drop_selected (before : Evidence initial native quantum current monitor) (move : Move current actual)
    (after : Evidence initial native quantum move.after nextMonitor) (id : Nat) (event : actual.event = .dropPacket id) :
    nextMonitor.drops.length = monitor.drops.length + 1 := by
  simp only [Step.drop_count before move after, event, CampusTCPCustodyFacts.dropEvent, ite_true]

theorem observe_retry_count (config : M.Config) (monitor : M.Monitor) (actual : Step input) :
    (M.observe config monitor actual).retries = monitor.retries ∨
      (M.observe config monitor actual).retries = monitor.retries + 1 := by
  unfold CampusTCPRecoveryRoundMonitor.observe
  repeat' first
    | (solve | exact .inl rfl)
    | (solve | exact .inr rfl)
    | split

theorem observe_retry_mono (config : M.Config) (monitor : M.Monitor) (actual : Step input) :
    monitor.retries ≤ (M.observe config monitor actual).retries := by
  rcases observe_retry_count config monitor actual with same | next <;> omega

theorem serves_copy_false (demand : M.Demand) (id : Nat) : M.serves demand (.copyPacket id) = false := by
  cases demand <;> rfl

theorem Allowed.copy_false (config : M.Config) (state : State input) (monitor : M.Monitor) (id : Nat) :
    ¬M.Allowed config state monitor (.copyPacket id) := by
  unfold CampusTCPRecoveryRoundMonitor.Allowed CampusTCPRecoveryRoundMonitor.allowed
  cases selected : CampusTCPRecoveryRoundMonitor.nextDemand config state monitor <;>
    cases connection : state.connection <;>
    simp only [serves_copy_false, CampusTCPRecoveryRoundMonitor.freeClock,
      CampusTCPRecoveryRoundMonitor.clockAllowed, connection, Bool.false_and, Bool.or_self, Bool.false_eq_true, not_false_eq_true]

theorem actions_no_copy (config : M.Config) (state : State input) (monitor : M.Monitor) (steps : List (Step input))
    (checked : CampusTCPRecoveryRoundServiceBound.actions config state monitor steps = true) :
    ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id := by
  intro actual member id event
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  have within := (List.getElem?_eq_some_iff.mp found).1
  have allowed := (CampusTCPRecoveryRoundServiceBound.actions_correct config state monitor steps).mp checked index within
  simp only [CampusTCPSchedule.eventAt, found, event] at allowed
  exact Allowed.copy_false _ _ _ id allowed

def copyEvent : Event → Bool
  | .copyPacket _ => true
  | _ => false

theorem actions_copy_count (config : M.Config) (state : State input) (monitor : M.Monitor) (steps : List (Step input))
    (checked : CampusTCPRecoveryRoundServiceBound.actions config state monitor steps = true) :
    steps.countP (fun actual => copyEvent actual.event) = 0 := by
  apply List.countP_eq_zero.mpr
  intro actual member
  have quiet : copyEvent actual.event = false := by
    cases event : actual.event <;> first
      | rfl
      | exact False.elim (actions_no_copy config state monitor steps checked actual member _ event)
  rw [quiet]
  decide

end Netlib.Check.CampusTCPRecoveryRoundBookkeeping
