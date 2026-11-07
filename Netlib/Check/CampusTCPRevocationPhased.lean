import Netlib.Check.CampusTCPRevocationControl
import Netlib.Check.CampusTCPRevocationEnabled
import Netlib.Check.CampusTCPRevocationTrigger
import Netlib.Check.CampusTCPStartupTransferObserved
import Netlib.Check.CampusTCPTwoExchangeProjection

/-!
# One action and service contract through TCP revocation

The earlier phase uses the cold-start and transfer monitor.
The shutdown phase retains its actual suffix and the original loss allowance.
-/

namespace Netlib.Check.CampusTCPRevocationPhased

open CampusTCPModel
open CampusTCPRevocationMonitor (Installation)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt pendingAt actions check)
end E
namespace C
export CampusTCPRevocationControl (pendingAt serves actions lossAllowed nativeAllowed)
end C
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

inductive Demand where
  | transfer (demand : CampusTCPStartupTransferMonitor.Demand)
  | shutdown (demand : CampusTCPRevocationControl.Demand)
  deriving DecidableEq

def pending (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (initial : State input) (steps : List (Step input)) (slot : Nat) : Option Demand :=
  if slot ≤ transferEnd then (E.pendingAt config initial (E.initial config) steps slot).map Demand.transfer
  else if slot < triggerCut then none
  else (C.pendingAt names (S.stateAt initial steps triggerCut) CampusTCPRevocationMonitor.initial
    (steps.drop triggerCut) (slot - triggerCut)).map Demand.shutdown

def serves (config : CampusTCPStartupTransferMonitor.Config) (names : Installation → String) : Demand → Event → Bool
  | .transfer demand => CampusTCPStartupTransferMonitor.serves config demand
  | .shutdown demand => C.serves names demand

def service (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (initial : State input) (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pending config transferEnd triggerCut names initial steps)
    (S.eventAt steps) (serves config names) bound

def middleAllowed (names : Installation → String) (event : Event) : Bool :=
  (CampusTCPRevocationMonitor.requested event).isNone && C.nativeAllowed names event

def observationsMatch (steps : List (Step input)) : Bool :=
  steps.all fun actual => actual.result.service.all (fun served => served.observed && served.routeMatched)

def actions (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (report : Report input events) : Bool :=
  report.supported && report.remaining.isEmpty &&
    decide (transferEnd < triggerCut ∧ triggerCut ≤ report.steps.length) &&
    CampusTCPStartupTransferObserved.doneAt config report.steps transferEnd &&
    E.actions config input.initial (E.initial config) (report.steps.take transferEnd) &&
    (report.steps.drop transferEnd |>.take (triggerCut - transferEnd - 1)).all
      (fun actual => middleAllowed names actual.event) &&
    CampusTCPRevocationTrigger.triggerAt report.steps triggerCut &&
    C.actions names config.transfer.lossAllowance (report.steps.drop triggerCut) &&
    report.steps.all (fun actual => C.lossAllowed config.transfer.lossAllowance actual.before actual.event) &&
    CampusTCPRevocationEnabled.check names config.transfer.lossAllowance
      (S.stateAt input.initial report.steps triggerCut) (report.steps.drop triggerCut) &&
    observationsMatch report.steps

structure CheckedActions (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (report : Report input events) : Prop where
  supported : report.supported = true
  finished : report.remaining.isEmpty = true
  order : transferEnd < triggerCut
  within : triggerCut ≤ report.steps.length
  done : CampusTCPStartupTransferObserved.doneAt config report.steps transferEnd = true
  transfer : E.actions config input.initial (E.initial config) (report.steps.take transferEnd) = true
  middle : (report.steps.drop transferEnd |>.take (triggerCut - transferEnd - 1)).all
    (fun actual => middleAllowed names actual.event) = true
  trigger : CampusTCPRevocationTrigger.triggerAt report.steps triggerCut = true
  shutdown : C.actions names config.transfer.lossAllowance (report.steps.drop triggerCut) = true
  loss : report.steps.all (fun actual => C.lossAllowed config.transfer.lossAllowance actual.before actual.event) = true
  enabled : CampusTCPRevocationEnabled.check names config.transfer.lossAllowance
    (S.stateAt input.initial report.steps triggerCut) (report.steps.drop triggerCut) = true
  observations : observationsMatch report.steps = true

theorem checked_actions (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (report : Report input events)
    (checked : actions config transferEnd triggerCut names report = true) :
    CheckedActions config transferEnd triggerCut names report := by
  simp only [actions, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨supported, finished⟩, bounds⟩, done⟩, transfer⟩, middle⟩, trigger⟩, shutdown⟩, loss⟩, enabled⟩, observations⟩
  exact ⟨supported, finished, bounds.1, bounds.2, done, transfer, middle, trigger, shutdown, loss, enabled, observations⟩

theorem monitorAt_take (config : CampusTCPStartupTransferMonitor.Config)
    (monitor : CampusTCPStartupTransferExecution.Monitor input) (steps : List (Step input))
    (slot count : Nat) (inside : slot ≤ count) :
    E.monitorAt config monitor (steps.take count) slot = E.monitorAt config monitor steps slot := by
  induction steps generalizing monitor slot count with
  | nil => simp only [List.take_nil]
  | cons actual rest ih =>
    cases slot with
    | zero => cases count <;> rfl
    | succ slot =>
      cases count with
      | zero => omega
      | succ count => exact ih _ _ _ (Nat.le_of_succ_le_succ inside)

theorem pendingAt_take (config : CampusTCPStartupTransferMonitor.Config) (initial : State input)
    (steps : List (Step input)) (slot count : Nat) (inside : slot ≤ count) :
    E.pendingAt config initial (E.initial config) (steps.take count) slot =
      E.pendingAt config initial (E.initial config) steps slot := by
  unfold E.pendingAt
  rw [CampusTCPTraceSlices.stateAt_take initial steps inside, monitorAt_take config _ steps slot count inside]

theorem transfer_service (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (initial : State input) (steps : List (Step input)) (bound : Nat)
    (within : transferEnd ≤ steps.length)
    (checked : service config transferEnd triggerCut names initial steps bound = true) :
    E.check config initial (E.initial config) (steps.take transferEnd) bound = true := by
  have whole := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  apply (CampusTCPStartupTransferExecution.check_correct _ _ _ _ _).mpr
  apply Theory.BoundedServiceProjection.restrict whole (offset := 0)
    (by rw [List.length_take, Nat.min_eq_left within]; omega) Demand.transfer id
  · intro slot inside demand selected
    have inside : slot ≤ transferEnd := by rw [List.length_take, Nat.min_eq_left within] at inside; exact inside
    rw [Nat.zero_add, pending, ite_eq_left inside, ← pendingAt_take config initial steps slot transferEnd inside, selected]
    rfl
  · intro slot inside
    have inside : slot < transferEnd := by rw [List.length_take, Nat.min_eq_left within] at inside; exact inside
    simpa only [Nat.zero_add, id_eq] using (CampusTCPTwoExchangeProjection.eventAt_take steps inside).symm
  · intro demand event
    rfl

theorem shutdown_service (config : CampusTCPStartupTransferMonitor.Config) (transferEnd triggerCut : Nat)
    (names : Installation → String) (initial : State input) (steps : List (Step input)) (bound : Nat)
    (order : transferEnd < triggerCut) (within : triggerCut ≤ steps.length)
    (checked : service config transferEnd triggerCut names initial steps bound = true) :
    CampusTCPRevocationControl.service names (S.stateAt initial steps triggerCut)
      CampusTCPRevocationMonitor.initial (steps.drop triggerCut) bound = true := by
  have whole := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  apply (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mpr
  apply Theory.BoundedServiceProjection.restrict whole (offset := triggerCut)
    (by rw [List.length_drop]; omega) Demand.shutdown id
  · intro slot _ demand selected
    have pastTransfer : ¬triggerCut + slot ≤ transferEnd := by omega
    have pastTrigger : ¬triggerCut + slot < triggerCut := by omega
    simp only [pending, pastTransfer, ↓reduceIte, pastTrigger, Nat.add_sub_cancel_left, selected, Option.map_some]
  · intro slot _
    exact (CampusTCPTraceSlices.eventAt_drop steps triggerCut slot).symm
  · intro demand event
    rfl

end Netlib.Check.CampusTCPRevocationPhased
