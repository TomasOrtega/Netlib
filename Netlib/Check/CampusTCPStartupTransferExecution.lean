import Netlib.Check.CampusTCPStartupMonitor
import Netlib.Check.CampusTCPSchedule
import Netlib.Theory.BoundedServiceCheck

/-!
# One observed monitor for startup and transfer

The actual setup write captures the archive and spent startup losses once.
Later data steps retain that snapshot and use the existing transfer monitor.
-/

namespace Netlib.Check.CampusTCPStartupTransferExecution

open CampusTCPModel

namespace M
export CampusTCPStartupTransferMonitor (Config Demand serves)
end M
namespace T
export CampusTCPStartupTransferConfig (Handoff snapshot)
end T
namespace P
export CampusTCPStartupMonitor (Monitor initial nextDemand allowed observe)
end P
namespace W
export CampusTCPTwoTransferMonitor (Monitor nextDemand allowed observe)
end W
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

inductive Monitor (input : Input) where
  | startup (monitor : P.Monitor)
  | data (handoff : T.Handoff input.active input.passive) (monitor : W.Monitor)
  | invalid

def initial (config : M.Config) : Monitor input := .startup (P.initial config)

def nextDemand (config : M.Config) (state : State input) : Monitor input → Option M.Demand
  | .startup monitor => (P.nextDemand config state monitor).map CampusTCPStartupTransferMonitor.Demand.startup
  | .data handoff monitor => (W.nextDemand (config.transfer.data handoff) state monitor).map
      CampusTCPStartupTransferMonitor.Demand.data
  | .invalid => none

def allowed (config : M.Config) (state : State input) : Monitor input → Event → Bool
  | .startup monitor, event => P.allowed config state monitor event
  | .data handoff monitor, event => W.allowed (config.transfer.data handoff) state monitor event
  | .invalid, _ => false

def observe (config : M.Config) : Monitor input → Step input → Monitor input
  | .startup monitor, actual =>
    let next := P.observe config monitor actual
    if next.mode = .data then
      match T.snapshot actual.result.state with
      | some handoff => .data handoff .initial
      | none => .invalid
    else .startup next
  | .data handoff monitor, actual => .data handoff (W.observe (config.transfer.data handoff) monitor actual)
  | .invalid, _ => .invalid

def monitorAt (config : M.Config) (monitor : Monitor input) : List (Step input) → Nat → Monitor input
  | [], _ => monitor
  | _ :: _, 0 => monitor
  | actual :: rest, slot + 1 => monitorAt config (observe config monitor actual) rest slot

def pendingAt (config : M.Config) (state : State input) (monitor : Monitor input)
    (steps : List (Step input)) (slot : Nat) : Option M.Demand :=
  nextDemand config (S.stateAt state steps slot) (monitorAt config monitor steps slot)

def Serviced (config : M.Config) (state : State input) (monitor : Monitor input)
    (steps : List (Step input)) (bound : Nat) : Prop :=
  Theory.BoundedServiceCheck.Serviced steps.length (pendingAt config state monitor steps)
    (S.eventAt steps) (M.serves config) bound

def check (config : M.Config) (state : State input) (monitor : Monitor input)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pendingAt config state monitor steps)
    (S.eventAt steps) (M.serves config) bound

theorem check_correct (config : M.Config) (state : State input) (monitor : Monitor input)
    (steps : List (Step input)) (bound : Nat) :
    check config state monitor steps bound = true ↔ Serviced config state monitor steps bound :=
  Theory.BoundedServiceCheck.check_correct _ _ _ _ _

def actions (config : M.Config) (state : State input) (monitor : Monitor input) : List (Step input) → Bool
  | [] => true
  | actual :: rest => allowed config state monitor actual.event &&
      actions config actual.result.state (observe config monitor actual) rest

theorem actions_correct (config : M.Config) (state : State input) (monitor : Monitor input) (steps : List (Step input)) :
    actions config state monitor steps = true ↔
      ∀ slot, slot < steps.length → allowed config (S.stateAt state steps slot)
        (monitorAt config monitor steps slot) (S.eventAt steps slot) = true := by
  induction steps generalizing state monitor with
  | nil =>
    constructor
    · intro _ slot inside
      cases Nat.not_lt_zero slot inside
    · intro _
      rfl
  | cons actual rest ih =>
    simp only [actions, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨first, later⟩ slot inside
      cases slot with
      | zero => exact first
      | succ slot => exact later slot (Nat.lt_of_succ_lt_succ inside)
    · intro checked
      exact ⟨checked 0 (Nat.zero_lt_succ _), fun slot inside => checked (slot + 1) (Nat.succ_lt_succ inside)⟩

theorem observe_handoff (config : M.Config) (monitor : P.Monitor) (actual : Step input)
    (ready : (P.observe config monitor actual).mode = .data) (selected : T.snapshot actual.result.state = some handoff) :
    observe config (.startup monitor) actual = .data handoff .initial := by
  simp only [observe, ready, ↓reduceIte, selected]

end Netlib.Check.CampusTCPStartupTransferExecution
