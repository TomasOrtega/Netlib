import Netlib.Check.CampusTCPRevocationMonitor
import Netlib.Check.CampusTCPRevocationCustody
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Theory.BoundedServiceProjection

/-!
# Actual policy and packet demands after TCP revocation

Four installation demands precede resolution of the receiver-link frontier.
The loss gate uses the original report counter and allowance.
-/

namespace Netlib.Check.CampusTCPRevocationControl

open CampusTCPModel
open CampusTCPRevocationMonitor (Installation Monitor)

namespace M
export CampusTCPRevocationMonitor (requested selected observe nextDemand monitorAt)
end M
namespace C
export CampusTCPRevocationCustody (frontier potential)
end C

inductive Demand where
  | install (target : Installation)
  | resolveLink (id service : Nat) (bytes : List UInt8)
  deriving Repr, DecidableEq

def lossAllowed (allowance : Nat) (before : State input) : Event → Bool
  | .dropPacket _ => decide (before.custody.dropped < allowance)
  | _ => true

def nativeAllowed (names : Installation → String) (event : Event) : Bool :=
  match M.requested event with
  | some (target, name) => decide (name = names target)
  | none => match event with
    | .write .. | .send .. | .enableRecovery .. | .enableAck .. | .dispatchAck ..
    | .advanceClock .. | .timeout .. | .read .. | .emitAck .. | .assign ..
    | .serve .. | .deliver .. | .dropPacket .. => true
    | _ => false

def allowed (names : Installation → String) (allowance : Nat) (before : State input) (event : Event) : Bool :=
  nativeAllowed names event && lossAllowed allowance before event

def linkDemand (item : Theory.PacketCustody.Item (Transit input)) : Option Demand :=
  match item.value.payload with
  | .ingress .. => none
  | .link service _ emission _ => some (.resolveLink item.id service emission.bytes)

def pending (names : Installation → String) (initial : Monitor) (steps : List (Step input))
    (state : State input) (slot : Nat) : Option Demand :=
  match M.nextDemand (M.monitorAt names initial steps slot) with
  | some target => some (.install target)
  | none => (C.frontier state).head?.bind linkDemand

def pendingAt (names : Installation → String) (initialState : State input) (initial : Monitor)
    (steps : List (Step input)) (slot : Nat) : Option Demand :=
  pending names initial steps (CampusTCPSchedule.stateAt initialState steps slot) slot

def serves (names : Installation → String) : Demand → Event → Bool
  | .install target, event => CampusTCPRevocationMonitor.serves names target event
  | .resolveLink _ service bytes, .deliver actualService actualBytes policy =>
    decide (actualService = service ∧ actualBytes = bytes ∧ policy = true)
  | .resolveLink id _ _, .dropPacket actualID => decide (actualID = id)
  | _, _ => false

def service (names : Installation → String) (initialState : State input) (initial : Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pendingAt names initialState initial steps)
    (CampusTCPSchedule.eventAt steps) (serves names) bound

def actions (names : Installation → String) (allowance : Nat) : List (Step input) → Bool
  | [] => true
  | actual :: rest => allowed names allowance actual.before actual.event && actions names allowance rest

theorem allowed_no_copy (names : Installation → String) (allowance : Nat) (before : State input)
    (event : Event) (checked : allowed names allowance before event = true) : ∀ id, event ≠ .copyPacket id := by
  intro id same
  simp only [same, allowed, nativeAllowed, M.requested, Bool.false_and, Bool.false_eq_true] at checked

theorem allowed_request (names : Installation → String) (allowance : Nat) (before : State input)
    (event : Event) (checked : allowed names allowance before event = true)
    (target : Installation) (name : String) (request : M.requested event = some (target, name)) :
    name = names target := by
  have pair : nativeAllowed names event = true ∧ lossAllowed allowance before event = true := by
    simpa only [allowed, Bool.and_eq_true] using checked
  have native := pair.1
  simpa only [nativeAllowed, request, decide_eq_true_eq] using native

theorem allowed_transport (names : Installation → String) (allowance : Nat) (before : State input)
    (event : Event) (checked : allowed names allowance before event = true) (request : M.requested event = none) :
    CampusTCPRoundEnvironment.TransportOnly event := by
  have pair : nativeAllowed names event = true ∧ lossAllowed allowance before event = true := by
    simpa only [allowed, Bool.and_eq_true] using checked
  have native := pair.1
  cases event <;> simp_all [nativeAllowed, M.requested, CampusTCPRoundEnvironment.TransportOnly]

theorem allowed_drop (names : Installation → String) (allowance : Nat) (before : State input)
    (id : Nat) (checked : allowed names allowance before (.dropPacket id) = true) :
    before.custody.dropped < allowance := by
  simpa only [allowed, nativeAllowed, M.requested, lossAllowed, Bool.true_and, decide_eq_true_eq] using checked

theorem pending_install (names : Installation → String) (initial : Monitor) (steps : List (Step input))
    (state : State input) (slot : Nat) (target : Installation)
    (selected : M.nextDemand (M.monitorAt names initial steps slot) = some target) :
    pending names initial steps state slot = some (.install target) := by
  simp only [pending, selected]

theorem installation_service (names : Installation → String) (initialState : State input) (initial : Monitor)
    (steps : List (Step input)) (bound : Nat) (checked : service names initialState initial steps bound = true) :
    CampusTCPRevocationMonitor.service names initial steps bound = true := by
  have whole := (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mp checked
  apply (Theory.BoundedServiceCheck.check_correct _ _ _ _ _).mpr
  apply Theory.BoundedServiceProjection.project whole Demand.install
  · intro slot _ target selected
    exact pending_install names initial steps _ slot target selected
  · intro target event
    rfl

theorem installations_complete (names : Installation → String) (initialState : State input)
    (steps : List (Step input)) (bound : Nat)
    (checked : service names initialState CampusTCPRevocationMonitor.initial steps bound = true)
    (enough : 4 * bound ≤ steps.length) :
    M.monitorAt names CampusTCPRevocationMonitor.initial steps (4 * bound) = [] := by
  exact CampusTCPRevocationMonitor.complete names _ steps bound
    (installation_service names initialState _ steps bound checked) enough

end Netlib.Check.CampusTCPRevocationControl
