import Netlib.Check.CampusTCPTwoProgressMonitor

/-!
# One current selector for both exchange directions

The actual forward read exposes the reverse write demand.
Both legs keep one global drop log and timeout count.
-/

namespace Netlib.Check.CampusTCPTwoExchangeMonitor

open CampusTCPModel CampusTCPEnabled Protocol.TCP

namespace L
export CampusTCPTwoProgressMonitor (Config Monitor Demand nextDemand allowed observe serves)
end L
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

structure Config where
  forward : L.Config
  reverseLower : List UInt8
  reverseUpper : List UInt8
  reverseRTO : Nat

def Config.reverseBytes (config : Config) : List UInt8 := config.reverseLower ++ config.reverseUpper

def Config.reverse (config : Config) (forwardDrops : Nat) : L.Config :=
  { config.forward with
    sender := config.forward.sender.other
    bytes := config.reverseBytes
    initialRTO := config.reverseRTO
    initialRemaining := 0
    lossAllowance := config.forward.lossAllowance - forwardDrops
    lowerCount := config.reverseLower.length
    upperCount := config.reverseUpper.length }

inductive Mode where
  | forward | needWrite | reverse | done | invalid
  deriving Repr, BEq, DecidableEq

structure Monitor where
  mode : Mode := .forward
  forward : L.Monitor := .initial
  reverse : L.Monitor := .initial
  drops : List Nat := []
  timeouts : Nat := 0
  slots : Nat := 0
  forwardReadSlot : Option Nat := none
  writeSlot : Option Nat := none
  reverseReadSlot : Option Nat := none
  deriving Repr, BEq, DecidableEq

def Monitor.initial : Monitor := {}

def Monitor.invalid (monitor : Monitor) : Monitor := { monitor with mode := .invalid }

inductive Demand where
  | forward (demand : L.Demand)
  | reverseWrite (actor : Actor) (bytes : List UInt8)
  | reverse (demand : L.Demand)
  deriving BEq, DecidableEq

def serves : Demand → Event → Bool
  | .forward demand, event | .reverse demand, event => L.serves demand event
  | .reverseWrite actor bytes, .write selected payload => actor == selected && bytes == payload
  | .reverseWrite .., _ => false

def writeDemand (config : Config) : Demand :=
  .reverseWrite config.forward.sender.other config.reverseBytes

def nextDemand (config : Config) (state : State input) (monitor : Monitor) : Option Demand :=
  match monitor.mode with
  | .forward => (L.nextDemand config.forward state monitor.forward).map Demand.forward
  | .needWrite => some (writeDemand config)
  | .reverse =>
    (L.nextDemand (config.reverse monitor.forward.drops.length) state monitor.reverse).map Demand.reverse
  | .done | .invalid => none

def allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Bool :=
  match monitor.mode with
  | .forward => L.allowed config.forward state monitor.forward event
  | .needWrite =>
    match event with
    | .write .. => serves (writeDemand config) event
    | .advanceClock .. => L.allowed config.forward state monitor.forward event
    | _ => false
  | .reverse => L.allowed (config.reverse monitor.forward.drops.length) state monitor.reverse event
  | .done =>
    match event with
    | .advanceClock .. => L.allowed (config.reverse monitor.forward.drops.length) state monitor.reverse event
    | _ => false
  | .invalid => false

def Allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Prop :=
  allowed config state monitor event = true

private def record (monitor : Monitor) (actual : Step input) : Monitor :=
  { monitor with
    slots := monitor.slots + 1
    drops := match actual.event with | .dropPacket id => monitor.drops ++ [id] | _ => monitor.drops
    timeouts := match actual.event with | .timeout _ true => monitor.timeouts + 1 | _ => monitor.timeouts }

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event then
    let recorded := record monitor actual
    match monitor.mode with
    | .forward =>
      let next := L.observe config.forward monitor.forward actual
      if next.mode == .invalid then monitor.invalid
      else if next.mode == .done then
        { recorded with mode := .needWrite, forward := next, forwardReadSlot := some monitor.slots }
      else { recorded with forward := next }
    | .needWrite =>
      match actual.event with
      | .write .. => { recorded with mode := .reverse, reverse := .initial, writeSlot := some monitor.slots }
      | .advanceClock .. => recorded
      | _ => monitor.invalid
    | .reverse =>
      let next := L.observe (config.reverse monitor.forward.drops.length) monitor.reverse actual
      if next.mode == .invalid then monitor.invalid
      else if next.mode == .done then
        { recorded with mode := .done, reverse := next, reverseReadSlot := some monitor.slots }
      else { recorded with reverse := next }
    | .done => recorded
    | .invalid => monitor.invalid
  else monitor.invalid

def system (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := ∃ actual : Step input, actual.before = before.1 ∧ actual.event = event ∧
    actual.result.state = after.1 ∧ observe config before.2 actual = after.2

def guardedSystem (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := Allowed config before.1 before.2 event ∧ (system input config).step before event after

def monitorAt (config : Config) (initial : Monitor) : List (Step input) → Nat → Monitor
  | [], _ => initial
  | _ :: _, 0 => initial
  | head :: rest, index + 1 => monitorAt config (observe config initial head) rest index

@[simp] theorem monitorAt_zero (config : Config) (initial : Monitor) (steps : List (Step input)) :
    monitorAt config initial steps 0 = initial := by cases steps <;> rfl

theorem monitorAt_next (config : Config) (initial : Monitor) (steps : List (Step input))
    (found : steps[index]? = some actual) :
    monitorAt config initial steps (index + 1) = observe config (monitorAt config initial steps index) actual := by
  induction steps generalizing index initial with
  | nil => simp at found
  | cons head rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst actual
      simp only [monitorAt, monitorAt_zero]
    | succ index => exact ih _ found

theorem monitorAt_length (config : Config) (initial : Monitor) (steps : List (Step input)) :
    monitorAt config initial steps steps.length = steps.foldl (observe config) initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons head rest ih => simpa only [List.length_cons, monitorAt, List.foldl_cons] using ih (observe config initial head)

def stateAt (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) (index : Nat) :
    State input × Monitor :=
  ⟨S.stateAt initial steps index, monitorAt config monitor steps index⟩

def Trace.prefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor) :
    Theory.BoundedProgress.Prefix (system input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := S.eventAt steps
  checked index within := by
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace index within
    exact ⟨actual, before, event, after, (monitorAt_next config monitor steps found).symm⟩

def pendingAt (config : Config) (initial : State input) (monitor : Monitor)
    (steps : List (Step input)) (slot : Nat) : Option Demand :=
  nextDemand config (S.stateAt initial steps slot) (monitorAt config monitor steps slot)

def Serviced (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) (bound : Nat) : Prop :=
  Theory.BoundedServiceCheck.Serviced steps.length (pendingAt config initial monitor steps) (S.eventAt steps) serves bound

def check (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pendingAt config initial monitor steps) (S.eventAt steps) serves bound

theorem check_correct (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ Serviced config initial monitor steps bound :=
  Theory.BoundedServiceCheck.check_correct _ _ _ _ _

def actions (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) : Bool :=
  (List.range steps.length).all fun slot => allowed config (S.stateAt initial steps slot)
    (monitorAt config monitor steps slot) (S.eventAt steps slot)

theorem actions_correct (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → Allowed config (S.stateAt initial steps slot)
        (monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  simp only [actions, List.all_eq_true, List.mem_range, Allowed]

end Netlib.Check.CampusTCPTwoExchangeMonitor
