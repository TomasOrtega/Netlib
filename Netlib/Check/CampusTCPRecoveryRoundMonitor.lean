import Netlib.Check.CampusTCPRoundMonitor
import Netlib.Protocol.TCP.EndpointClockEnabled

/-!
# Stored-step monitor for timed campus recovery

Packet resolution can consume the selected packet or drop it.
Only an actual timeout starts another transmission of the range.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundMonitor

open CampusTCPModel CampusTCPEnabled Protocol.TCP
namespace R
export CampusTCPRoundMonitor (Phase References Action ingressAction ticketAction linkAction)
end R

structure Config extends CampusTCPRoundMonitor.Config where
  quantum : Nat

structure Monitor where
  round : CampusTCPRoundMonitor.Monitor := .initial
  waiting : Bool := false
  drops : List Nat := []
  retries : Nat := 0
  firstDataReceipt : Option Nat := none
  deriving Repr, BEq, DecidableEq

def Monitor.initial : Monitor := {}
def Monitor.invalid (monitor : Monitor) : Monitor :=
  { monitor with round := monitor.round.invalid, waiting := false }

inductive Demand where
  | operation (action : R.Action)
  | resolution (action : R.Action) (packet : Nat)
  | tick (millis : Nat)
  | timeout
  deriving BEq, DecidableEq

def Demand.event : Demand → Event
  | .operation action | .resolution action _ => action.event
  | .tick millis => .advanceClock .client millis
  | .timeout => .timeout .client true

def serves : Demand → Event → Bool
  | .operation action, event => decide (CampusTCPRoundMonitor.actionOf event = some action)
  | .resolution action packet, event =>
    decide (CampusTCPRoundMonitor.actionOf event = some action) ||
      match event with | .dropPacket id => id == packet | _ => false
  | .tick target, .advanceClock .client millis => millis == target
  | .timeout, .timeout .client true => true
  | _, _ => false

@[simp] theorem Demand.serves_event (demand : Demand) : serves demand demand.event = true := by
  cases demand <;> simp [serves, Demand.event]

def packetAt (monitor : Monitor) : Option Nat :=
  match monitor.round.phase with
  | .dataIngress => monitor.round.refs.dataIngressPacket
  | .dataLink => monitor.round.refs.dataLinkPacket
  | .ackIngress => monitor.round.refs.ackIngressPacket
  | .ackLink => monitor.round.refs.ackLinkPacket
  | _ => none

def clientRecovery (state : State input) : Option Recovery.State :=
  match state.connection with
  | .application _ endpoints => (endpoint endpoints .client).recovery
  | _ => none

def nextDemand (config : Config) (state : State input) (monitor : Monitor) : Option Demand := do
  if monitor.waiting then
    let recovery ← clientRecovery state
    let deadline ← recovery.deadline
    if recovery.now < deadline then
      return .tick (min (recovery.now + config.quantum) deadline)
    else return .timeout
  else
    let action ← CampusTCPRoundMonitor.nextAction config.toConfig state monitor.round
    match packetAt monitor with
    | some packet =>
      if monitor.drops.length < 2 then return .resolution action packet
      else return .operation action
    | none => return .operation action

def clockAllowed (config : Config) (before : State input) (event : Event) : Bool :=
  match before.connection, event with
  | .application _ endpoints, .advanceClock actor millis =>
    let state := endpoint endpoints actor
    state.recovery.isSome && decide (state.now ≤ millis ∧ millis ≤ state.now + config.quantum) &&
      decide (Endpoint.AckTimeReady state millis)
  | _, _ => false

def freeClock (config : Config) (before : State input) (monitor : Monitor) (event : Event) : Bool :=
  clockAllowed config before event &&
    match before.connection, event with
    | .application _ endpoints, .advanceClock .client millis =>
      !monitor.waiting || millis == (endpoint endpoints .client).now
    | _, .advanceClock .server _ => true
    | _, _ => false

def allowed (config : Config) (before : State input) (monitor : Monitor) (event : Event) : Bool :=
  let selected := match nextDemand config before monitor with
    | none => false
    | some demand => serves demand event
  let guard := match event with
    | .advanceClock .. => clockAllowed config before event
    | _ => true
  (selected || freeClock config before monitor event) && guard

def Allowed (config : Config) (before : State input) (monitor : Monitor) (event : Event) : Prop :=
  allowed config before monitor event = true

def observeDrop (monitor : Monitor) (id : Nat) : Monitor :=
  { monitor with waiting := true, drops := monitor.drops ++ [id] }

def observeTimeout (monitor : Monitor) (actual : Step input) : Monitor :=
  { monitor with
    round := CampusTCPRoundMonitor.observeOutput monitor.round actual .client .dataIngress
    waiting := false
    retries := monitor.retries + 1 }

def observeOrdinary (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  let updated := CampusTCPRoundMonitor.observe config.toConfig monitor.round actual
  { monitor with
    round := updated
    firstDataReceipt := match monitor.firstDataReceipt with
      | some index => some index
      | none => if monitor.round.phase == .dataLink then updated.refs.dataReceipt else none }

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed then
    match actual.event with
    | .advanceClock .. => monitor
    | .dropPacket id =>
      match nextDemand config actual.before monitor with
      | some (.resolution _ packet) => if id == packet then observeDrop monitor id else monitor.invalid
      | _ => monitor.invalid
    | .timeout .client true =>
      if monitor.waiting then observeTimeout monitor actual else monitor.invalid
    | _ =>
      if monitor.waiting then monitor.invalid else observeOrdinary config monitor actual
  else monitor.invalid

def waitSlots (quantum remaining : Nat) : Nat := (remaining + quantum - 1) / quantum

def reserve (quantum retries : Nat) : Nat :=
  match retries with
  | 0 => waitSlots quantum 1000 + 8 + waitSlots quantum 2000 + 8
  | 1 => waitSlots quantum 2000 + 8
  | _ => 0

def Monitor.rank (config : Config) (state : State input) (monitor : Monitor) : Nat :=
  if monitor.waiting then
    let remaining := match clientRecovery state with
      | none => 0
      | some recovery => recovery.deadline.getD recovery.now - recovery.now
    waitSlots config.quantum remaining + 9 + reserve config.quantum (monitor.retries + 1)
  else match monitor.round.phase with
    | .needRead => 1
    | .done => 0
    | _ => monitor.round.rank + reserve config.quantum monitor.retries

theorem initial_rank (config : Config) (state : State input) :
    Monitor.initial.rank config state = 25 + waitSlots config.quantum 1000 + waitSlots config.quantum 2000 := by
  simp only [Monitor.rank, Monitor.initial, Bool.false_eq_true, ↓reduceIte, CampusTCPRoundMonitor.Monitor.initial,
    CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank, reserve]
  omega

def system (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := ∃ actual : Step input, actual.before = before.1 ∧ actual.event = event ∧
    actual.result.state = after.1 ∧ observe config before.2 actual = after.2

def guardedSystem (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := Allowed config before.1 before.2 event ∧ (system input config).step before event after

theorem erase (edge : (system input config).step before event after) :
    (CampusTCPSchedule.system input).step before.1 event after.1 := by
  obtain ⟨actual, same, selected, result, _⟩ := edge
  exact ⟨actual.result, by simpa only [← same, ← selected] using actual.computed, result⟩

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
  ⟨CampusTCPSchedule.stateAt initial steps index, monitorAt config monitor steps index⟩

def Trace.prefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor) :
    Theory.BoundedProgress.Prefix (system input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := CampusTCPSchedule.eventAt steps
  checked index within := by
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace index within
    exact ⟨actual, before, event, after, (monitorAt_next config monitor steps found).symm⟩

def Trace.guardedPrefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor)
    (actions : ∀ index, index < steps.length →
      Allowed config (CampusTCPSchedule.stateAt initial steps index) (monitorAt config monitor steps index)
        (CampusTCPSchedule.eventAt steps index)) : Theory.BoundedProgress.Prefix (guardedSystem input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := CampusTCPSchedule.eventAt steps
  checked index within := ⟨actions index within, (Trace.prefix trace config monitor).checked index within⟩

end Netlib.Check.CampusTCPRecoveryRoundMonitor
