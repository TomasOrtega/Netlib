import Netlib.Check.CampusTCPSchedule
import Netlib.Check.CampusTCPEnabled

/-!
# Stored-step observation for a campus TCP round

The monitor reads actual operation results and packet references.
It does not run an endpoint, gateway, or campus operation.
-/

namespace Netlib.Check.CampusTCPRoundMonitor

open CampusTCPModel CampusTCPEnabled

structure Config where
  bytes : List UInt8
  clientIngress : I.InterfaceRef
  serverIngress : I.InterfaceRef

inductive Phase where
  | needSend | dataIngress | dataTicket | dataLink | needAck
  | ackIngress | ackTicket | ackLink | needRead | done | invalid
  deriving Repr, BEq, DecidableEq

def Phase.rank : Phase → Nat
  | .needSend => 9 | .dataIngress => 8 | .dataTicket => 7 | .dataLink => 6 | .needAck => 5
  | .ackIngress => 4 | .ackTicket => 3 | .ackLink => 2 | .needRead => 1 | .done => 0 | .invalid => 10

structure References where
  dataOutput : Option Nat := none
  dataIngressPacket : Option Nat := none
  dataTicket : Option Nat := none
  dataService : Option Nat := none
  dataLinkPacket : Option Nat := none
  dataReceipt : Option Nat := none
  dataReceiveStamp : Option Nat := none
  ackOutput : Option Nat := none
  ackIngressPacket : Option Nat := none
  ackTicket : Option Nat := none
  ackService : Option Nat := none
  ackLinkPacket : Option Nat := none
  ackReceipt : Option Nat := none
  ackReceiveStamp : Option Nat := none
  readStamp : Option Nat := none
  readBytes : List UInt8 := []
  deriving Repr, BEq, DecidableEq

structure Monitor where
  phase : Phase := .needSend
  refs : References := {}
  deriving Repr, BEq, DecidableEq

def Monitor.initial : Monitor := {}
def Monitor.rank (monitor : Monitor) : Nat := monitor.phase.rank
def Monitor.invalid (monitor : Monitor) : Monitor := { monitor with phase := .invalid }

theorem Phase.rank_zero (phase : Phase) : phase.rank = 0 ↔ phase = .done := by
  cases phase <;> simp only [Phase.rank, reduceCtorEq]

inductive Action where
  | send (actor : Actor) (count : Nat) (policy : Bool)
  | assign (output : Nat) (ingress : I.InterfaceRef)
  | serve (ticket : Nat)
  | deliver (service : Nat) (bytes : List UInt8) (policy : Bool)
  | emitAck (actor : Actor) (policy : Bool)
  | read (actor : Actor) (count : Nat)
  deriving BEq, DecidableEq

def Action.event : Action → Event
  | .send actor count policy => .send actor count policy
  | .assign output ingress => .assign output ingress
  | .serve ticket => .serve ticket none
  | .deliver service bytes policy => .deliver service bytes policy
  | .emitAck actor policy => .emitAck actor policy
  | .read actor count => .read actor count

def actionOf : Event → Option Action
  | .send actor count policy => some (.send actor count policy)
  | .assign output ingress => some (.assign output ingress)
  | .serve ticket none => some (.serve ticket)
  | .deliver service bytes policy => some (.deliver service bytes policy)
  | .emitAck actor policy => some (.emitAck actor policy)
  | .read actor count => some (.read actor count)
  | _ => none

@[simp] theorem Action.actionOf_event (action : Action) : actionOf action.event = some action := by
  cases action <;> rfl

def sameClock (before : State input) (event : Event) : Bool :=
  match before.connection, event with
  | .application _ endpoints, .advanceClock actor now =>
    (endpoint endpoints actor).recovery.isSome && now == (endpoint endpoints actor).now
  | _, _ => false

def ingressAction (before : State input) (output packet : Option Nat) (ingress : I.InterfaceRef) : Option Action := do
  let index ← output
  let expected ← packet
  let _ ← before.outputs[index]?
  let pending ← before.custody.pendingID (Transit.ingressAt index)
  if pending == expected then return .assign index ingress else none

def ticketAction (before : State input) (ticket : Option Nat) : Option Action := do
  let id ← ticket
  let _ ← before.work.pending.find? (fun item => item.id == id)
  return .serve id

def linkAction (before : State input) (service packet : Option Nat) : Option Action := do
  let index ← service
  let expected ← packet
  let served ← before.services[index]?
  let emission ← served.evidence.output
  let pending ← before.custody.pendingID (Transit.linkAt index)
  if pending == expected then return .deliver index emission.bytes true else none

def nextAction (config : Config) (before : State input) (monitor : Monitor) : Option Action :=
  match monitor.phase with
  | .needSend => some (.send .client config.bytes.length true)
  | .dataIngress => ingressAction before monitor.refs.dataOutput monitor.refs.dataIngressPacket config.clientIngress
  | .dataTicket => ticketAction before monitor.refs.dataTicket
  | .dataLink => linkAction before monitor.refs.dataService monitor.refs.dataLinkPacket
  | .needAck => some (.emitAck .server true)
  | .ackIngress => ingressAction before monitor.refs.ackOutput monitor.refs.ackIngressPacket config.serverIngress
  | .ackTicket => ticketAction before monitor.refs.ackTicket
  | .ackLink => linkAction before monitor.refs.ackService monitor.refs.ackLinkPacket
  | .needRead => some (.read .server config.bytes.length)
  | .done | .invalid => none

def nextEvent (config : Config) (before : State input) (monitor : Monitor) : Option Event :=
  (nextAction config before monitor).map Action.event

def Allowed (config : Config) (before : State input) (monitor : Monitor) (event : Event) : Prop :=
  nextEvent config before monitor = some event ∨ sameClock before event = true

theorem nextEvent_action (config : Config) (before : State input) (monitor : Monitor) (event : Event)
    (next : nextEvent config before monitor = some event) :
    ∃ action, nextAction config before monitor = some action ∧ event = action.event := by
  cases selected : nextAction config before monitor with
  | none => simp only [nextEvent, selected, Option.map_none, reduceCtorEq] at next
  | some action =>
    simp only [nextEvent, selected, Option.map_some, Option.some.injEq] at next
    exact ⟨action, rfl, next.symm⟩

def observeOutput (monitor : Monitor) (actual : Step input) (actor : Actor) (next : Phase) : Monitor :=
  match actual.result.output with
  | none => monitor.invalid
  | some produced =>
    if produced.actor == actor then
      let index := actual.before.outputs.length
      match actual.result.state.custody.pendingID (Transit.ingressAt index) with
      | none => monitor.invalid
      | some id =>
        match actor with
        | .client => { phase := next, refs := { monitor.refs with dataOutput := some index, dataIngressPacket := some id } }
        | .server => { phase := next, refs := { monitor.refs with ackOutput := some index, ackIngressPacket := some id } }
    else monitor.invalid

def observeAssignment (monitor : Monitor) (actual : Step input) (actor : Actor) (next : Phase) : Monitor :=
  match actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) with
  | none => monitor.invalid
  | some ticket =>
    match actor with
    | .client => { phase := next, refs := { monitor.refs with dataTicket := some ticket.id } }
    | .server => { phase := next, refs := { monitor.refs with ackTicket := some ticket.id } }

def observeService (monitor : Monitor) (actual : Step input) (actor : Actor) (next : Phase) : Monitor :=
  match actual.result.service with
  | none => monitor.invalid
  | some served =>
    match served.evidence.output with
    | none => monitor.invalid
    | some _ =>
      let index := actual.before.services.length
      match actual.result.state.custody.pendingID (Transit.linkAt index) with
      | none => monitor.invalid
      | some id =>
        match actor with
        | .client => { phase := next, refs := { monitor.refs with dataService := some index, dataLinkPacket := some id } }
        | .server => { phase := next, refs := { monitor.refs with ackService := some index, ackLinkPacket := some id } }

def observeReceipt (monitor : Monitor) (actual : Step input) (actor : Actor) (next : Phase) : Monitor :=
  match actual.result.receipt, actual.result.application with
  | some received, some (receiver, operation) =>
    if received.actor == actor && receiver == actor then
      let index := actual.before.receipts.length
      match actor with
      | .server => { phase := next, refs := { monitor.refs with dataReceipt := some index, dataReceiveStamp := some operation.stamp } }
      | .client => { phase := next, refs := { monitor.refs with ackReceipt := some index, ackReceiveStamp := some operation.stamp } }
    else monitor.invalid
  | _, _ => monitor.invalid

def advance (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  match monitor.phase with
  | .needSend => observeOutput monitor actual .client .dataIngress
  | .dataIngress => observeAssignment monitor actual .client .dataTicket
  | .dataTicket => observeService monitor actual .client .dataLink
  | .dataLink => observeReceipt monitor actual .server .needAck
  | .needAck => observeOutput monitor actual .server .ackIngress
  | .ackIngress => observeAssignment monitor actual .server .ackTicket
  | .ackTicket => observeService monitor actual .server .ackLink
  | .ackLink => observeReceipt monitor actual .client .needRead
  | .needRead =>
    match actual.result.application with
    | some (.server, operation) =>
      if actual.result.read == config.bytes then
        { phase := .done, refs := { monitor.refs with readStamp := some operation.stamp, readBytes := actual.result.read } }
      else monitor.invalid
    | _ => monitor.invalid
  | .done | .invalid => monitor.invalid

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed then
    if sameClock actual.before actual.event then monitor
    else match nextAction config actual.before monitor, actionOf actual.event with
      | some expected, some selected => if expected = selected then advance config monitor actual else monitor.invalid
      | _, _ => monitor.invalid
  else monitor.invalid

theorem observe_clock (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (clock : sameClock actual.before actual.event = true) : observe config monitor actual = monitor := by
  simp only [observe, supported, passed, Bool.and_self, clock, ite_true]

theorem observe_selected (config : Config) (monitor : Monitor) (actual : Step input) (action : Action)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (clock : sameClock actual.before actual.event = false)
    (next : nextAction config actual.before monitor = some action) (selected : actionOf actual.event = some action) :
    observe config monitor actual = advance config monitor actual := by
  simp only [observe, supported, passed, Bool.and_self, clock, Bool.false_eq_true, ite_false, next, selected,
    ite_true]

def system (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := ∃ actual : Step input, actual.before = before.1 ∧ actual.event = event ∧
    actual.result.state = after.1 ∧ observe config before.2 actual = after.2

def guardedSystem (input : Input) (config : Config) : Protocol.Transition (State input × Monitor) Event where
  step before event after := Allowed config before.1 before.2 event ∧ (system input config).step before event after

theorem erase (edge : (system input config).step before event after) :
    (CampusTCPSchedule.system input).step before.1 event after.1 := by
  obtain ⟨actual, same, selected, result, _⟩ := edge
  exact ⟨actual.result, by simpa only [← same, ← selected] using actual.computed, result⟩

theorem guarded_erase (edge : (guardedSystem input config).step before event after) :
    (CampusTCPSchedule.system input).step before.1 event after.1 := erase edge.2

theorem lift_step (edge : (CampusTCPSchedule.system input).step before event after) (monitor : Monitor) :
    ∃ next, (system input config).step (before, monitor) event (after, next) := by
  obtain ⟨effect, computed, same⟩ := edge
  let actual : Step input := ⟨before, event, effect, computed⟩
  exact ⟨observe config monitor actual, actual, rfl, rfl, same, rfl⟩

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

@[simp] theorem Trace.prefix_length (trace : Trace input initial events steps final remaining)
    (config : Config) (monitor : Monitor) : (Trace.prefix trace config monitor).length = steps.length := rfl

@[simp] theorem Trace.prefix_initial (trace : Trace input initial events steps final remaining)
    (config : Config) (monitor : Monitor) : (Trace.prefix trace config monitor).state 0 = (initial, monitor) := by
  simp only [Trace.prefix, stateAt, CampusTCPSchedule.stateAt_zero, monitorAt_zero]

theorem Trace.prefix_final (trace : Trace input initial events steps final remaining)
    (config : Config) (monitor : Monitor) :
    (Trace.prefix trace config monitor).state steps.length = (final, steps.foldl (observe config) monitor) := by
  simp only [Trace.prefix, stateAt, CampusTCPSchedule.Trace.last_state trace, monitorAt_length]

theorem Trace.prefix_erases (trace : Trace input initial events steps final remaining)
    (config : Config) (monitor : Monitor) (index : Nat) :
    ((Trace.prefix trace config monitor).state index).1 = (CampusTCPSchedule.Trace.prefix trace).state index := rfl

theorem Trace.slot_time (trace : Trace input initial events steps final remaining)
    (config : Config) (monitor : Monitor) (index : Nat) (within : index ≤ steps.length) :
    ((Trace.prefix trace config monitor).state index).1.time = initial.time + index :=
  CampusTCPSchedule.Trace.slot_time trace index within

def Trace.guardedPrefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor)
    (actions : ∀ index, index < steps.length →
      Allowed config (CampusTCPSchedule.stateAt initial steps index) (monitorAt config monitor steps index)
        (CampusTCPSchedule.eventAt steps index)) : Theory.BoundedProgress.Prefix (guardedSystem input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := CampusTCPSchedule.eventAt steps
  checked index within := ⟨actions index within, (Trace.prefix trace config monitor).checked index within⟩

end Netlib.Check.CampusTCPRoundMonitor
