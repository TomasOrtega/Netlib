import Netlib.Check.CampusTCPRecoveryRoundMonitor

/-!
# Stored-step monitor for a held TCP gap

The task starts with an actual lower-range link packet.
One loss allowance covers its data and ACK paths and all retries.
-/

namespace Netlib.Check.CampusTCPGapProgressMonitor

open CampusTCPModel CampusTCPEnabled Protocol.TCP
namespace R
export CampusTCPRoundMonitor (Phase References Action ingressAction ticketAction linkAction actionOf)
end R

structure Config where
  sender : Actor
  bytes : List UInt8
  clientIngress : I.InterfaceRef
  serverIngress : I.InterfaceRef
  quantum : Nat
  initialRTO : Nat
  initialRemaining : Nat
  lossAllowance : Nat

def Config.ingress (config : Config) : Actor → I.InterfaceRef
  | .client => config.clientIngress
  | .server => config.serverIngress

structure Monitor where
  phase : R.Phase := .dataLink
  refs : R.References := {}
  waiting : Bool := false
  drops : List Nat := []
  retries : Nat := 0
  firstDataReceipt : Option Nat := none
  deriving Repr, BEq, DecidableEq

def Monitor.initial (output service packet : Nat) : Monitor :=
  { refs := { dataOutput := some output, dataService := some service, dataLinkPacket := some packet } }

def Monitor.invalid (monitor : Monitor) : Monitor :=
  { monitor with phase := .invalid, waiting := false }

inductive Demand where
  | operation (action : R.Action)
  | resolution (action : R.Action) (packet : Nat)
  | tick (actor : Actor) (millis : Nat)
  | timeout (actor : Actor)
  deriving BEq, DecidableEq

def Demand.event : Demand → Event
  | .operation action | .resolution action _ => action.event
  | .tick actor millis => .advanceClock actor millis
  | .timeout actor => .timeout actor true

def serves : Demand → Event → Bool
  | .operation action, event => decide (R.actionOf event = some action)
  | .resolution action packet, event =>
    decide (R.actionOf event = some action) ||
      match event with | .dropPacket id => id == packet | _ => false
  | .tick actor target, .advanceClock selected millis => actor == selected && millis == target
  | .timeout actor, .timeout selected true => actor == selected
  | _, _ => false

@[simp] theorem Demand.serves_event (demand : Demand) : serves demand demand.event = true := by
  cases demand with
  | operation action => simp [serves, Demand.event]
  | resolution action packet => simp [serves, Demand.event]
  | tick actor millis => cases actor <;> simp [serves, Demand.event] <;> rfl
  | timeout actor => cases actor <;> rfl

def packetAt (monitor : Monitor) : Option Nat :=
  match monitor.phase with
  | .dataIngress => monitor.refs.dataIngressPacket
  | .dataLink => monitor.refs.dataLinkPacket
  | .ackIngress => monitor.refs.ackIngressPacket
  | .ackLink => monitor.refs.ackLinkPacket
  | _ => none

def senderRecovery (config : Config) (state : State input) : Option Recovery.State :=
  match state.connection with
  | .application _ endpoints => (endpoint endpoints config.sender).recovery
  | _ => none

def nextAction (config : Config) (before : State input) (monitor : Monitor) : Option R.Action :=
  match monitor.phase with
  | .dataIngress => R.ingressAction before monitor.refs.dataOutput monitor.refs.dataIngressPacket (config.ingress config.sender)
  | .dataTicket => R.ticketAction before monitor.refs.dataTicket
  | .dataLink => R.linkAction before monitor.refs.dataService monitor.refs.dataLinkPacket
  | .needAck => some (.emitAck config.sender.other true)
  | .ackIngress => R.ingressAction before monitor.refs.ackOutput monitor.refs.ackIngressPacket (config.ingress config.sender.other)
  | .ackTicket => R.ticketAction before monitor.refs.ackTicket
  | .ackLink => R.linkAction before monitor.refs.ackService monitor.refs.ackLinkPacket
  | .needRead => some (.read config.sender.other config.bytes.length)
  | .needSend | .done | .invalid => none

def nextDemand (config : Config) (state : State input) (monitor : Monitor) : Option Demand := do
  if monitor.waiting then
    let recovery ← senderRecovery config state
    let deadline ← recovery.deadline
    if recovery.now < deadline then
      return .tick config.sender (min (recovery.now + config.quantum) deadline)
    else return .timeout config.sender
  else
    let action ← nextAction config state monitor
    match packetAt monitor with
    | some packet =>
      if monitor.drops.length < config.lossAllowance then return .resolution action packet
      else return .operation action
    | none => return .operation action

def clockAllowed (config : Config) (before : State input) (event : Event) : Bool :=
  CampusTCPRecoveryRoundMonitor.clockAllowed
    ⟨⟨config.bytes, config.clientIngress, config.serverIngress⟩, config.quantum⟩ before event

def freeClock (config : Config) (before : State input) (monitor : Monitor) (event : Event) : Bool :=
  clockAllowed config before event &&
    match before.connection, event with
    | .application _ endpoints, .advanceClock actor millis =>
      !monitor.waiting || actor != config.sender || millis == (endpoint endpoints actor).now
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

def observeOutput (config : Config) (monitor : Monitor) (actual : Step input) (data : Bool) (next : R.Phase) : Monitor :=
  let actor := if data then config.sender else config.sender.other
  match actual.result.output with
  | none => monitor.invalid
  | some produced =>
    if produced.actor == actor then
      let index := actual.before.outputs.length
      match actual.result.state.custody.pendingID (Transit.ingressAt index) with
      | none => monitor.invalid
      | some id =>
        if data then { monitor with phase := next, refs := { monitor.refs with dataOutput := some index, dataIngressPacket := some id } }
        else { monitor with phase := next, refs := { monitor.refs with ackOutput := some index, ackIngressPacket := some id } }
    else monitor.invalid

def observeAssignment (monitor : Monitor) (actual : Step input) (data : Bool) (next : R.Phase) : Monitor :=
  match actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) with
  | none => monitor.invalid
  | some ticket =>
    if data then { monitor with phase := next, refs := { monitor.refs with dataTicket := some ticket.id } }
    else { monitor with phase := next, refs := { monitor.refs with ackTicket := some ticket.id } }

def observeService (monitor : Monitor) (actual : Step input) (data : Bool) (next : R.Phase) : Monitor :=
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
        if data then { monitor with phase := next, refs := { monitor.refs with dataService := some index, dataLinkPacket := some id } }
        else { monitor with phase := next, refs := { monitor.refs with ackService := some index, ackLinkPacket := some id } }

def observeReceipt (config : Config) (monitor : Monitor) (actual : Step input) (data : Bool) (next : R.Phase) : Monitor :=
  let actor := if data then config.sender.other else config.sender
  match actual.result.receipt, actual.result.application with
  | some received, some (receiver, operation) =>
    if received.actor == actor && receiver == actor then
      let index := actual.before.receipts.length
      if data then
        { monitor with
          phase := next,
          refs := { monitor.refs with dataReceipt := some index, dataReceiveStamp := some operation.stamp },
          firstDataReceipt := match monitor.firstDataReceipt with
            | some previous => some previous
            | none => some index }
      else { monitor with phase := next, refs := { monitor.refs with ackReceipt := some index, ackReceiveStamp := some operation.stamp } }
    else monitor.invalid
  | _, _ => monitor.invalid

def advance (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  match monitor.phase with
  | .dataIngress => observeAssignment monitor actual true .dataTicket
  | .dataTicket => observeService monitor actual true .dataLink
  | .dataLink => observeReceipt config monitor actual true .needAck
  | .needAck => observeOutput config monitor actual false .ackIngress
  | .ackIngress => observeAssignment monitor actual false .ackTicket
  | .ackTicket => observeService monitor actual false .ackLink
  | .ackLink => observeReceipt config monitor actual false .needRead
  | .needRead =>
    match actual.result.application with
    | some (actor, operation) =>
      if actor == config.sender.other && actual.result.read == config.bytes then
        { monitor with phase := .done, refs := { monitor.refs with readStamp := some operation.stamp, readBytes := actual.result.read } }
      else monitor.invalid
    | _ => monitor.invalid
  | .needSend | .done | .invalid => monitor.invalid

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed then
    match actual.event with
    | .advanceClock .. => monitor
    | .dropPacket id =>
      match nextDemand config actual.before monitor with
      | some (.resolution _ packet) =>
        if id == packet then { monitor with waiting := true, drops := monitor.drops ++ [id] }
        else monitor.invalid
      | _ => monitor.invalid
    | .timeout actor true =>
      if monitor.waiting && actor == config.sender then
        { observeOutput config monitor actual true .dataIngress with waiting := false, retries := monitor.retries + 1 }
      else monitor.invalid
    | _ =>
      if monitor.waiting then monitor.invalid
      else match nextAction config actual.before monitor, R.actionOf actual.event with
        | some expected, some selected => if expected = selected then advance config monitor actual else monitor.invalid
        | _, _ => monitor.invalid
  else monitor.invalid

def waitSlots := CampusTCPRecoveryRoundMonitor.waitSlots

def waitBound (config : Config) (retries : Nat) : Nat :=
  if retries = 0 then config.initialRemaining else 2 ^ retries * config.initialRTO

def reserve (config : Config) (retries : Nat) : Nat :=
  match retries with
  | 0 =>
    (if 0 < config.lossAllowance then waitSlots config.quantum config.initialRemaining + 8 else 0) +
      (if 1 < config.lossAllowance then waitSlots config.quantum (2 * config.initialRTO) + 8 else 0)
  | 1 => if 1 < config.lossAllowance then waitSlots config.quantum (2 * config.initialRTO) + 8 else 0
  | _ => 0

def Monitor.rank (config : Config) (state : State input) (monitor : Monitor) : Nat :=
  if monitor.waiting then
    let remaining := match senderRecovery config state with
      | none => 0
      | some recovery => recovery.deadline.getD recovery.now - recovery.now
    waitSlots config.quantum remaining + 9 + reserve config (monitor.retries + 1)
  else match monitor.phase with
    | .needRead => 1
    | .done => 0
    | _ => monitor.phase.rank + reserve config monitor.retries

theorem initial_rank (config : Config) (state : State input) (output service packet : Nat) :
    (Monitor.initial output service packet).rank config state = 6 + reserve config 0 := rfl

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

end Netlib.Check.CampusTCPGapProgressMonitor
