import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Theory.BoundedServiceCheck

/-!
# Stored-step monitor for two TCP records

Both original paths share the drop log with later head retries.
The next head and timer come from the actual sender ledger.
-/

namespace Netlib.Check.CampusTCPTwoProgressMonitor

open CampusTCPModel CampusTCPEnabled Protocol.TCP
namespace R
export CampusTCPRoundMonitor (Phase References Action actionOf)
end R
namespace G
export CampusTCPGapProgressMonitor
  (Config Monitor Demand serves packetAt senderRecovery nextAction clockAllowed freeClock
    observeOutput observeAssignment observeService observeReceipt)
end G
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

structure Config extends G.Config where
  lowerCount : Nat
  upperCount : Nat

inductive Mode where
  | originals | recovery | needRead | done | invalid
  deriving Repr, BEq, DecidableEq

inductive Original where
  | lower | upper
  deriving Repr, BEq, DecidableEq

inductive DropTarget where
  | lower | upper | retry | ack
  deriving Repr, BEq, DecidableEq

structure Lane where
  phase : R.Phase := .needSend
  refs : R.References := {}
  deriving Repr, BEq, DecidableEq

def Lane.toGap (lane : Lane) : G.Monitor := { phase := lane.phase, refs := lane.refs }

def Lane.ofGap (monitor : G.Monitor) : Lane := ⟨monitor.phase, monitor.refs⟩

structure Monitor where
  mode : Mode := .originals
  lower : Lane := {}
  upper : Lane := {}
  retry : Lane := { phase := .done }
  ack : Option Lane := none
  waiting : Bool := false
  retries : Nat := 0
  drops : List Nat := []
  lastOriginal : Option Original := none
  dataReceipts : List Nat := []
  ackReceipts : List Nat := []
  releaseStamps : List Nat := []
  readStamp : Option Nat := none
  readBytes : List UInt8 := []
  deriving Repr, BEq, DecidableEq

def Monitor.initial : Monitor := {}

def Monitor.invalid (monitor : Monitor) : Monitor :=
  { monitor with mode := .invalid, waiting := false }

inductive Demand where
  | single (demand : G.Demand)
  | originalChoice (lower upper : Option G.Demand)
  deriving BEq, DecidableEq

def servesOption (demand : Option G.Demand) (event : Event) : Bool :=
  match demand with | none => false | some value => G.serves value event

def serves : Demand → Event → Bool
  | .single demand, event => G.serves demand event
  | .originalChoice lower upper, event => servesOption lower event || servesOption upper event

def laneDemand (config : Config) (state : State input) (monitor : Monitor) (lane : Lane) : Option G.Demand := do
  let action ← G.nextAction config.toConfig state lane.toGap
  match G.packetAt lane.toGap with
  | some packet =>
    if monitor.drops.length < config.lossAllowance then return .resolution action packet
    else return .operation action
  | none => return .operation action

def timerTarget (recovery : Recovery.State) : Option Nat := do
  let head ← recovery.outstanding.head?
  let deadline ← recovery.deadline
  return max deadline (head.lastAt + recovery.rto)

def timerDemand (config : Config) (state : State input) : Option G.Demand := do
  let recovery ← G.senderRecovery config.toConfig state
  let target ← timerTarget recovery
  if recovery.now < target then
    return .tick config.sender (min (recovery.now + config.quantum) target)
  else return .timeout config.sender

def nextDemand (config : Config) (state : State input) (monitor : Monitor) : Option Demand :=
  match monitor.mode with
  | .originals =>
    if monitor.lower.phase == .needSend then
      some (.single (.operation (.send config.sender config.lowerCount true)))
    else if monitor.upper.phase == .needSend then
      some (.single (.operation (.send config.sender config.upperCount true)))
    else match monitor.ack with
      | some lane => (laneDemand config state monitor lane).map Demand.single
      | none =>
        let lower := laneDemand config state monitor monitor.lower
        let upper := laneDemand config state monitor monitor.upper
        if lower.isSome || upper.isSome then some (.originalChoice lower upper) else none
  | .recovery =>
    match monitor.ack with
    | some lane => (laneDemand config state monitor lane).map Demand.single
    | none =>
      if monitor.waiting then (timerDemand config state).map Demand.single
      else (laneDemand config state monitor monitor.retry).map Demand.single
  | .needRead => some (.single (.operation (.read config.sender.other config.bytes.length)))
  | .done | .invalid => none

def exposedPacket (config : Config) (state : State input) (lane : Lane) : Option Nat := do
  let _ ← G.nextAction config.toConfig state lane.toGap
  G.packetAt lane.toGap

def dropTarget (config : Config) (state : State input) (monitor : Monitor) (id : Nat) : Option DropTarget :=
  if monitor.mode == .originals || monitor.mode == .recovery then
    if monitor.drops.length < config.lossAllowance then
      if exposedPacket config state monitor.lower == some id then some .lower
      else if exposedPacket config state monitor.upper == some id then some .upper
      else if exposedPacket config state monitor.retry == some id then some .retry
      else match monitor.ack with
        | some lane => if exposedPacket config state lane == some id then some .ack else none
        | none => none
    else none
  else none

def clockAllowed (config : Config) (state : State input) (event : Event) : Bool :=
  G.clockAllowed config.toConfig state event

def freeClock (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Bool :=
  G.freeClock config.toConfig state { waiting := monitor.waiting } event

def allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Bool :=
  if monitor.mode == .invalid then false
  else
    let selected := match nextDemand config state monitor with
      | none => false
      | some demand => serves demand event
    let dropped := match event with
      | .dropPacket id => (dropTarget config state monitor id).isSome
      | _ => false
    let guard := match event with
      | .advanceClock .. => clockAllowed config state event
      | _ => true
    (selected || dropped || freeClock config state monitor event) && guard

def Allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Prop :=
  allowed config state monitor event = true

def normalize (config : Config) (state : State input) (monitor : Monitor) : Monitor :=
  let resolved := monitor.ack.isNone &&
    match monitor.mode with
    | .originals => monitor.lower.phase == .done && monitor.upper.phase == .done
    | .recovery => monitor.retry.phase == .done
    | _ => false
  if resolved then
    match G.senderRecovery config.toConfig state with
    | none => monitor.invalid
    | some recovery =>
      if recovery.outstanding.isEmpty then { monitor with mode := .needRead, waiting := false }
      else { monitor with mode := .recovery, waiting := true }
  else monitor

def recordData (monitor : Monitor) (lane : Lane) (actual : Step input) : Monitor :=
  match lane.refs.dataReceipt, actual.result.application with
  | some index, some (_, operation) =>
    { monitor with
      dataReceipts := monitor.dataReceipts ++ [index],
      releaseStamps := if operation.releasedPayload.isEmpty then monitor.releaseStamps
        else monitor.releaseStamps ++ [operation.stamp] }
  | _, _ => monitor.invalid

def dataLane (config : Config) (lane : Lane) (actual : Step input) : Lane :=
  Lane.ofGap <| match lane.phase with
  | .dataIngress => G.observeAssignment lane.toGap actual true .dataTicket
  | .dataTicket => G.observeService lane.toGap actual true .dataLink
  | .dataLink => G.observeReceipt config.toConfig lane.toGap actual true .done
  | _ => lane.toGap.invalid

def ackLane (config : Config) (lane : Lane) (actual : Step input) : Lane :=
  Lane.ofGap <| match lane.phase with
  | .needAck => G.observeOutput config.toConfig lane.toGap actual false .ackIngress
  | .ackIngress => G.observeAssignment lane.toGap actual false .ackTicket
  | .ackTicket => G.observeService lane.toGap actual false .ackLink
  | .ackLink => G.observeReceipt config.toConfig lane.toGap actual false .done
  | _ => lane.toGap.invalid

def observeData (config : Config) (monitor : Monitor) (actual : Step input) (target : DropTarget) : Monitor :=
  let before := match target with
    | .lower => monitor.lower
    | .upper => monitor.upper
    | .retry => monitor.retry
    | .ack => { phase := .invalid }
  let lane := dataLane config before actual
  if lane.phase == .invalid then monitor.invalid
  else
    let updated := match target with
      | .lower => { monitor with lower := lane, lastOriginal := some .lower }
      | .upper => { monitor with upper := lane, lastOriginal := some .upper }
      | .retry => { monitor with retry := lane }
      | .ack => monitor.invalid
    if lane.phase == .done then
      let recorded := recordData updated lane actual
      { recorded with ack := some { phase := .needAck, refs := lane.refs }, waiting := false }
    else updated

def observeAck (config : Config) (monitor : Monitor) (actual : Step input) (before : Lane) : Monitor :=
  let lane := ackLane config before actual
  if lane.phase == .invalid then monitor.invalid
  else if lane.phase == .done then
    match lane.refs.ackReceipt with
    | none => monitor.invalid
    | some index => normalize config actual.result.state
        { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [index] }
  else { monitor with ack := some lane }

def observeSend (config : Config) (monitor : Monitor) (actual : Step input) (target : Original) : Monitor :=
  let before := match target with | .lower => monitor.lower | .upper => monitor.upper
  let lane := Lane.ofGap (G.observeOutput config.toConfig before.toGap actual true .dataIngress)
  if lane.phase == .invalid then monitor.invalid
  else match target with
    | .lower => { monitor with lower := lane }
    | .upper => { monitor with upper := lane }

def observeDrop (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat) : Monitor :=
  match dropTarget config actual.before monitor id with
  | none => monitor.invalid
  | some target =>
    let charged := { monitor with drops := monitor.drops ++ [id] }
    let updated := match target with
      | .lower => { charged with lower := { charged.lower with phase := .done } }
      | .upper => { charged with upper := { charged.upper with phase := .done } }
      | .retry => { charged with retry := { charged.retry with phase := .done } }
      | .ack => { charged with ack := none }
    normalize config actual.result.state updated

def observeTimeout (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  let lane := Lane.ofGap (G.observeOutput config.toConfig monitor.retry.toGap actual true .dataIngress)
  if lane.phase == .invalid then monitor.invalid
  else { monitor with retry := lane, waiting := false, retries := monitor.retries + 1 }

def observeRead (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  match actual.result.application with
  | some (actor, operation) =>
    if actor == config.sender.other && actual.result.read == config.bytes then
      { monitor with mode := .done, waiting := false, readStamp := some operation.stamp, readBytes := actual.result.read }
    else monitor.invalid
  | none => monitor.invalid

def observeOrdinary (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  match monitor.mode with
  | .originals =>
    if monitor.lower.phase == .needSend then observeSend config monitor actual .lower
    else if monitor.upper.phase == .needSend then observeSend config monitor actual .upper
    else match monitor.ack with
      | some lane => observeAck config monitor actual lane
      | none =>
        if servesOption (laneDemand config actual.before monitor monitor.lower) actual.event then
          observeData config monitor actual .lower
        else if servesOption (laneDemand config actual.before monitor monitor.upper) actual.event then
          observeData config monitor actual .upper
        else monitor.invalid
  | .recovery =>
    match monitor.ack with
    | some lane => observeAck config monitor actual lane
    | none => if monitor.waiting then monitor.invalid else observeData config monitor actual .retry
  | .needRead => observeRead config monitor actual
  | .done | .invalid => monitor.invalid

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event then
    match actual.event with
    | .advanceClock .. => monitor
    | .dropPacket id => observeDrop config monitor actual id
    | .timeout _ true => observeTimeout config monitor actual
    | _ => observeOrdinary config monitor actual
  else monitor.invalid

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
  ⟨S.stateAt initial steps index, monitorAt config monitor steps index⟩

def Trace.prefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor) :
    Theory.BoundedProgress.Prefix (system input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := S.eventAt steps
  checked index within := by
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace index within
    exact ⟨actual, before, event, after, (monitorAt_next config monitor steps found).symm⟩

def Trace.guardedPrefix (trace : Trace input initial events steps final remaining) (config : Config) (monitor : Monitor)
    (actions : ∀ index, index < steps.length → Allowed config (S.stateAt initial steps index)
      (monitorAt config monitor steps index) (S.eventAt steps index)) :
    Theory.BoundedProgress.Prefix (guardedSystem input config) where
  length := steps.length
  state := stateAt config initial monitor steps
  action := S.eventAt steps
  checked index within := ⟨actions index within, (Trace.prefix trace config monitor).checked index within⟩

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

end Netlib.Check.CampusTCPTwoProgressMonitor
