import Netlib.Check.CampusTCPTwoExchangeMonitor

/-!
# One exchange through a planned gateway transfer

The first resolved original path exposes the pause demand.
Transfer controls retain the exchange monitor and its global counters.
Assignments use the ingress of the actual current owner.
-/

namespace Netlib.Check.CampusTCPTwoTransferMonitor

open CampusTCPModel CampusTCPEnabled

namespace X
export CampusTCPTwoExchangeMonitor (Config Monitor Demand nextDemand serves allowed observe)
end X
namespace L
export CampusTCPTwoProgressMonitor (observeData)
end L
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

structure Config where
  exchange : X.Config
  ingress : Gateway → Actor → I.InterfaceRef
  executionNS : I.NamespaceRef

def Config.at (config : Config) (state : State input) : X.Config :=
  { config.exchange with forward :=
    { config.exchange.forward with
      clientIngress := config.ingress (state.owner .client) .client
      serverIngress := config.ingress (state.owner .server) .server } }

inductive Control where
  | pause | capture | install | clientRoute | serverRoute | fence | resume
  deriving Repr, BEq, DecidableEq

def Control.event (config : Config) : Control → Event
  | .pause => .pause
  | .capture => .stageCheckpoint
  | .install => .installCheckpoint config.executionNS
  | .clientRoute => .switchRoute .client .standby
  | .serverRoute => .switchRoute .server .standby
  | .fence => .fencePrimary
  | .resume => .resume

def Control.serves (config : Config) : Control → Event → Bool
  | .pause, .pause | .capture, .stageCheckpoint | .fence, .fencePrimary | .resume, .resume => true
  | .install, .installCheckpoint ns => ns == config.executionNS
  | .clientRoute, .switchRoute .client .standby | .serverRoute, .switchRoute .server .standby => true
  | _, _ => false

inductive Mode where
  | armed | capture | install | clientRoute | serverRoute | fence | resume | finished | invalid
  deriving Repr, BEq, DecidableEq

def Control.after : Control → Mode
  | .pause => .capture
  | .capture => .install
  | .install => .clientRoute
  | .clientRoute => .serverRoute
  | .serverRoute => .fence
  | .fence => .resume
  | .resume => .finished

structure Monitor where
  mode : Mode := .armed
  exchange : X.Monitor := .initial
  controls : List (Control × Nat) := []
  deriving Repr, BEq, DecidableEq

def Monitor.initial : Monitor := {}

def Monitor.invalid (monitor : Monitor) : Monitor := { monitor with mode := .invalid }

def transferDue (monitor : X.Monitor) : Bool :=
  monitor.mode == .forward && monitor.forward.mode == .originals &&
    (monitor.forward.lower.phase == .done || monitor.forward.upper.phase == .done)

def controlDemand (monitor : Monitor) : Option Control :=
  match monitor.mode with
  | .armed => if transferDue monitor.exchange then some .pause else none
  | .capture => some .capture
  | .install => some .install
  | .clientRoute => some .clientRoute
  | .serverRoute => some .serverRoute
  | .fence => some .fence
  | .resume => some .resume
  | .finished | .invalid => none

inductive Demand where
  | exchange (demand : X.Demand)
  | transfer (control : Control)
  | drain (ticket : Nat)
  deriving BEq, DecidableEq

def drainServes (ticket : Nat) : Event → Bool
  | .serve selected none => decide (selected = ticket)
  | _ => false

def serves (config : Config) : Demand → Event → Bool
  | .exchange demand, event => X.serves demand event
  | .transfer control, event => control.serves config event
  | .drain ticket, event => drainServes ticket event

def drainTicket (state : State input) (monitor : Monitor) : Option Nat :=
  if monitor.mode == .capture then
    (state.work.pending.find? (fun item => decide (item.value.gateway = .primary))).map (·.id)
  else none

def nextDemand (config : Config) (state : State input) (monitor : Monitor) : Option Demand :=
  if decide (monitor.mode = .invalid) then none
  else match drainTicket state monitor with
    | some ticket => some (.drain ticket)
    | none => match controlDemand monitor with
      | some control => some (.transfer control)
      | none => (X.nextDemand (config.at state) state monitor.exchange).map Demand.exchange

def allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Bool :=
  if decide (monitor.mode = .invalid) then false
  else match drainTicket state monitor with
    | some ticket =>
      match event with
      | .advanceClock .. => X.allowed (config.at state) state monitor.exchange event
      | _ => drainServes ticket event
    | none => match controlDemand monitor with
      | none => X.allowed (config.at state) state monitor.exchange event
      | some control =>
        match event with
        | .advanceClock .. => X.allowed (config.at state) state monitor.exchange event
        | _ => control.serves config event

def Allowed (config : Config) (state : State input) (monitor : Monitor) (event : Event) : Prop :=
  allowed config state monitor event = true

def ordinary (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  let next := X.observe (config.at actual.before) monitor.exchange actual
  if decide (next.mode = .invalid) then monitor.invalid else { monitor with exchange := next }

def observeDrain (config : Config) (monitor : Monitor) (actual : Step input) (ticket : Nat) : Monitor :=
  match actual.result.service with
  | none => monitor.invalid
  | some served =>
    if decide (served.ticket.id = ticket ∧ served.ticket.value.gateway = .primary) then
      let before := monitor.exchange.forward
      let next :=
        if before.lower.phase == .dataTicket && before.lower.refs.dataTicket == some ticket then
          L.observeData (config.at actual.before).forward before actual .lower
        else if before.upper.phase == .dataTicket && before.upper.refs.dataTicket == some ticket then
          L.observeData (config.at actual.before).forward before actual .upper
        else before
      if decide (next.mode = .invalid) then monitor.invalid
      else { monitor with exchange := { monitor.exchange with forward := next, slots := monitor.exchange.slots + 1 } }
    else monitor.invalid

def observe (config : Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event then
    match drainTicket actual.before monitor with
    | some ticket =>
      match actual.event with
      | .advanceClock .. => ordinary config monitor actual
      | _ => observeDrain config monitor actual ticket
    | none => match controlDemand monitor with
      | none => ordinary config monitor actual
      | some control =>
        match actual.event with
        | .advanceClock .. => ordinary config monitor actual
        | _ =>
          { mode := control.after
            exchange := { monitor.exchange with slots := monitor.exchange.slots + 1 }
            controls := monitor.controls ++ [(control, monitor.exchange.slots)] }
  else monitor.invalid

def monitorAt (config : Config) (initial : Monitor) : List (Step input) → Nat → Monitor
  | [], _ => initial
  | _ :: _, 0 => initial
  | actual :: rest, slot + 1 => monitorAt config (observe config initial actual) rest slot

@[simp] theorem monitorAt_zero (config : Config) (initial : Monitor) (steps : List (Step input)) :
    monitorAt config initial steps 0 = initial := by cases steps <;> rfl

theorem monitorAt_length (config : Config) (initial : Monitor) (steps : List (Step input)) :
    monitorAt config initial steps steps.length = steps.foldl (observe config) initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons actual rest ih =>
    simpa only [List.length_cons, monitorAt, List.foldl_cons] using ih (observe config initial actual)

def pendingAt (config : Config) (initial : State input) (monitor : Monitor)
    (steps : List (Step input)) (slot : Nat) : Option Demand :=
  nextDemand config (S.stateAt initial steps slot) (monitorAt config monitor steps slot)

def Serviced (config : Config) (initial : State input) (monitor : Monitor)
    (steps : List (Step input)) (bound : Nat) : Prop :=
  Theory.BoundedServiceCheck.Serviced steps.length (pendingAt config initial monitor steps)
    (S.eventAt steps) (serves config) bound

def check (config : Config) (initial : State input) (monitor : Monitor)
    (steps : List (Step input)) (bound : Nat) : Bool :=
  Theory.BoundedServiceCheck.check steps.length (pendingAt config initial monitor steps)
    (S.eventAt steps) (serves config) bound

theorem check_correct (config : Config) (initial : State input) (monitor : Monitor)
    (steps : List (Step input)) (bound : Nat) :
    check config initial monitor steps bound = true ↔ Serviced config initial monitor steps bound :=
  Theory.BoundedServiceCheck.check_correct _ _ _ _ _

def actions (config : Config) (initial : State input) (monitor : Monitor) : List (Step input) → Bool
  | [] => true
  | actual :: rest =>
    allowed config initial monitor actual.event &&
      actions config actual.result.state (observe config monitor actual) rest

theorem actions_correct (config : Config) (initial : State input) (monitor : Monitor) (steps : List (Step input)) :
    actions config initial monitor steps = true ↔
      ∀ slot, slot < steps.length → Allowed config (S.stateAt initial steps slot)
        (monitorAt config monitor steps slot) (S.eventAt steps slot) := by
  induction steps generalizing initial monitor with
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

end Netlib.Check.CampusTCPTwoTransferMonitor
