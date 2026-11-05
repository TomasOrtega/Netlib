import Netlib.Check.CampusTCPService
import Netlib.Check.TCPHandshake
import Netlib.Protocol.TCP.ApplicationTraceFacts
import Netlib.Theory.Outstanding
import Netlib.Examples.CampusDirect

/-!
# Authenticated campus TCP execution

Endpoint outputs allocate immutable work items.
Service uses the current stored policy, actual ingress guard, and tracked NAT pipeline.
Receiver inputs come from actual earlier gateway emissions.
-/

namespace Netlib.Check.CampusTCPModel

open Packet Protocol
namespace T
export Netlib.Protocol.TCP.ApplicationTrace (Step Event Chain OutputOrigin OutputAt)
end T
namespace H
export Netlib.Check.TCPHandshake (Stage Completed)
end H
namespace W
export Netlib.Protocol.TCP.WireForwarding (Source Emission)
end W
namespace I
export Netlib.Protocol.IngressAttachment (NamespaceRef InterfaceRef ExpectedAttachment)
end I
namespace Work
export Netlib.Theory.Outstanding (State Item Completed enqueue complete)
end Work

inductive Actor where
  | client | server
  deriving Repr, BEq, DecidableEq

def Actor.other : Actor → Actor | .client => .server | .server => .client
def Actor.direction : Actor → FlowNAT.Direction | .client => .original | .server => .reply
def Actor.nextHop : Actor → String | .client => "server" | .server => "client"

structure Specification where
  id : String
  direction : FlowNAT.Direction
  ingress : I.InterfaceRef
  traffic : Match

structure Guard where
  id : String
  source : Import.NftablesIngress.Snapshot

structure Input where
  context : CampusTCPService.Context
  application : Scope
  scopes : ∀ requirement ∈ context.requirements, requirement.scope = application
  initialConfig : Check.ConntrackLifecycle.Config
  initialGuard : Guard
  guards : List Guard
  specifications : List Specification
  authenticationPort : I.InterfaceRef
  live : List I.InterfaceRef
  active : TCP.Handshake.Local
  passive : TCP.Handshake.Local
  zone : Nat

structure Cursor (seed : TCP.Endpoint.State) where
  current : TCP.Endpoint.State
  valid : current.Valid
  steps : List T.Step
  chain : T.Chain seed steps current
  ordered : TCP.ApplicationTrace.Chronological steps

def Cursor.initial (seed : TCP.Endpoint.State) (valid : seed.Valid) : Cursor seed :=
  ⟨seed, valid, [], .nil seed, .nil⟩

structure Applied (before : Cursor seed) where
  step : T.Step
  same : step.before = before.current
  cursor : Cursor seed
  history : cursor.steps = before.steps ++ [step]
  state : cursor.current = step.result.state

def Cursor.apply (before : Cursor seed) (event : T.Event) (stamp : Nat) : Except String (Applied before) := do
  if earlier : before.steps.all (fun step => decide (step.stamp < stamp)) = true then
    let step := TCP.ApplicationTrace.Step.make before.current before.valid event stamp
    have prior : ∀ old ∈ before.steps, old.stamp < step.stamp := by
      change ∀ old ∈ before.steps, old.stamp < stamp
      simpa only [List.all_eq_true, decide_eq_true_eq] using earlier
    let cursor : Cursor seed := ⟨step.result.state, step.valid, before.steps ++ [step], before.chain.snoc,
      TCP.ApplicationTrace.chronological_snoc before.ordered prior⟩
    return ⟨step, rfl, cursor, rfl, rfl⟩
  else throw "Application events must occur after the endpoint's earlier events."

structure Applications (complete : H.Completed active passive) where
  client : Cursor complete.certificate.activeSeed
  server : Cursor complete.certificate.passiveSeed

def Applications.initial (complete : H.Completed active passive) : Applications complete :=
  ⟨Cursor.initial _ complete.certificate.valid.1, Cursor.initial _ complete.certificate.valid.2⟩

inductive Connection (active passive : TCP.Handshake.Local) where
  | startup (stage : H.Stage active passive) (pending : stage.exchangeComplete = false)
  | application (complete : H.Completed active passive) (endpoints : Applications complete)

def Connection.ofStage : (stage : H.Stage active passive) → Connection active passive
  | .idle => .startup .idle rfl
  | .opened value => .startup (.opened value) rfl
  | .answered value => .startup (.answered value) rfl
  | .acknowledged value => .startup (.acknowledged value) rfl
  | .complete value => .application value (Applications.initial value)

inductive Produced (active passive : TCP.Handshake.Local) where
  | startup (step : TCPHandshake.Step active passive) (output : TCP.EstablishedReceive.Input)
      (present : step.result.output = some output)
  | application (actor : Actor) (step : T.Step) (output : TCP.EstablishedReceive.Input)
      (origin : T.OutputOrigin step output)

def Produced.actor : Produced active passive → Actor
  | .startup step _ _ => match step.event with | .listenSyn .. => .server | _ => .client
  | .application actor _ _ _ => actor

def Produced.time : Produced active passive → Nat
  | .startup step _ _ => step.index
  | .application _ step _ _ => step.stamp

def Produced.output : Produced active passive → TCP.EstablishedReceive.Input
  | .startup _ output _ | .application _ _ output _ => output

def Produced.source (value : Produced active passive) : W.Source := TCP.WireForwarding.Source.ofInput value.output

structure Ticket (active passive : TCP.Handshake.Local) where
  outputIndex : Nat
  produced : Produced active passive
  ingress : I.InterfaceRef

def Ticket.source (value : Ticket active passive) : W.Source := value.produced.source

structure Staged where
  specification : String
  value : I.ExpectedAttachment

structure Served (input : Input) where
  time : Nat
  ticket : Work.Item (Ticket input.active input.passive)
  before : CampusTCPService.Before
  evidence : CampusTCPService.Evidence input.context before ticket.value.source input.zone ticket.value.ingress
  computed : CampusTCPService.run input.context before ticket.value.source input.zone ticket.value.ingress = .ok evidence
  observed : Bool

def Served.routeMatched (value : Served input) : Bool :=
  match value.evidence.processing with
  | none => true
  | some processing => match processing.outcome.output with
    | none => true
    | some _ => decide (processing.outcome.nextHop = some value.ticket.value.produced.actor.nextHop)

def Served.passed (value : Served input) : Bool := value.evidence.passed && value.routeMatched && value.observed

structure Receipt (input : Input) where
  time : Nat
  serviceIndex : Nat
  served : Served input
  emission : W.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  received : TCP.EstablishedReceive.Input
  bytes : received.bytes = emission.bytes
  actor : Actor
  receiver : actor = served.ticket.value.produced.actor.other
  application : Option T.Step

theorem Receipt.bytePath (value : Receipt input) :
    TCP.ApplicationTrace.BytePath value.served.ticket.value.produced.output value.received := by
  have generated := value.emission.bytePath value.served.ticket.value.source
  exact .trans generated (.direct value.bytes)

structure State (input : Input) where
  time : Nat := 0
  authentication : Nat := 0
  configuration : Check.ConntrackLifecycle.Config
  guard : Guard
  live : List I.InterfaceRef
  attachments : List Staged := []
  tracker : Protocol.ConntrackLifecycle.State := .initial
  admission : TCP.Admission.State := .initial
  connection : Connection input.active input.passive := .startup .idle rfl
  outputs : List (Produced input.active input.passive) := []
  work : Work.State (Ticket input.active input.passive) := .initial
  services : List (Served input) := []
  receipts : List (Receipt input) := []

def Input.initial (input : Input) : State input :=
  { configuration := input.initialConfig, guard := input.initialGuard, live := input.live }

def beforeService (input : Input) (before : State input) : CampusTCPService.Before :=
  ⟨before.authentication, before.configuration, before.guard.source, before.live,
    before.attachments.map (·.value), before.tracker, before.admission⟩

inductive Event where
  | authentication (index : Nat)
  | install (configuration : String)
  | stage (specification : String)
  | installGuard (guard : String)
  | open (remote : TCP.Handshake.Socket) (policy : Bool)
  | write (actor : Actor) (bytes : List UInt8)
  | send (actor : Actor) (count : Nat) (policy : Bool)
  | read (actor : Actor) (count : Nat)
  | emitAck (actor : Actor) (policy : Bool)
  | assign (output : Nat) (ingress : I.InterfaceRef)
  | serve (ticket : Nat) (observed : Option (List UInt8 × Option (List UInt8)))
  | deliver (service : Nat) (bytes : List UInt8) (policy : Bool)

inductive Error where
  | input (reason : String)
  | unsupported (reason : String)
  deriving Repr, BEq, DecidableEq

def Error.message : Error → String | .input text | .unsupported text => text

def admissionReason : TCP.Admission.Unsupported → String
  | .missingHistory => "missingHistory" | .replacement => "replacement" | .direction => "direction"
  | .flags => "flags" | .options => "options" | .data => "data" | .sequence => "sequence"
  | .acknowledgment => "acknowledgment" | .window => "window" | .epoch => "epoch" | .historyLost => "historyLost"

structure Effect (input : Input) where
  state : State input
  passed : Bool := true
  supported : Bool := true
  decision : String := "accepted"
  output : Option (Produced input.active input.passive) := none
  service : Option (Served input) := none
  receipt : Option (Receipt input) := none
  startup : Option (TCPHandshake.Step input.active input.passive) := none
  application : Option (Actor × T.Step) := none
  read : List UInt8 := []

def get (values : List α) (index : Nat) (message : String) : Except Error α :=
  match values[index]? with | none => .error (.input message) | some value => .ok value

def parsed (value : Except String α) : Except Error α := value.mapError Error.input

def unsupported (before : State input) (reason : String) : Effect input :=
  { state := before, supported := false, decision := reason }

def publish (before : State input) (production : Produced input.active input.passive) : State input :=
  { before with outputs := before.outputs ++ [production] }

def startup (input : Input) (before : State input) (event : TCPHandshake.Event) : Except Error (Effect input) := do
  match before.connection with
  | .application .. => return unsupported before "startupCopy"
  | .startup stage _ =>
    match computed : TCPHandshake.evaluate input.active input.passive stage before.time event with
    | .error reason => throw (.input reason)
    | .ok result =>
      let step : TCPHandshake.Step input.active input.passive := ⟨stage, before.time, event, result, computed⟩
      let after := { before with connection := Connection.ofStage result.state }
      let outcome : Effect input := {
        state := after
        supported := step.supported
        startup := some step
        decision := if step.supported then "accepted" else "startup" }
      match present : result.output with
      | none => return outcome
      | some output =>
        let produced := Produced.startup step output present
        return { outcome with state := publish after produced, output := some produced }

def applyApplication (input : Input) (before : State input) (actor : Actor) (event : T.Event) :
    Except Error (Effect input) := do
  match before.connection with
  | .startup .. => return unsupported before "phase"
  | .application complete endpoints =>
    let (after, step) ← match actor with
      | .client => do
        let applied ← parsed (endpoints.client.apply event before.time)
        pure ({ endpoints with client := applied.cursor }, applied.step)
      | .server => do
        let applied ← parsed (endpoints.server.apply event before.time)
        pure ({ endpoints with server := applied.cursor }, applied.step)
    let next := { before with connection := .application complete after }
    let result : Effect input := {
      state := next
      supported := step.supported
      read := step.result.read
      application := some (actor, step)
      decision := if step.supported then "accepted" else "endpoint" }
    match step.result.output with
    | none => return result
    | some _ =>
      let actual ← parsed (TCP.ApplicationTrace.stepOutput step)
      let produced := Produced.application actor step actual.val actual.property
      return { result with state := publish next produced, output := some produced }

def observe (seen : Option (List UInt8 × Option (List UInt8))) (source : W.Source)
    (output : Option (W.Emission source.packet)) : Bool :=
  match seen with
  | none => true
  | some (bytes, after) => decide (bytes = source.bytes) && decide (after = output.map (·.bytes))

def process (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  match event with
  | .authentication index =>
    if index ≠ before.authentication then throw (.input "Consume the next authentication observation exactly once.")
    if available : before.authentication < input.context.authentication.observations.length then
      let source := input.context.authentication.observations[before.authentication]'available
      let finding := Check.EAP.finding source (SessionInstallation.current input.context.authentication (before.authentication + 1))
      return { state := { before with authentication := before.authentication + 1 }, passed := finding.passed }
    else throw (.input "No authentication observation remains.")
  | .install id =>
    let some configuration := input.context.configs.find? (·.id == id) | throw (.input "The configuration is unknown.")
    let certificate ← parsed (SessionInstallation.check input.context.authentication input.context.requirements
      before.authentication ⟨configuration.id, configuration.pipeline input.context.routing⟩ input.context.configs)
    return { state := { before with configuration }, passed := certificate.passed }
  | .stage id =>
    let some specification := input.specifications.find? (·.id == id) | throw (.input "The ingress specification is unknown.")
    let now := CampusTCPService.current input.context (beforeService input before)
    let attachment ← (IngressAttachment.stage now (CampusTCPService.current_safe _ _) input.authenticationPort
      specification.ingress specification.direction input.application specification.traffic).mapError (fun reason => .input reason.describe)
    return { state := { before with attachments := before.attachments ++ [⟨id, attachment⟩] } }
  | .installGuard id =>
    let some guard := input.guards.find? (·.id == id) | throw (.input "The ingress guard is unknown.")
    let now := CampusTCPService.current input.context (beforeService input before)
    let checked ← parsed (IngressGuard.check now input.context.executionNS (before.attachments.map (·.value)) []
      input.context.application guard.source)
    return { state := { before with guard }, passed := checked.passed }
  | .open remote policy => startup input before (.activeOpen remote policy)
  | .write actor bytes => applyApplication input before actor (.write bytes)
  | .send actor count policy => applyApplication input before actor (.send count policy)
  | .read actor count => applyApplication input before actor (.read count)
  | .emitAck actor policy => applyApplication input before actor (.emitAck policy)
  | .assign index ingress =>
    let produced ← get before.outputs index "The endpoint output reference is missing."
    let ticket : Ticket input.active input.passive := ⟨index, produced, ingress⟩
    return { state := { before with work := Work.enqueue before.work ticket } }
  | .serve id observed =>
    let completed ← (Work.complete before.work id).mapError (fun reason => .input reason.describe)
    let origin := beforeService input before
    match computed : CampusTCPService.run input.context origin completed.item.value.source input.zone completed.item.value.ingress with
    | .error (.input reason) => throw (.input reason)
    | .error (.unsupported reason) => return unsupported before (admissionReason reason)
    | .ok evidence =>
      let served : Served input := ⟨before.time, completed.item, origin, evidence, computed,
        observe observed completed.item.value.source evidence.output⟩
      let after := { before with
        work := completed.state
        tracker := evidence.tracker
        admission := evidence.admission
        services := before.services ++ [served] }
      return { state := after, passed := served.passed, service := some served }
  | .deliver index bytes policy =>
    let served ← get before.services index "The gateway service reference is missing."
    let chosen : { emission : W.Emission served.ticket.value.source.packet // served.evidence.output = some emission } ←
      match emitted : served.evidence.output with
      | none => throw (.input "The selected gateway service emitted no packet.")
      | some emission => pure ⟨emission, emitted⟩
    let emission := chosen.val
    let received ← parsed (TCP.EstablishedReceive.input bytes)
    if same : received.bytes = emission.bytes then
      let actor := served.ticket.value.produced.actor.other
      match served.ticket.value.produced with
      | .startup source _ _ =>
        let event ← match source.event with
          | .activeOpen .. => pure (TCPHandshake.Event.listenSyn bytes .rewrite policy)
          | .listenSyn .. => pure (TCPHandshake.Event.synSentSynAck bytes .rewrite policy)
          | .synSentSynAck .. => pure (TCPHandshake.Event.synReceivedAck bytes .rewrite)
          | .synReceivedAck .. => throw (.input "A final ACK receipt has no startup output.")
        let result ← startup input before event
        let receipt : Receipt input := ⟨before.time, index, served, emission, chosen.property, received, same, actor, rfl, none⟩
        return { result with state := { result.state with receipts := before.receipts ++ [receipt] }, receipt := some receipt }
      | .application _ _ _ _ =>
        let result ← applyApplication input before actor (.receive received)
        let step := result.application.map (·.2)
        let receipt : Receipt input := ⟨before.time, index, served, emission, chosen.property, received, same, actor, rfl, step⟩
        return { result with state := { result.state with receipts := before.receipts ++ [receipt] }, receipt := some receipt }
    else throw (.input "Receiver bytes must equal the selected actual gateway emission.")

def step (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  let result ← process input before event
  return { result with state := { result.state with time := before.time + 1 } }

structure Step (input : Input) where
  before : State input
  event : Event
  result : Effect input
  computed : step input before event = .ok result

theorem Step.processed (value : Step input) :
    ∃ effect, process input value.before value.event = .ok effect ∧
      value.result = { effect with state := { effect.state with time := value.before.time + 1 } } := by
  have accepted := value.computed
  unfold step at accepted
  cases observed : process input value.before value.event with
  | error reason => simp [observed, bind, Except.bind] at accepted
  | ok result =>
    simp only [observed, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    exact ⟨result, rfl, accepted.symm⟩

theorem Step.clock (value : Step input) : value.result.state.time = value.before.time + 1 := by
  have accepted := value.computed
  unfold step at accepted
  cases observed : process input value.before value.event with
  | error reason => simp [observed, bind, Except.bind] at accepted
  | ok result =>
    simp only [observed, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    rw [← accepted]

inductive Trace (input : Input) : State input → List Event → List (Step input) → State input → List Event → Prop where
  | done (state) : Trace input state [] [] state []
  | stop (head : Step input) (unsupported : head.result.supported = false) (tail : List Event) :
      Trace input head.before (head.event :: tail) [head] head.result.state tail
  | next (head : Step input) (supported : head.result.supported = true)
      (rest : Trace input head.result.state tail steps final remaining) :
      Trace input head.before (head.event :: tail) (head :: steps) final remaining

structure Report (input : Input) (events : List Event) where
  final : State input
  steps : List (Step input)
  remaining : List Event
  trace : Trace input input.initial events steps final remaining

private structure Run (input : Input) (before : State input) (events : List Event) where
  final : State input
  steps : List (Step input)
  remaining : List Event
  trace : Trace input before events steps final remaining

private def run (input : Input) (before : State input) :
    (events : List Event) → Except Error (Run input before events)
  | [] => .ok ⟨before, [], [], .done before⟩
  | event :: events => do
    match computed : step input before event with
    | .error reason => throw reason
    | .ok result =>
      let head : Step input := ⟨before, event, result, computed⟩
      if supported : result.supported = true then
        let rest ← run input result.state events
        return ⟨rest.final, head :: rest.steps, rest.remaining, .next head supported rest.trace⟩
      else
        have blocked : result.supported = false := by cases actual : result.supported <;> simp_all
        return ⟨result.state, [head], events, .stop head blocked events⟩

def Input.check (input : Input) (events : List Event) : Except Error (Report input events) := do
  let result ← run input input.initial events
  return ⟨result.final, result.steps, result.remaining, result.trace⟩

def Report.supported (report : Report input events) : Bool := report.steps.all (·.result.supported)
def Report.compliant (report : Report input events) : Bool := report.supported && report.steps.all (·.result.passed)

theorem Trace.covered (trace : Trace input initial events steps final remaining) :
    steps.map (·.event) ++ remaining = events := by
  induction trace with
  | done state => rfl
  | stop head _ _ => rfl
  | next head _ _ ih => simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem Trace.indices (trace : Trace input initial events steps final remaining) :
    steps.map (·.before.time) = List.range' initial.time steps.length := by
  induction trace with
  | done state => rfl
  | stop head _ _ => rfl
  | next head _ _ ih =>
    rw [head.clock] at ih
    simpa only [List.map_cons, List.length_cons, List.range'_succ] using congrArg (head.before.time :: ·) ih

theorem Report.indices (report : Report input events) :
    report.steps.map (·.before.time) = List.range' 0 report.steps.length := report.trace.indices

theorem Report.step_passed (report : Report input events) (compliant : report.compliant = true)
    (step : Step input) (member : step ∈ report.steps) : step.result.passed = true := by
  have pair : report.supported = true ∧ report.steps.all (·.result.passed) = true := by
    simpa only [Report.compliant, Bool.and_eq_true] using compliant
  have passed := pair.2
  exact (List.all_eq_true.mp passed) step member

theorem Report.step_supported (report : Report input events) (compliant : report.compliant = true)
    (step : Step input) (member : step ∈ report.steps) : step.result.supported = true := by
  have pair : report.steps.all (·.result.supported) = true ∧ report.steps.all (·.result.passed) = true := by
    simpa only [Report.compliant, Report.supported, Bool.and_eq_true] using compliant
  have passed := pair.1
  exact (List.all_eq_true.mp passed) step member

end Netlib.Check.CampusTCPModel
