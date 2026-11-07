import Netlib.Check.CampusTCPHistory
import Netlib.Check.TCPHandshake
import Netlib.Check.TCPHandshakeRecoveryEvaluate
import Netlib.Protocol.TCP.ApplicationTraceFacts
import Netlib.Theory.Outstanding
import Netlib.Theory.PacketCustody
import Netlib.Examples.CampusDirect

/-!
# Authenticated campus TCP execution

Endpoint outputs allocate immutable work items.
Service uses the current stored policy, actual ingress guard, and tracked NAT pipeline.
Receiver inputs come from actual earlier gateway emissions.
-/

namespace Netlib.Check.CampusTCPModel

open Packet Protocol
abbrev Gateway := StatefulFailover.Gateway
namespace T
export Netlib.Protocol.TCP.ApplicationTrace (Step Event Chain OutputOrigin OutputAt)
end T
namespace H
export Netlib.Check.TCPHandshake (Stage Completed)
end H
namespace C
export Netlib.Check.TCPHandshakeRecovery (State Step Emission Receipt Event)
end C
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
def Actor.leg : Actor → StatefulFailover.Leg | .client => .client | .server => .server
def Actor.recoverySide : Actor → TCPHandshakeRecovery.Side | .client => .active | .server => .passive
def Actor.ofRecovery : TCPHandshakeRecovery.Side → Actor | .active => .client | .passive => .server

structure Specification where
  id : String
  direction : FlowNAT.Direction
  ingress : I.InterfaceRef
  traffic : Match

structure Guard where
  id : String
  source : Import.NftablesIngress.Snapshot

structure Deployment where
  routing : Import.LinuxRoute.Snapshot
  configs : List Check.ConntrackLifecycle.Config
  executionNS : I.NamespaceRef
  initialConfig : Check.ConntrackLifecycle.Config
  initialGuard : Guard
  guards : List Guard
  specifications : List Specification
  authenticationPort : I.InterfaceRef
  live : List I.InterfaceRef

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
  standby : Option Deployment := none

def Input.primary (input : Input) : Deployment :=
  ⟨input.context.routing, input.context.configs, input.context.executionNS, input.initialConfig,
    input.initialGuard, input.guards, input.specifications, input.authenticationPort, input.live⟩

def Input.deployment (input : Input) : Gateway → Deployment
  | .primary => input.primary
  | .standby => input.standby.getD input.primary

def Input.configured (input : Input) : Gateway → Bool
  | .primary => true
  | .standby => input.standby.isSome

def Input.contextFor (input : Input) : Gateway → CampusTCPService.Context
  | .primary => input.context
  | .standby =>
    let deployment := input.deployment .standby
    { input.context with routing := deployment.routing, configs := deployment.configs, executionNS := deployment.executionNS }

@[simp] theorem Input.contextFor_authentication (input : Input) (gateway : Gateway) :
    (input.contextFor gateway).authentication = input.context.authentication := by cases gateway <;> rfl

@[simp] theorem Input.contextFor_requirements (input : Input) (gateway : Gateway) :
    (input.contextFor gateway).requirements = input.context.requirements := by cases gateway <;> rfl

@[simp] theorem Input.contextFor_application (input : Input) (gateway : Gateway) :
    (input.contextFor gateway).application = input.context.application := by cases gateway <;> rfl

structure Cursor (seed : TCP.Endpoint.State) where
  current : TCP.Endpoint.State
  valid : current.Valid
  steps : List T.Step
  chain : T.Chain seed steps current
  ordered : TCP.ApplicationTrace.Chronological steps

def Cursor.initial (seed : TCP.Endpoint.State) (valid : seed.Valid) : Cursor seed :=
  ⟨seed, valid, [], .nil seed, .nil⟩

def Cursor.ofPreData (current : TCPHandshakeRecovery.PreData seed) : Cursor seed :=
  ⟨current.current, current.valid, current.steps, current.chain, current.ordered⟩

def Cursor.beforeTransport (cursor : Cursor seed) : Bool :=
  cursor.steps.all (fun step => match step.event with | .send .. | .receive .. => false | _ => true)

def Cursor.beforeRecoveryTransport (cursor : Cursor seed) (drained : Nat) : Bool :=
  cursor.steps.all fun step => match step.event with
    | .send .. => false
    | .receive packet =>
      decide (step.stamp < drained) && decide (TCP.Handshake.Profile packet 16) &&
        (match step.result.decision with | .accepted (.receive 0 0) => true | _ => false) &&
        step.result.output.isNone && step.result.read.isEmpty
    | _ => true

theorem Cursor.beforeTransport_no_send (cursor : Cursor seed) (ready : cursor.beforeTransport = true)
    (step : T.Step) (member : step ∈ cursor.steps) (count : Nat) (policy : Bool) :
    step.event ≠ .send count policy := by
  have selected := (List.all_eq_true.mp ready) step member
  intro event
  simp only [event] at selected
  contradiction

theorem Cursor.beforeTransport_no_receive (cursor : Cursor seed) (ready : cursor.beforeTransport = true)
    (step : T.Step) (member : step ∈ cursor.steps) (packet : TCP.EstablishedReceive.Input) :
    step.event ≠ .receive packet := by
  have selected := (List.all_eq_true.mp ready) step member
  intro event
  simp only [event] at selected
  contradiction

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
  | recovering (current : C.State active passive)
  | application (complete : H.Completed active passive) (endpoints : Applications complete)

def Connection.admissionMode : Connection active passive → TCP.AdmissionExecution.Mode
  | .recovering _ => .startupRecovery
  | _ => .ordinary

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
  | recovery (step : C.Step active passive) (emission : C.Emission)
      (present : step.result.output = some emission)

def Produced.actor : Produced active passive → Actor
  | .startup step _ _ => match step.event with | .listenSyn .. => .server | _ => .client
  | .application actor _ _ _ => actor
  | .recovery _ emission _ => Actor.ofRecovery emission.actor

def Produced.time : Produced active passive → Nat
  | .startup step _ _ => step.index
  | .application _ step _ _ => step.stamp
  | .recovery _ emission _ => emission.index

def Produced.output : Produced active passive → TCP.EstablishedReceive.Input
  | .startup _ output _ | .application _ _ output _ => output
  | .recovery _ emission _ => emission.packet

def Produced.isRecovery : Produced active passive → Bool
  | .recovery .. => true
  | _ => false

def Produced.source (value : Produced active passive) : W.Source := TCP.WireForwarding.Source.ofInput value.output

structure Ticket (active passive : TCP.Handshake.Local) where
  outputIndex : Nat
  produced : Produced active passive
  ingress : I.InterfaceRef
  gateway : Gateway
  routeEpoch : Nat

def Ticket.source (value : Ticket active passive) : W.Source := value.produced.source

structure Staged where
  specification : String
  value : I.ExpectedAttachment

structure Local where
  configuration : Check.ConntrackLifecycle.Config
  guard : Guard
  live : List I.InterfaceRef
  attachments : List Staged := []
  transport : TCP.Checkpoint.Gateway
  history : TCP.Checkpoint.History transport

def Local.initial (deployment : Deployment) : Local :=
  ⟨deployment.initialConfig, deployment.initialGuard, deployment.live, [], .initial, .initial⟩

structure CachedCheckpoint where
  id : Nat
  time : Nat
  snapshot : TCP.Checkpoint.Snapshot

structure InstalledCheckpoint where
  time : Nat
  checkpoint : CachedCheckpoint
  source : TCP.Checkpoint.Gateway
  history : TCP.Checkpoint.History source
  target : TCP.Checkpoint.Gateway
  installed : TCP.Checkpoint.Installation checkpoint.snapshot history target
  computed : TCP.Checkpoint.install checkpoint.snapshot history target = .ok installed

structure Served (input : Input) where
  time : Nat
  ticket : Work.Item (Ticket input.active input.passive)
  before : CampusTCPService.Before
  mode : TCP.AdmissionExecution.Mode := .ordinary
  evidence : CampusTCPService.Evidence (input.contextFor ticket.value.gateway) before ticket.value.source input.zone ticket.value.ingress mode
  computed : CampusTCPService.run (input.contextFor ticket.value.gateway) before ticket.value.source input.zone ticket.value.ingress 100000 mode = .ok evidence
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
  recovery : Option C.Receipt := none

theorem Receipt.bytePath (value : Receipt input) :
    TCP.ApplicationTrace.BytePath value.served.ticket.value.produced.output value.received := by
  have generated := value.emission.bytePath value.served.ticket.value.source
  exact .trans generated (.direct value.bytes)

inductive Transit (input : Input) where
  | ingress (outputIndex : Nat) (produced : Produced input.active input.passive)
  | link (serviceIndex : Nat) (served : Served input)
      (emission : W.Emission served.ticket.value.source.packet)
      (emitted : served.evidence.output = some emission)

def Transit.bytes : Transit input → List UInt8
  | .ingress _ produced => produced.source.bytes
  | .link _ _ emission _ => emission.bytes

def Transit.ingressAt (index : Nat) : Transit input → Bool
  | .ingress source _ => source == index
  | .link .. => false

def Transit.linkAt (index : Nat) : Transit input → Bool
  | .link source .. => source == index
  | .ingress .. => false

def Transit.isRecovery : Transit input → Bool
  | .ingress _ produced => produced.isRecovery
  | .link _ served _ _ => served.ticket.value.produced.isRecovery

abbrev Custody (input : Input) := Theory.PacketCustody.State (Transit input)

structure RecoveryArchive (active passive : TCP.Handshake.Local) where
  time : Nat
  current : C.State active passive
  complete : H.Completed active passive
  client : TCPHandshakeRecovery.PreData complete.certificate.activeSeed
  server : TCPHandshakeRecovery.PreData complete.certificate.passiveSeed
  phase : current.phase = .complete complete client server
  activeData : TCP.HandshakeTimer.Data
  activeHandoff : TCP.HandshakeTimer.handoff current.activeTimer = some activeData
  passiveData : TCP.HandshakeTimer.Data
  passiveHandoff : TCP.HandshakeTimer.handoff current.passiveTimer = some passiveData

def RecoveryArchive.data (archive : RecoveryArchive active passive) : Actor → TCP.HandshakeTimer.Data
  | .client => archive.activeData
  | .server => archive.passiveData

structure State (input : Input) where
  time : Nat := 0
  authentication : Nat := 0
  primary : Local
  standby : Local
  owners : StatefulFailover.Owners := {}
  routeEpoch : Nat := 0
  assignmentPaused : Bool := false
  primarySealed : Bool := false
  primaryFenced : Bool := false
  checkpoints : List CachedCheckpoint := []
  cache : Option CachedCheckpoint := none
  installation : Option InstalledCheckpoint := none
  connection : Connection input.active input.passive := .startup .idle rfl
  recoveryArchive : Option (RecoveryArchive input.active input.passive) := none
  outputs : List (Produced input.active input.passive) := []
  work : Work.State (Ticket input.active input.passive) := .initial
  services : List (Served input) := []
  receipts : List (Receipt input) := []
  custody : Custody input := .initial

def Input.initial (input : Input) : State input :=
  { primary := Local.initial input.primary, standby := Local.initial (input.deployment .standby) }

def State.resident (state : State input) : Gateway → Local
  | .primary => state.primary
  | .standby => state.standby

def State.write (state : State input) (gateway : Gateway) (resident : Local) : State input :=
  match gateway with
  | .primary => { state with primary := resident }
  | .standby => { state with standby := resident }

@[simp] theorem State.resident_write (state : State input) (gateway : Gateway) (resident : Local) :
    (state.write gateway resident).resident gateway = resident := by cases gateway <;> rfl

def State.configuration (state : State input) := state.primary.configuration
def State.guard (state : State input) := state.primary.guard
def State.live (state : State input) := state.primary.live
def State.attachments (state : State input) := state.primary.attachments
def State.tracker (state : State input) := state.primary.transport.tracker
def State.admission (state : State input) := state.primary.transport.admission
def State.owner (state : State input) (actor : Actor) := state.owners.get actor.leg
def State.outstanding (state : State input) (gateway : Gateway) : Nat :=
  (state.work.pending.filter (fun item => decide (item.value.gateway = gateway))).length

def beforeService (input : Input) (before : State input) (gateway : Gateway := .primary) : CampusTCPService.Before :=
  let resident := before.resident gateway
  ⟨before.authentication, resident.configuration, resident.guard.source, resident.live,
    resident.attachments.map (·.value), resident.transport.tracker, resident.transport.admission⟩

@[simp] theorem beforeService_after (input : Input) (before : State input) (gateway : Gateway) :
    (beforeService input before gateway).after = before.authentication := rfl

inductive Event where
  | authentication (index : Nat)
  | install (configuration : String)
  | stage (specification : String)
  | installGuard (guard : String)
  | installAt (gateway : Gateway) (configuration : String)
  | stageAt (gateway : Gateway) (specification : String)
  | installGuardAt (gateway : Gateway) (guard : String)
  | pause
  | stageCheckpoint
  | installCheckpoint (executionNS : I.NamespaceRef)
  | switchRoute (actor : Actor) (gateway : Gateway)
  | fencePrimary
  | resume
  | open (remote : TCP.Handshake.Socket) (policy : Bool)
  | write (actor : Actor) (bytes : List UInt8)
  | send (actor : Actor) (count : Nat) (policy : Bool)
  | enableRecovery (actor : Actor)
  | enableAck (actor : Actor)
  | dispatchAck (actor : Actor) (policy : Bool)
  | advanceClock (actor : Actor) (millis : Nat)
  | timeout (actor : Actor) (policy : Bool)
  | read (actor : Actor) (count : Nat)
  | emitAck (actor : Actor) (policy : Bool)
  | assign (output : Nat) (ingress : I.InterfaceRef)
  | serve (ticket : Nat) (observed : Option (List UInt8 × Option (List UInt8)))
  | deliver (service : Nat) (bytes : List UInt8) (policy : Bool)
  | copyPacket (packet : Nat)
  | dropPacket (packet : Nat)
  | openRecovering (remote : TCP.Handshake.Socket) (policy : Bool)
  | startupClock (actor : Actor) (millis : Nat)
  | startupTimeout (actor : Actor) (generation : Nat) (policy : Bool)
  | finishStartup
  | enableStartupRecovery (actor : Actor)

inductive Error where
  | input (reason : String)
  | unsupported (reason : String)
  deriving Repr, BEq, DecidableEq

def Error.message : Error → String | .input text | .unsupported text => text

def admissionReason : TCP.Admission.Unsupported → String
  | .missingHistory => "missingHistory" | .replacement => "replacement" | .direction => "direction"
  | .flags => "flags" | .options => "options" | .data => "data" | .sequence => "sequence"
  | .acknowledgment => "acknowledgment" | .window => "window" | .epoch => "epoch" | .historyLost => "historyLost"
  | .overlap => "overlap" | .conflict => "conflict"

structure Effect (input : Input) where
  state : State input
  passed : Bool := true
  supported : Bool := true
  decision : String := "accepted"
  output : Option (Produced input.active input.passive) := none
  service : Option (Served input) := none
  receipt : Option (Receipt input) := none
  startup : Option (TCPHandshake.Step input.active input.passive) := none
  recovery : Option (C.Step input.active input.passive) := none
  application : Option (Actor × T.Step) := none
  read : List UInt8 := []
  checkpoint : Option CachedCheckpoint := none
  installation : Option InstalledCheckpoint := none

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
  | .recovering _ => return unsupported before "startupMode"
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

def runRecovery (input : Input) (before : State input) (event : C.Event) : Except Error (Effect input) := do
  match before.connection with
  | .startup .. | .application .. => return unsupported before "startupRecoveryPhase"
  | .recovering current =>
    match computed : TCPHandshakeRecovery.evaluate current before.time event with
    | .error reason => throw (.input reason)
    | .ok result =>
      let actual : C.Step input.active input.passive := ⟨current, before.time, event, result, computed⟩
      let after := { before with connection := .recovering result.state }
      let outcome : Effect input := {
        state := after
        recovery := some actual
        application := result.application.map (fun pair => (Actor.ofRecovery pair.1, pair.2))
        read := (result.application.map (fun pair => pair.2.result.read)).getD []
        decision := match result.decision with
          | .accepted => "accepted"
          | .discarded => "startupDiscarded"
          | .obsolete => "startupObsolete" }
      match present : result.output with
      | none => return outcome
      | some emission =>
        let produced := Produced.recovery actual emission present
        return { outcome with state := publish after produced, output := some produced }

def openRecovering (input : Input) (before : State input) (remote : TCP.Handshake.Socket) (policy : Bool) :
    Except Error (Effect input) := do
  if before.recoveryArchive.isSome then throw (.input "Startup recovery is already closed.")
  match before.connection with
  | .startup .idle _ =>
    runRecovery input { before with connection := .recovering .initial } (.activeOpen remote policy)
  | _ => return unsupported before "startupRecoveryOpen"

def applyApplication (input : Input) (before : State input) (actor : Actor) (event : T.Event) :
    Except Error (Effect input) := do
  match before.connection with
  | .startup .. | .recovering _ => return unsupported before "phase"
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

def enableRecovery (input : Input) (before : State input) (actor : Actor) : Except Error (Effect input) :=
  applyApplication input before actor .enableRecovery

def enableStartupRecovery (input : Input) (before : State input) (actor : Actor) : Except Error (Effect input) :=
  match before.recoveryArchive with
  | none => .ok (unsupported before "startupRecoveryHandoff")
  | some archive => applyApplication input before actor (.enableStartupRecovery (archive.data actor))

def enableAck (input : Input) (before : State input) (actor : Actor) : Except Error (Effect input) := do
  match before.connection with
  | .startup .. | .recovering _ => applyApplication input before actor .enableAck
  | .application _ endpoints =>
    let recoveryReady := match before.recoveryArchive with
      | none => false
      | some archive => match actor with
        | .client => endpoints.client.beforeRecoveryTransport archive.time
        | .server => endpoints.server.beforeRecoveryTransport archive.time
    let permitted := match actor with
      | .client => endpoints.client.current.ackReaction.isSome || endpoints.client.beforeTransport || recoveryReady
      | .server => endpoints.server.current.ackReaction.isSome || endpoints.server.beforeTransport || recoveryReady
    if permitted then applyApplication input before actor .enableAck
    else throw (.input "Enable ACK reactions before this endpoint's send or receive operations.")

def finishStartup (input : Input) (before : State input) : Except Error (Effect input) := do
  if before.recoveryArchive.isSome then throw (.input "Startup recovery is already closed.")
  if before.work.pending.any (fun item => item.value.produced.isRecovery) then
    throw (.input "Process every recovery startup ticket before closing startup.")
  if before.custody.pending.any (fun item => item.value.payload.isRecovery) then
    throw (.input "Deliver or drop every recovery startup packet before closing startup.")
  match before.connection with
  | .startup .. | .application .. => return unsupported before "startupRecoveryDrain"
  | .recovering current =>
    match phase : current.phase with
    | .idle | .opened _ | .answered _ | .acknowledged .. =>
      throw (.input "Complete both startup acknowledgments before closing recovery startup.")
    | .complete complete client server =>
      match activeHandoff : TCP.HandshakeTimer.handoff current.activeTimer with
      | none => throw (.input "The active startup timer is not acknowledged.")
      | some activeData =>
        match passiveHandoff : TCP.HandshakeTimer.handoff current.passiveTimer with
        | none => throw (.input "The passive startup timer is not acknowledged.")
        | some passiveData =>
          let archive : RecoveryArchive input.active input.passive :=
            ⟨before.time, current, complete, client, server, phase, activeData, activeHandoff, passiveData, passiveHandoff⟩
          let endpoints : Applications complete := ⟨Cursor.ofPreData client, Cursor.ofPreData server⟩
          return { state := { before with connection := .application complete endpoints, recoveryArchive := some archive } }

def observe (seen : Option (List UInt8 × Option (List UInt8))) (source : W.Source)
    (output : Option (W.Emission source.packet)) : Bool :=
  match seen with
  | none => true
  | some (bytes, after) => decide (bytes = source.bytes) && decide (after = output.map (·.bytes))

def installConfiguration (input : Input) (before : State input) (gateway : Gateway) (id : String) :
    Except Error (Effect input) := do
  if !input.configured gateway then throw (.input "The selected gateway has no deployment.")
  let context := input.contextFor gateway
  let some configuration := context.configs.find? (·.id == id) | throw (.input "The configuration is unknown.")
  let certificate ← parsed (SessionInstallation.check context.authentication context.requirements
    before.authentication ⟨configuration.id, configuration.pipeline context.routing⟩ context.configs)
  return { state := before.write gateway { before.resident gateway with configuration }, passed := certificate.passed }

def stageAttachment (input : Input) (before : State input) (gateway : Gateway) (id : String) :
    Except Error (Effect input) := do
  if !input.configured gateway then throw (.input "The selected gateway has no deployment.")
  let deployment := input.deployment gateway
  let some specification := deployment.specifications.find? (·.id == id) | throw (.input "The ingress specification is unknown.")
  let context := input.contextFor gateway
  let now := CampusTCPService.current context (beforeService input before gateway)
  let attachment ← (IngressAttachment.stage now (CampusTCPService.current_safe _ _) deployment.authenticationPort
    specification.ingress specification.direction input.application specification.traffic).mapError (fun reason => .input reason.describe)
  let resident := before.resident gateway
  return { state := before.write gateway { resident with attachments := resident.attachments ++ [⟨id, attachment⟩] } }

def installIngress (input : Input) (before : State input) (gateway : Gateway) (id : String) :
    Except Error (Effect input) := do
  if !input.configured gateway then throw (.input "The selected gateway has no deployment.")
  let some guard := (input.deployment gateway).guards.find? (·.id == id) | throw (.input "The ingress guard is unknown.")
  let context := input.contextFor gateway
  let resident := before.resident gateway
  let now := CampusTCPService.current context (beforeService input before gateway)
  let checked ← parsed (IngressGuard.check now context.executionNS (resident.attachments.map (·.value)) [] context.application guard.source)
  return { state := before.write gateway { resident with guard }, passed := checked.passed }

def transferControl (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  if !input.configured .standby then throw (.input "Declare a standby deployment before planned transfer.")
  match event with
  | .pause =>
    if before.assignmentPaused || before.primarySealed || before.primaryFenced then
      throw (.input "Pause assignments before the selected transfer starts.")
    return { state := { before with assignmentPaused := true } }
  | .stageCheckpoint =>
    if before.primarySealed || before.primaryFenced then throw (.input "The source is sealed against new checkpoints.")
    match before.connection with
    | .startup .. | .recovering _ => throw (.input "Finish the startup exchange before checkpoint staging.")
    | .application .. =>
      let snapshot ← (TCP.Checkpoint.capture before.primary.history).mapError (fun reason => .input reason.message)
      let checkpoint : CachedCheckpoint := ⟨before.checkpoints.length, before.time, snapshot⟩
      return { state := { before with checkpoints := before.checkpoints ++ [checkpoint], cache := some checkpoint }, checkpoint := some checkpoint }
  | .installCheckpoint executionNS =>
    if !before.assignmentPaused then throw (.input "Pause new assignments before checkpoint installation.")
    if before.primarySealed || before.primaryFenced then throw (.input "The source transfer is already sealed.")
    if before.outstanding .primary != 0 then throw (.input "Process all primary tickets before checkpoint installation.")
    if executionNS != (input.deployment .standby).executionNS || before.standby.guard.source.ns != executionNS then
      throw (.input "The target namespace lifetime differs from the declared standby installation.")
    let some checkpoint := before.cache | throw (.input "Stage an actual source checkpoint before installation.")
    match computed : TCP.Checkpoint.install checkpoint.snapshot before.primary.history before.standby.transport with
    | .error reason => throw (.input reason.message)
    | .ok copied =>
      let installed : InstalledCheckpoint :=
        ⟨before.time, checkpoint, before.primary.transport, before.primary.history, before.standby.transport, copied, computed⟩
      let standby := { before.standby with transport := copied.state, history := copied.history }
      return { state := { before with standby, primarySealed := true, installation := some installed }, installation := some installed }
  | .switchRoute actor gateway =>
    if !before.assignmentPaused || !before.primarySealed then throw (.input "Pause and install the checkpoint before changing route ownership.")
    if gateway != .standby then throw (.input "The selected transfer moves endpoint routes to the standby.")
    let some installed := before.installation | throw (.input "The standby has no installed checkpoint.")
    if !before.primary.transport.same installed.checkpoint.snapshot.source ||
        !before.standby.transport.same installed.installed.state then
      throw (.input "The source or target transport state changed before route transfer.")
    return { state := { before with owners := before.owners.set actor.leg gateway, routeEpoch := before.routeEpoch + 1 } }
  | .fencePrimary =>
    if !before.assignmentPaused || !before.primarySealed || before.installation.isNone then
      throw (.input "Pause and install the checkpoint before primary fencing.")
    if before.owners.client != .standby || before.owners.server != .standby then
      throw (.input "Move the two endpoint routes to the standby before primary fencing.")
    if before.outstanding .primary != 0 then throw (.input "Process all primary tickets before primary fencing.")
    return { state := { before with primaryFenced := true } }
  | .resume =>
    if !before.assignmentPaused || !before.primaryFenced then throw (.input "Fence the primary before resuming assignments.")
    if before.owners.client != .standby || before.owners.server != .standby then
      throw (.input "The two endpoint routes must select the standby before assignments resume.")
    let some installed := before.installation | throw (.input "The standby has no installed checkpoint.")
    if !before.primary.transport.same installed.checkpoint.snapshot.source ||
        !before.standby.transport.same installed.installed.state then
      throw (.input "The source or target transport state changed before assignments resume.")
    return { state := { before with assignmentPaused := false } }
  | _ => throw (.input "The event is not a planned transfer control.")

def processCore (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  match event with
  | .authentication index =>
    if index ≠ before.authentication then throw (.input "Consume the next authentication observation exactly once.")
    if available : before.authentication < input.context.authentication.observations.length then
      let source := input.context.authentication.observations[before.authentication]'available
      let finding := Check.EAP.finding source (SessionInstallation.current input.context.authentication (before.authentication + 1))
      return { state := { before with authentication := before.authentication + 1 }, passed := finding.passed }
    else throw (.input "No authentication observation remains.")
  | .install id => installConfiguration input before .primary id
  | .stage id => stageAttachment input before .primary id
  | .installGuard id => installIngress input before .primary id
  | .installAt gateway id => installConfiguration input before gateway id
  | .stageAt gateway id => stageAttachment input before gateway id
  | .installGuardAt gateway id => installIngress input before gateway id
  | .pause | .stageCheckpoint | .installCheckpoint _ | .switchRoute .. | .fencePrimary | .resume =>
    transferControl input before event
  | .open remote policy => startup input before (.activeOpen remote policy)
  | .openRecovering remote policy => openRecovering input before remote policy
  | .startupClock actor millis => runRecovery input before (.advanceClock actor.recoverySide millis)
  | .startupTimeout actor generation policy => runRecovery input before (.timeout actor.recoverySide generation policy)
  | .finishStartup => finishStartup input before
  | .enableStartupRecovery actor => enableStartupRecovery input before actor
  | .write actor bytes => applyApplication input before actor (.write bytes)
  | .send actor count policy => applyApplication input before actor (.send count policy)
  | .enableRecovery actor => applyApplication input before actor .enableRecovery
  | .enableAck actor => enableAck input before actor
  | .dispatchAck actor policy => applyApplication input before actor (.dispatchAck policy)
  | .advanceClock actor millis => applyApplication input before actor (.advanceClock millis)
  | .timeout actor policy => applyApplication input before actor (.timeout policy)
  | .read actor count => applyApplication input before actor (.read count)
  | .emitAck actor policy => applyApplication input before actor (.emitAck policy)
  | .copyPacket _ | .dropPacket _ => return { state := before }
  | .assign index ingress =>
    if before.assignmentPaused then throw (.input "New assignments are paused for the selected transfer.")
    let produced ← get before.outputs index "The endpoint output reference is missing."
    let gateway := before.owner produced.actor
    if !input.configured gateway then throw (.input "The route owner has no declared gateway deployment.")
    if gateway == .primary && (before.primarySealed || before.primaryFenced) then
      throw (.input "The selected primary is sealed or fenced.")
    if gateway == .standby && before.installation.isNone then throw (.input "The standby has no installed TCP checkpoint.")
    let ticket : Ticket input.active input.passive := ⟨index, produced, ingress, gateway, before.routeEpoch⟩
    return { state := { before with work := Work.enqueue before.work ticket } }
  | .serve id observed =>
    let completed ← (Work.complete before.work id).mapError (fun reason => .input reason.describe)
    let gateway := completed.item.value.gateway
    if gateway == .primary && (before.primarySealed || before.primaryFenced) then
      throw (.input "The selected primary cannot process tickets after sealing or fencing.")
    if gateway == .standby && (before.assignmentPaused || before.installation.isNone) then
      throw (.input "Resume the installed standby before packet service.")
    let origin := beforeService input before gateway
    let resident := before.resident gateway
    let mode := before.connection.admissionMode
    match computed : CampusTCPService.run (input.contextFor gateway) origin completed.item.value.source input.zone completed.item.value.ingress 100000 mode with
    | .error (.input reason) => throw (.input reason)
    | .error (.unsupported reason) => return unsupported before (admissionReason reason)
    | .ok evidence =>
      let served : Served input := ⟨before.time, completed.item, origin, mode, evidence, computed,
        observe observed completed.item.value.source evidence.output⟩
      let next := { resident with transport := ⟨evidence.tracker, evidence.admission⟩, history := evidence.history resident.history }
      let after := { before.write gateway next with
        work := completed.state
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
        let receipt : Receipt input := ⟨before.time, index, served, emission, chosen.property, received, same, actor, rfl, none, none⟩
        return { result with state := { result.state with receipts := before.receipts ++ [receipt] }, receipt := some receipt }
      | .application _ _ _ _ =>
        let result ← applyApplication input before actor (.receive received)
        let step := result.application.map (·.2)
        let receipt : Receipt input := ⟨before.time, index, served, emission, chosen.property, received, same, actor, rfl, step, none⟩
        return { result with state := { result.state with receipts := before.receipts ++ [receipt] }, receipt := some receipt }
      | .recovery _ occurrence _ =>
        let result ← runRecovery input before (.receive occurrence.index bytes .rewrite policy)
        let step := result.application.map (·.2)
        let control := result.recovery.bind (fun actual => actual.result.receipt)
        let receipt : Receipt input := ⟨before.time, index, served, emission, chosen.property, received, same, actor, rfl, step, control⟩
        return { result with state := { result.state with receipts := before.receipts ++ [receipt] }, receipt := some receipt }
    else throw (.input "Receiver bytes must equal the selected actual gateway emission.")

def prepareCustody (before : State input) (event : Event) : Except Error (Custody input) := do
  match event with
  | .assign index _ =>
    let some id := before.custody.pendingID (Transit.ingressAt index)
      | throw (.input "No pending ingress packet remains for this endpoint output.")
    let result ← (Theory.PacketCustody.resolve before.custody id .assigned).mapError (fun reason => .input reason.describe)
    return result.state
  | .deliver index bytes _ =>
    let some id := before.custody.pendingID (Transit.linkAt index)
      | throw (.input "No pending receiver-link packet remains for this gateway service.")
    let result ← (Theory.PacketCustody.resolve before.custody id .delivered).mapError (fun reason => .input reason.describe)
    if bytes = result.item.value.payload.bytes then return result.state
    else throw (.input "Receiver bytes must equal the selected actual gateway emission.")
  | .copyPacket id =>
    let result ← (Theory.PacketCustody.copy before.custody id).mapError (fun reason => .input reason.describe)
    if before.recoveryArchive.isSome && result.source.value.payload.isRecovery then
      throw (.input "A closed recovery startup packet cannot be copied again.")
    return result.state
  | .dropPacket id =>
    let result ← (Theory.PacketCustody.resolve before.custody id .dropped).mapError (fun reason => .input reason.describe)
    return result.state
  | _ => return before.custody

def finishCustody (before : State input) (effect : Effect input) (custody : Custody input) : Custody input :=
  let after := match effect.output with
    | none => custody
    | some produced => Theory.PacketCustody.mint custody (.ingress before.outputs.length produced)
  match effect.service with
  | none => after
  | some served => match emitted : served.evidence.output with
    | none => after
    | some emission => Theory.PacketCustody.mint after (.link before.services.length served emission emitted)

def process (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  let result ← processCore input before event
  let custody ← prepareCustody before event
  return { result with state := { result.state with custody := finishCustody before result custody } }

def step (input : Input) (before : State input) (event : Event) : Except Error (Effect input) := do
  let result ← process input before event
  return { result with state := { result.state with time := before.time + 1 } }

structure Step (input : Input) where
  before : State input
  event : Event
  result : Effect input
  computed : step input before event = .ok result

theorem Step.transaction (value : Step input) :
    ∃ effect custody, processCore input value.before value.event = .ok effect ∧
      prepareCustody value.before value.event = .ok custody ∧
      value.result = { effect with state := { effect.state with
        custody := finishCustody value.before effect custody, time := value.before.time + 1 } } := by
  have accepted := value.computed
  unfold step process at accepted
  cases observed : processCore input value.before value.event with
  | error reason => simp [observed, bind, Except.bind] at accepted
  | ok result =>
    simp only [observed, bind, Except.bind] at accepted
    cases prepared : prepareCustody value.before value.event with
    | error reason => simp [prepared] at accepted
    | ok custody =>
      simp only [prepared, pure, Except.pure, Except.ok.injEq] at accepted
      exact ⟨result, custody, rfl, rfl, accepted.symm⟩

theorem Step.processed (value : Step input) :
    ∃ effect custody, processCore input value.before value.event = .ok effect ∧
      value.result = { effect with state := { effect.state with custody, time := value.before.time + 1 } } := by
  obtain ⟨effect, custody, computed, _, result⟩ := value.transaction
  exact ⟨effect, finishCustody value.before effect custody, computed, result⟩

theorem Step.clock (value : Step input) : value.result.state.time = value.before.time + 1 := by
  obtain ⟨effect, custody, _, result⟩ := value.processed
  rw [result]

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
