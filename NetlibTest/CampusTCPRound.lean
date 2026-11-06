import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPRoundSetup
import Netlib.Check.CampusTCPRoundServiceBound
import NetlibTest.CampusTCPRoundBounded

namespace NetlibTest.CampusTCPRound

open Netlib Packet Protocol

namespace M
export Check.CampusTCPModel (Input Event Report State Step Applications)
end M
namespace R
export Check.CampusTCPRoundSetup (applications_initial prepare setupEvents)
end R
namespace S
export Check.CampusTCPSchedule (Report.appendStep Report.appendStep_supported)
end S
namespace O
export Check.CampusTCPRoundMonitor (Config Monitor Monitor.initial observe)
end O
namespace B
export Check.CampusTCPRoundServiceBound (actions actions_correct check check_correct Serviced)
end B

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private structure Checked (input : M.Input) (origin : M.State input) where
  events : List M.Event
  report : M.Report input events
  supported : report.supported = true
  finished : report.remaining = []
  recorded : List (M.Step input)
  suffix : Check.CampusTCPModel.Trace input origin (recorded.map (·.event)) recorded report.final []
  accepted : ∀ actual ∈ recorded, actual.result.supported = true

variable {input : M.Input} {origin : M.State input}

private def initial (input : M.Input) : Checked input input.initial :=
  ⟨[], ⟨input.initial, [], [], .done input.initial⟩, rfl, rfl, [], .done input.initial, by simp⟩

private def checkpoint (prior : Checked input origin) : Checked input prior.report.final :=
  ⟨prior.events, prior.report, prior.supported, prior.finished, [], .done prior.report.final, by simp⟩

private structure Appended (prior : Checked input origin) (event : M.Event) where
  next : Checked input origin
  actual : M.Step input
  beforeEq : actual.before = prior.report.final
  eventEq : actual.event = event
  supported : actual.result.supported = true
  finalEq : next.report.final = actual.result.state
  recordedEq : next.recorded = prior.recorded ++ [actual]

private def appendOne (prior : Checked input origin) (event : M.Event) : IO (Appended prior event) := do
  match computed : Check.CampusTCPModel.step input prior.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    ensure effect.passed "The generated operation must pass its actual policy checks."
    if supported : effect.supported = true then
      let actual : M.Step input := ⟨prior.report.final, event, effect, computed⟩
      let report := S.Report.appendStep prior.report prior.supported prior.finished actual rfl supported
      let next : Checked input origin := {
        events := prior.events ++ [event], report
        supported := S.Report.appendStep_supported _ _ _ _ _ _
        finished := rfl
        recorded := prior.recorded ++ [actual]
        suffix := by
          rw [List.map_append]
          exact Check.CampusTCPSchedule.Trace.append_complete prior.suffix rfl prior.accepted
            (.next actual supported (.done actual.result.state))
        accepted := by
          intro selected member
          rcases List.mem_append.mp member with old | current
          · exact prior.accepted selected old
          · have same := List.mem_singleton.mp current
            subst selected
            exact supported }
      return ⟨next, actual, rfl, rfl, supported, rfl, rfl⟩
    else throw (IO.userError "The generated operation requires an unsupported step.")

private def append (prior : Checked input origin) (event : M.Event) : IO (Checked input origin) := do
  return (← appendOne prior event).next

private structure SetupRun (prior : Checked input origin) (bytes : List UInt8) where
  next : Checked input prior.report.final
  trace : Check.CampusTCPModel.Trace input prior.report.final (R.setupEvents bytes) next.recorded next.report.final []

private def setup (prior : Checked input origin) (bytes : List UInt8) : IO (SetupRun prior bytes) := do
  let base := checkpoint prior
  let a ← appendOne base (.enableRecovery .client)
  let b ← appendOne a.next (.enableRecovery .server)
  let c ← appendOne b.next (.enableAck .client)
  let d ← appendOne c.next (.enableAck .server)
  let e ← appendOne d.next (.write .client bytes)
  have events : e.next.recorded.map (·.event) = R.setupEvents bytes := by
    rw [e.recordedEq, d.recordedEq, c.recordedEq, b.recordedEq, a.recordedEq]
    simp only [base, checkpoint, List.nil_append, List.map_cons, List.map_nil,
      a.eventEq, b.eventEq, c.eventEq, d.eventEq, e.eventEq, List.cons_append,
      R.setupEvents]
  return ⟨e.next, events ▸ e.next.suffix⟩

private def startup (events : List M.Event) (prior : Checked input origin) : IO (Checked input origin) := do
  match prior.report.final.connection with
  | .application .. => return prior
  | .startup .. =>
    match events with
    | [] => throw (IO.userError "The startup input ended before the final ACK receipt.")
    | event :: rest => startup rest (← append prior event)

private def endpoint (state : M.State input) (actor : Check.CampusTCPModel.Actor) :
    Except String TCP.Endpoint.State :=
  match state.connection with
  | .startup .. => throw "The generated round has no completed startup."
  | .application _ endpoints => .ok (Check.CampusTCPEnabled.endpoint endpoints actor)

private def stall (prior : Checked input origin) (phase count : Nat) : IO (Checked input origin) := do
  let mut current := prior
  for index in List.range count do
    let client ← load (endpoint current.report.final .client)
    let server ← load (endpoint current.report.final .server)
    let actor := if (phase + index) % 2 == 0 then Check.CampusTCPModel.Actor.client else .server
    let selected ← load (endpoint current.report.final actor)
    let next ← append current (.advanceClock actor selected.now)
    let nextClient ← load (endpoint next.report.final .client)
    let nextServer ← load (endpoint next.report.final .server)
    ensure (client == nextClient && server == nextServer &&
        current.report.final.outputs.length == next.report.final.outputs.length &&
        current.report.final.services.length == next.report.final.services.length &&
        current.report.final.receipts.length == next.report.final.receipts.length &&
        current.report.final.work.pending.map (·.id) == next.report.final.work.pending.map (·.id) &&
        current.report.final.custody.pending.map (·.id) == next.report.final.custody.pending.map (·.id) &&
        current.report.final.custody.nextID == next.report.final.custody.nextID)
      "A same-clock wait must retain both endpoints and all live packet work."
    current := next
  return current

private def ingress (state : M.State input) (actor : Check.CampusTCPModel.Actor) :
    Except String IngressAttachment.InterfaceRef := do
  let deployment := input.deployment (state.owner actor)
  let some specification := deployment.specifications.find? (fun value => value.direction == actor.direction)
    | throw "The actual gateway has no ingress for the selected direction."
  return specification.ingress

private def last (value : Checked input origin) : Except String (M.Step input) := do
  let some actual := value.report.steps.getLast?
    | throw "The actual checked history has no operation."
  return actual

private def assign (prior : Checked input origin) (output : Nat) (actor : Check.CampusTCPModel.Actor) :
    IO (Checked input origin × Nat) := do
  let current ← append prior (.assign output (← load (ingress prior.report.final actor)))
  let some ticket := current.report.final.work.pending.getLast?
    | throw (IO.userError "Assignment must retain the actual new ticket.")
  ensure (ticket.value.outputIndex == output && ticket.value.produced.actor == actor)
    "The new ticket must select the generated endpoint output."
  return (current, ticket.id)

private def serve (prior : Checked input origin) (id : Nat) : IO (Checked input origin × Nat × List UInt8) := do
  let index := prior.report.final.services.length
  let current ← append prior (.serve id none)
  let some served := current.report.final.services[index]?
    | throw (IO.userError "The generated ticket must produce a stored gateway service.")
  let some emission := served.evidence.output
    | throw (IO.userError "The current gateway must emit the selected range.")
  ensure (served.ticket.id == id && current.report.final.services.length == index + 1)
    "Service must consume the selected immutable ticket."
  return (current, index, emission.bytes)

private def noReplay (current : Checked input origin) (index : Nat) (bytes : List UInt8) : IO Unit := do
  match Check.CampusTCPModel.step input current.report.final (.deliver index bytes true) with
  | .error reason =>
    ensure (reason.message == "No pending receiver-link packet remains for this gateway service.")
      "An old delivery must fail at its consumed packet identity."
  | .ok _ => throw (IO.userError "A consumed link packet must not enter a second delivery slot.")

private def checkSetup (current : Checked input origin) (bytes : List UInt8) : IO Unit := do
  match connection : current.report.final.connection with
  | .startup .. => throw (IO.userError "The selected initial prefix must complete TCP startup.")
  | .application complete endpoints =>
    let client ← load (verify (endpoints.client.steps = []) "The first application cut already has client operations.")
    let server ← load (verify (endpoints.server.steps = []) "The first application cut already has server operations.")
    let fits ← load (verify (bytes.length ≤ input.active.pendingLimit) "The selected write exceeds the initial pending limit.")
    have initialConnection : current.report.final.connection =
        .application complete (Check.CampusTCPModel.Applications.initial complete) := by
      rw [connection, R.applications_initial endpoints client.property server.property]
    let _ := R.prepare current.report current.supported current.finished complete initialConnection bytes fits.property
    pure ()

private def omission (config : O.Config) (preparedAt : Nat) (phase : Nat) (prior : Checked input origin) : IO Unit := do
  let monitor := (prior.report.steps.drop preparedAt).foldl (O.observe config) O.Monitor.initial
  let ending ← stall prior phase 2
  let slots := ending.report.steps.drop prior.report.steps.length
  let allowed ← load (verify (B.actions config prior.report.final monitor slots = true)
    "The omitted-service schedule must contain allowed clock slots.")
  let _ := B.actions_correct config prior.report.final monitor slots |>.mp allowed.property
  let denied ← load (verify (B.check config prior.report.final monitor slots 2 = false)
    "Each omitted phase must fail its service bound.")
  have _missing : ¬B.Serviced config prior.report.final monitor slots 2 := by
    intro serviced
    have accepted := (B.check_correct config prior.report.final monitor slots 2).mpr serviced
    rw [denied.property] at accepted
    contradiction
  pure ()

private def historicalWork (prior : Checked input origin) : IO (Checked input origin) := do
  let copied ← append prior (.copyPacket 0)
  let assigned ← append copied (.assign 0 (← load (ingress copied.report.final .client)))
  let pending ← append assigned (.copyPacket 0)
  ensure (pending.report.final.work.pending.length == 1 && pending.report.final.custody.pending.length == 1 &&
      pending.report.final.custody.pending.all (fun item => item.value.parent == some 0))
    "The scope case must retain one old startup ticket and one old ingress copy."
  return pending

private def round (input : M.Input) (events : List M.Event) (bytes : List UInt8)
    (waits : List Nat) (windowExpected : Bool) (keepHistorical : Bool := false) : IO Unit := do
  let startupPrefix ← startup events (initial input)
  ensure (startupPrefix.report.steps.length == 25) "The round must use only the actual startup prefix."
  checkSetup startupPrefix bytes
  let start ← if keepHistorical then historicalWork startupPrefix else pure startupPrefix
  let prepared ← setup start bytes
  let mut current := checkpoint prepared.next
  let preparedAt := prepared.next.report.steps.length
  let preparedState := prepared.next.report.final
  let config : O.Config := ⟨bytes, ← load (ingress preparedState .client), ← load (ingress preparedState .server)⟩
  let selected := current.report.final.outputs.length
  current ← stall current 0 (waits[0]?.getD 0)
  unless keepHistorical do omission config preparedAt 0 current
  current ← append current (.send .client bytes.length true)
  let some data := current.report.final.outputs[selected]?
    | throw (IO.userError "The generated send must retain its output.")
  ensure (data.output.packet.segment.payload == bytes) "The original output must contain the new application write."
  current ← stall current 1 (waits[1]?.getD 0)
  unless keepHistorical do omission config preparedAt 1 current
  let assigned ← assign current selected .client
  current := assigned.1
  current ← stall current 2 (waits[2]?.getD 0)
  unless keepHistorical do omission config preparedAt 2 current
  let dataService ← serve current assigned.2
  current := dataService.1
  current ← stall current 3 (waits[3]?.getD 0)
  unless keepHistorical do omission config preparedAt 3 current
  current ← append current (.deliver dataService.2.1 dataService.2.2 true)
  let receiver ← load (endpoint current.report.final .server)
  ensure (receiver.core.received == bytes && receiver.receiveStore.held.isEmpty)
    "One actual receipt must release the selected range in order."
  noReplay current dataService.2.1 dataService.2.2
  current ← stall current 4 (waits[4]?.getD 0)
  unless keepHistorical do omission config preparedAt 4 current
  let ackIndex := current.report.final.outputs.length
  current ← append current (.emitAck .server true)
  let some ack := current.report.final.outputs[ackIndex]?
    | throw (IO.userError "The actual release must permit a covering ACK output.")
  ensure (ack.output.packet.segment.payload.isEmpty &&
      ack.output.packet.segment.acknowledgment == receiver.core.receiveNext)
    "The reverse ACK must cover the released cursor."
  current ← stall current 5 (waits[5]?.getD 0)
  unless keepHistorical do omission config preparedAt 5 current
  let assignedAck ← assign current ackIndex .server
  current := assignedAck.1
  current ← stall current 6 (waits[6]?.getD 0)
  unless keepHistorical do omission config preparedAt 6 current
  let ackService ← serve current assignedAck.2
  current := ackService.1
  current ← stall current 7 (waits[7]?.getD 0)
  unless keepHistorical do omission config preparedAt 7 current
  current ← append current (.deliver ackService.2.1 ackService.2.2 true)
  let sender ← load (endpoint current.report.final .client)
  let some recovery := sender.recovery
    | throw (IO.userError "The real sender recovery state must remain enabled.")
  ensure (sender.core.sent.isEmpty && sender.core.sendUna == sender.core.sendNext &&
      recovery.outstanding.isEmpty && recovery.deadline.isNone && recovery.timeoutCount == 0)
    "The covering ACK must retire the actual sent range and its timer ledger."
  noReplay current ackService.2.1 ackService.2.2
  current ← stall current 8 (waits[8]?.getD 0)
  unless keepHistorical do omission config preparedAt 8 current
  current ← append current (.read .server bytes.length)
  let actual ← load (last current)
  ensure (actual.result.read == bytes) "The application must read the exact original write."
  let receiver ← load (endpoint current.report.final .server)
  let some reaction := receiver.ackReaction
    | throw (IO.userError "The receiver ACK state must remain enabled after the read.")
  ensure (receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty &&
      reaction.work.pending.any (fun cause => cause.demand.kind == .window) == windowExpected)
    "Completion can retain the actual ACK work created by a window increase."
  let slots := current.report.steps.length - preparedAt
  let bound := 1 + waits.foldl max 0
  let beforePadding := slots
  current ← stall current 9 (9 * bound - beforePadding)
  let suffix := current.recorded
  let allowed ← load (verify (B.actions config preparedState O.Monitor.initial suffix = true)
    "The actual round must use only its selected actions and clock slots.")
  let _ := (B.actions_correct config preparedState O.Monitor.initial suffix).mp allowed.property
  let serviced ← load (verify (B.check config preparedState O.Monitor.initial suffix bound = true)
    "Each actual round demand must have service within its bound.")
  let _ := (B.check_correct config preparedState O.Monitor.initial suffix bound).mp serviced.property
  ensure ((suffix.foldl (O.observe config) O.Monitor.initial).phase == .done)
    "The actual read must complete the stored-step monitor."
  let enough ← load (verify (9 * bound ≤ suffix.length) "The bounded test needs enough evaluated slots.")
  NetlibTest.CampusTCPRoundBounded.check start.report start.supported start.finished config
    prepared.next.report prepared.next.recorded prepared.trace current.recorded current.suffix bound
    allowed.property serviced.property enough.property
  ensure (slots == 9 + (waits.take 9).foldl (· + ·) 0 && suffix.length == 9 * bound && slots ≤ 9 * bound &&
      current.report.final.custody.count .dropped == preparedState.custody.count .dropped &&
      current.report.final.custody.pending.map (·.id) == preparedState.custody.pending.map (·.id) &&
      current.report.final.work.pending.map (·.id) == preparedState.work.pending.map (·.id) &&
      current.report.final.custody.count .assigned == preparedState.custody.count .assigned + 2 &&
      current.report.final.custody.count .delivered == preparedState.custody.count .delivered + 2 &&
      suffix.all (fun actual => match actual.event with | .copyPacket .. | .dropPacket .. => false | _ => true))
    "The selected round must retain prior work and resolve only its own packets."

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json"))
  round input.model input.events [37] (List.replicate 9 0) false
  round input.model input.events (List.range 400 |>.map (UInt8.ofNat ·)) [1, 2, 3, 1, 2, 3, 1, 2, 3] false
  let smallerOutput := { input.model with passive := { input.model.passive with ipSendLimit := 840 } }
  round smallerOutput input.events (List.range 800 |>.map (UInt8.ofNat ·)) [3, 1, 2, 3, 1, 2, 3, 1, 2] true
  round input.model input.events [91] (List.replicate 9 0) false true
  IO.println "Campus generated TCP round tests passed."

end NetlibTest.CampusTCPRound
