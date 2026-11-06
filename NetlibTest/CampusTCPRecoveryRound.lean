import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPRecoveryRoundServiceBound
import Netlib.Check.CampusTCPRecoveryRoundBounded
import Netlib.Check.CampusTCPRoundReport
import NetlibTest.CampusTCPRoundTheorem

namespace NetlibTest.CampusTCPRecoveryRound

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
export Check.CampusTCPRecoveryRoundMonitor (Config Monitor Monitor.initial Demand observe nextDemand allowed)
end O
namespace B
export Check.CampusTCPRecoveryRoundServiceBound (actions actions_correct check check_correct Serviced)
end B
namespace T
export NetlibTest.CampusTCPRoundTheorem (verify ordinary cleanServices native setup_environment)
end T

def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

structure Checked (input : M.Input) (origin : M.State input) where
  events : List M.Event
  report : M.Report input events
  supported : report.supported = true
  finished : report.remaining = []
  recorded : List (M.Step input)
  suffix : Check.CampusTCPModel.Trace input origin (recorded.map (·.event)) recorded report.final []
  accepted : ∀ actual ∈ recorded, actual.result.supported = true

variable {input : M.Input} {origin : M.State input}

def initial (input : M.Input) : Checked input input.initial :=
  ⟨[], ⟨input.initial, [], [], .done input.initial⟩, rfl, rfl, [], .done input.initial, by simp⟩

def checkpoint (prior : Checked input origin) : Checked input prior.report.final :=
  ⟨prior.events, prior.report, prior.supported, prior.finished, [], .done prior.report.final, by simp⟩

structure Appended (prior : Checked input origin) (event : M.Event) where
  next : Checked input origin
  actual : M.Step input
  beforeEq : actual.before = prior.report.final
  eventEq : actual.event = event
  supported : actual.result.supported = true
  finalEq : next.report.final = actual.result.state
  recordedEq : next.recorded = prior.recorded ++ [actual]

def appendOne (prior : Checked input origin) (event : M.Event) : IO (Appended prior event) := do
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

def append (prior : Checked input origin) (event : M.Event) : IO (Checked input origin) := do
  return (← appendOne prior event).next

structure SetupRun (prior : Checked input origin) (bytes : List UInt8) where
  next : Checked input prior.report.final
  trace : Check.CampusTCPModel.Trace input prior.report.final (R.setupEvents bytes) next.recorded next.report.final []

def setup (prior : Checked input origin) (bytes : List UInt8) : IO (SetupRun prior bytes) := do
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

def startup (events : List M.Event) (prior : Checked input origin) : IO (Checked input origin) := do
  match prior.report.final.connection with
  | .application .. => return prior
  | .startup .. =>
    match events with
    | [] => throw (IO.userError "The startup input ended before the final ACK receipt.")
    | event :: rest =>
      let actualEvent ← match event with
        | .serve id _ => pure (.serve id none)
        | .deliver index _ policy => do
          let some served := prior.report.final.services[index]?
            | throw (IO.userError "The startup delivery has no actual service.")
          let some emission := served.evidence.output
            | throw (IO.userError "The startup service has no actual emission.")
          pure (.deliver index emission.bytes policy)
        | other => pure other
      startup rest (← append prior actualEvent)

def endpoint (state : M.State input) (actor : Check.CampusTCPModel.Actor) :
    Except String TCP.Endpoint.State :=
  match state.connection with
  | .startup .. => throw "The generated round has no completed startup."
  | .application _ endpoints => .ok (Check.CampusTCPEnabled.endpoint endpoints actor)


private def ingress (state : M.State input) (actor : Check.CampusTCPModel.Actor) :
    Except String IngressAttachment.InterfaceRef := do
  let deployment := input.deployment (state.owner actor)
  let some specification := deployment.specifications.find? (fun value => value.direction == actor.direction)
    | throw "The actual gateway has no ingress for the selected direction."
  return specification.ingress

def InitialWitness (startup : M.Report input startupEvents) (prepared : M.Report input preparedEvents)
    (config : O.Config) : Prop :=
  ∃ (complete : Check.TCPHandshake.Completed input.active input.passive)
    (request : Check.CampusTCPRoundStart.Request input)
    (initial : Check.CampusTCPRoundStart.Initial startup complete request)
    (native : Check.CampusTCPRoundStart.NativeEnv initial),
    request.bytes = config.bytes ∧ Check.CampusTCPRoundPhaseBase.config initial native = config.toConfig ∧
      initial.state = prepared.final

private theorem bounded_actual_read (startup : M.Report input startupEvents) (prepared : M.Report input preparedEvents)
    (config : O.Config) (witness : InitialWitness startup prepared config) (steps : List (M.Step input))
    (final : M.State input) (trace : Check.CampusTCPModel.Trace input prepared.final (steps.map (·.event)) steps final [])
    (quantum : config.quantum = 10)
    (allowed : B.actions config prepared.final O.Monitor.initial steps = true)
    (service : B.check config prepared.final O.Monitor.initial steps 2 = true) (enough : 650 ≤ steps.length) :
    ∃ actual ∈ steps.take 650, actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
  obtain ⟨complete, request, initial, native, bytes, sameConfig, stateEq⟩ := witness
  have configEq : Check.CampusTCPRecoveryRoundPhaseBase.config initial native 10 = config := by
    cases config with
    | mk base clock =>
      change Check.CampusTCPRoundPhaseBase.config initial native = base at sameConfig
      change clock = 10 at quantum
      cases sameConfig
      cases quantum
      rfl
  have actualTrace : Check.CampusTCPModel.Trace input initial.state (steps.map (·.event)) steps final [] := by
    rw [stateEq]
    exact trace
  have actualRead := Check.CampusTCPRecoveryRoundBounded.read_by_checked
    (initial := initial) (native := native) (quantum := 10) (bound := 2) (by decide) actualTrace
    (by rw [configEq, stateEq]; exact allowed) (by rw [configEq, stateEq]; exact service)
    (by simpa only [Check.CampusTCPRecoveryRoundBounded.boundSlots_ten_two] using enough)
  simpa only [Check.CampusTCPRecoveryRoundBounded.boundSlots_ten_two, bytes] using actualRead

private def initialWitness (startup : M.Report input startupEvents) (supported : startup.supported = true)
    (finished : startup.remaining = []) (config : O.Config) (prepared : M.Report input preparedEvents)
    (setupSteps : List (M.Step input))
    (setupTrace : Check.CampusTCPModel.Trace input startup.final (R.setupEvents config.bytes)
      setupSteps prepared.final []) : IO { _value : Unit // InitialWitness startup prepared config } := do
  match connection : startup.final.connection with
  | .startup .. => throw (IO.userError "The bounded initial prefix must complete startup.")
  | .application complete endpoints =>
    let clientEmpty ← load (T.verify (endpoints.client.steps = []) "The bounded initial client has prior operations.")
    let serverEmpty ← load (T.verify (endpoints.server.steps = []) "The bounded initial server has prior operations.")
    have initialConnection : startup.final.connection =
        .application complete (Check.CampusTCPModel.Applications.initial complete) := by
      rw [connection, Check.CampusTCPRoundSetup.applications_initial endpoints clientEmpty.property serverEmpty.property]
    let ordinary ← load (T.ordinary startup)
    let clean ← load (T.cleanServices startup complete ordinary)
    let nonempty ← load (T.verify (config.toConfig.bytes ≠ []) "The bounded request must contain bytes.")
    let pending ← load (T.verify (config.toConfig.bytes.length ≤ input.active.pendingLimit) "The bounded request exceeds pending storage.")
    let mss ← load (T.verify (config.toConfig.bytes.length ≤ TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive))
      "The bounded request exceeds learned MSS.")
    let window ← load (T.verify (config.toConfig.bytes.length ≤ input.passive.capacity) "The bounded request exceeds the peer window.")
    let request : Check.CampusTCPRoundStart.Request input :=
      ⟨config.toConfig.bytes, nonempty.property, pending.property, mss.property, window.property⟩
    let before := Check.CampusTCPModel.beforeService input startup.final .primary
    match records : before.tracker.records with
    | [⟨entry, true⟩] =>
      let original ← load (T.native (input.contextFor .primary) before config.toConfig.clientIngress entry .original "server")
      let reply ← load (T.native (input.contextFor .primary) before config.toConfig.serverIngress entry .reply "client")
      let client ← load (T.verify (startup.final.owner .client = .primary) "The bounded client route must use primary.")
      let server ← load (T.verify (startup.final.owner .server = .primary) "The bounded server route must use primary.")
      let unpaused ← load (T.verify (startup.final.assignmentPaused = false) "The bounded initial gateway is paused.")
      let unsealed ← load (T.verify (startup.final.primarySealed = false) "The bounded initial gateway is sealed.")
      let unfenced ← load (T.verify (startup.final.primaryFenced = false) "The bounded initial gateway is fenced.")
      return ⟨(), by
        obtain ⟨initial⟩ := Check.CampusTCPRoundStart.Initial.prepareOrdinary ordinary initialConnection
          (clean.property (Check.CampusTCPRoundStart.historyOfOrdinary ordinary complete initialConnection))
          supported finished request
        have current : initial.beforeService = before := Check.CampusTCPRoundLocal.setup_service initial.start .primary
        have selected := initial.records
        change initial.beforeService.tracker.records = [⟨initial.entry, true⟩] at selected
        rw [current, records] at selected
        have entryEq : initial.entry = entry :=
          (congrArg ConntrackLifecycle.Record.entry (List.cons.inj selected).1).symm
        have fixed := T.setup_environment initial.start
        have owners := congrArg Check.CampusTCPRoundEnvironment.Environment.owners fixed
        have paused := congrArg Check.CampusTCPRoundEnvironment.Environment.assignmentPaused fixed
        have sealed := congrArg Check.CampusTCPRoundEnvironment.Environment.primarySealed fixed
        have fenced := congrArg Check.CampusTCPRoundEnvironment.Environment.primaryFenced fixed
        change startup.final.owners = initial.state.owners at owners
        let env : Check.CampusTCPRoundStart.NativeEnv initial := {
          dataIngress := config.toConfig.clientIngress, ackIngress := config.toConfig.serverIngress
          original := by rw [current, entryEq]; exact original
          reply := by rw [current, entryEq]; exact reply
          clientOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using client.property
          serverOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using server.property
          unpaused := paused.symm.trans unpaused.property
          unsealed := sealed.symm.trans unsealed.property
          unfenced := fenced.symm.trans unfenced.property
          configured := rfl }
        have sameConfig : Check.CampusTCPRoundPhaseBase.config initial env = config.toConfig := by cases config; rfl
        have stateEq : initial.state = prepared.final :=
          Check.CampusTCPRoundReport.Trace.final_unique initial.start.suffix setupTrace
        exact ⟨complete, request, initial, env, rfl, sameConfig, stateEq⟩⟩
    | _ => throw (IO.userError "The initial prefix must retain one confirmed binding that has seen a reply.")

inductive LossPoint where
  | dataIngress | dataLink | ackIngress | ackLink
  deriving Repr, BEq, DecidableEq

def lossPoint : Check.CampusTCPRoundMonitor.Phase → Option LossPoint
  | .dataIngress => some .dataIngress
  | .dataLink => some .dataLink
  | .ackIngress => some .ackIngress
  | .ackLink => some .ackLink
  | _ => none

def lossWords : List (List LossPoint) :=
  let points := [LossPoint.dataIngress, .dataLink, .ackIngress, .ackLink]
  [[]] ++ points.map (fun point => [point]) ++ points.flatMap (fun first => points.map (fun second => [first, second]))

private def selectedTag (demand : O.Demand) (monitor : O.Monitor) : Nat :=
  match demand with
  | .tick _ => 11
  | .timeout => 12
  | _ => monitor.round.rank

private def omission (config : O.Config) (monitor : O.Monitor) (prior : Checked input origin) : IO Unit := do
  let server ← load (endpoint prior.report.final .server)
  let base := checkpoint prior
  let first ← append base (.advanceClock .server server.now)
  let second ← append first (.advanceClock .server server.now)
  let allowed ← load (verify (B.actions config base.report.final monitor second.recorded = true)
    "The omitted-service branch must contain allowed clock slots.")
  let _ := (B.actions_correct config base.report.final monitor second.recorded).mp allowed.property
  let denied ← load (verify (B.check config base.report.final monitor second.recorded 2 = false)
    "Two clock slots must fail the omitted demand's service bound.")
  have _missing : ¬B.Serviced config base.report.final monitor second.recorded 2 := by
    intro serviced
    have accepted := (B.check_correct config base.report.final monitor second.recorded 2).mpr serviced
    rw [denied.property] at accepted
    contradiction
  pure ()

private def historicalWork (prior : Checked input origin) : IO (Checked input origin) := do
  let copied ← append prior (.copyPacket 0)
  let some old := copied.report.final.custody.pending.getLast?
    | throw (IO.userError "The old copy must have a custody identity.")
  let dropped ← append copied (.dropPacket old.id)
  let first ← append dropped (.copyPacket 0)
  let assigned ← append first (.assign 0 (← load (ingress first.report.final .client)))
  let pending ← append assigned (.copyPacket 0)
  ensure (pending.report.final.work.pending.length == 1 && pending.report.final.custody.pending.length == 1 &&
      pending.report.final.custody.count .dropped == prior.report.final.custody.count .dropped + 1)
    "The scope case must retain old work and an old drop before the selected suffix."
  return pending

private def dropIDs (steps : List (M.Step input)) : List Nat := steps.filterMap fun actual =>
  match actual.event with | .dropPacket id => some id | _ => none

private def countAssigned (steps : List (M.Step input)) : Nat := (steps.filter fun actual =>
  match actual.event with | .assign .. => true | _ => false).length

private def countDelivered (steps : List (M.Step input)) : Nat := (steps.filter fun actual =>
  match actual.event with | .deliver .. => true | _ => false).length

private def positiveClock (actor : Check.CampusTCPModel.Actor) (actual : M.Step input) : Bool :=
  match actual.event, endpoint actual.before actor, endpoint actual.result.state actor with
  | .advanceClock selected millis, .ok before, .ok after =>
    selected == actor && actual.result.supported && actual.result.passed && before.now < after.now && after.now == millis
  | _, _, _ => false

private def noDropReplay (current : Checked input origin) (id : Nat) : IO Unit := do
  match Check.CampusTCPModel.step input current.report.final (.dropPacket id) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "The same custody identity must not be dropped twice.")

private def checkRetry (before after : M.State input) (actual : M.Step input) (bytes : List UInt8)
    (attempt : Nat) : IO Unit := do
  let old ← load (endpoint before .client)
  let next ← load (endpoint after .client)
  let some prior := old.recovery | throw (IO.userError "A retry needs its actual old recovery ledger.")
  let some recovery := next.recovery | throw (IO.userError "A retry must retain the recovery ledger.")
  let some produced := actual.result.output | throw (IO.userError "The actual timeout must emit its retry.")
  let some operation := actual.result.application | throw (IO.userError "The timeout must retain its endpoint operation.")
  let entries := prior.outstanding.map (fun entry => { entry with lastAt := prior.now, retried := true })
  ensure ((match operation.2.event with | .timeout true => true | _ => false) &&
      operation.2.result.decision == .accepted (.retry bytes.length) &&
      produced.output.packet.segment.sequence == old.core.sendUna &&
      produced.output.packet.segment.payload == bytes && old.core.sent == bytes &&
      next.core == old.core && next.pending == old.pending && next.receiveStore == old.receiveStore &&
      recovery.outstanding == entries && recovery.now == prior.now && recovery.rto == 2 * prior.rto &&
      recovery.deadline == some (prior.now + 2 * prior.rto) &&
      recovery.timeoutCount == attempt && recovery.nextId == prior.nextId && recovery.frontier == prior.frontier &&
      recovery.estimator == prior.estimator && recovery.lastSample == prior.lastSample &&
      TCP.Recovery.sample recovery bytes.length == none)
    "A timeout must retry the same bytes and ledger identity with real backoff and Karn suppression."

private def rejectedOperation (prior : Checked input origin) (event : M.Event)
    (actor : Check.CampusTCPModel.Actor) (decision : TCP.Endpoint.Decision) (supported : Bool) : IO Unit := do
  let old ← load (endpoint prior.report.final actor)
  match Check.CampusTCPModel.step input prior.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    let some operation := effect.application
      | throw (IO.userError "The negative endpoint operation must retain its actual local result.")
    let next ← load (endpoint effect.state actor)
    ensure (operation.2.result.decision == decision && effect.supported == supported &&
        effect.output.isNone && next == old)
      "The negative operation must fail its exact guard without output or endpoint mutation."

private def exhaustedTimeout (prior : Checked input origin) : IO Unit := do
  let client ← load (endpoint prior.report.final .client)
  let some recovery := client.recovery | throw (IO.userError "The third timeout test needs enabled recovery.")
  let some deadline := recovery.deadline | throw (IO.userError "The third timeout test needs the stored timer.")
  let due ← append prior (.advanceClock .client deadline)
  rejectedOperation due (.timeout .client true) .client (.recoveryUnsupported .failureHandling) false

private def overdueAck (prior : Checked input origin) : IO Unit := do
  let server ← load (endpoint prior.report.final .server)
  let some reaction := server.ackReaction | throw (IO.userError "The deadline test needs actual ACK work.")
  let some deadline := reaction.due | throw (IO.userError "The actual ACK cause must retain its deadline.")
  rejectedOperation prior (.advanceClock .server (deadline + 1)) .server (.ackUnsupported .deadline) false

private def checkComplete (prepared final : M.State input) (steps : List (M.Step input))
    (monitor : O.Monitor) (bytes : List UInt8) (losses : Nat) : IO Unit := do
  let sender ← load (endpoint final .client)
  let receiver ← load (endpoint final .server)
  let some recovery := sender.recovery | throw (IO.userError "Completion must retain enabled recovery.")
  ensure (sender.core.sent.isEmpty && sender.core.sendUna == sender.core.sendNext &&
      recovery.outstanding.isEmpty && recovery.deadline.isNone && recovery.timeoutCount == 0 &&
      recovery.lastTimedOut.isNone && receiver.core.received.isEmpty && receiver.receiveStore.held.isEmpty)
    "A real full ACK and read must clear the selected range, timer, and receiver bytes."
  match final.connection with
  | .startup .. => throw (IO.userError "The final state must remain an application connection.")
  | .application _ endpoints =>
    ensure (endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.releasedPayload == bytes &&
        endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes == bytes &&
        (endpoints.server.steps.filter (fun step => !step.releasedPayload.isEmpty)).length == 1)
      "Retries must release and read the selected bytes exactly once."
  let drops := dropIDs steps
  ensure (monitor.round.phase == .done && monitor.round.refs.readBytes == bytes &&
      monitor.retries == losses && monitor.drops == drops && drops.length == losses && drops.eraseDups == drops &&
      final.custody.count .dropped == prepared.custody.count .dropped + losses &&
      final.custody.count .assigned == prepared.custody.count .assigned + countAssigned steps &&
      final.custody.count .delivered == prepared.custody.count .delivered + countDelivered steps &&
      final.custody.pending.map (·.id) == prepared.custody.pending.map (·.id) &&
      final.work.pending.map (·.id) == prepared.work.pending.map (·.id) &&
      steps.all (fun actual => match actual.event with | .copyPacket .. => false | _ => true))
    "The selected suffix must charge its own drops and retain all older pending work."
  if 0 < losses then
    ensure (recovery.lastSample.isNone && recovery.estimator.isNone && recovery.rto == 1000 * 2 ^ losses)
      "A retried full ACK must retain the backed-off RTO without a new RTT sample."
  ensure (steps.any (positiveClock .client) && steps.any (positiveClock .server))
    "The actual selected suffix must contain successful positive clocks for both endpoints."

private def round (input : M.Input) (events : List M.Event) (bytes : List UInt8)
    (losses : List LossPoint) (checkOmissions : Bool := false) (keepHistorical : Bool := false)
    (zeroWindow : Bool := false) : IO Unit := do
  let startupPrefix ← startup events (initial input)
  ensure (startupPrefix.report.steps.length == 25) "The recovery case must use only the actual startup prefix."
  let start ← if keepHistorical then historicalWork startupPrefix else pure startupPrefix
  let prepared ← setup start bytes
  let preparedState := prepared.next.report.final
  let config : O.Config := ⟨⟨bytes, ← load (ingress preparedState .client), ← load (ingress preparedState .server)⟩, 10⟩
  let witness ← initialWitness start.report start.supported start.finished config prepared.next.report prepared.next.recorded prepared.trace
  let _ := witness.property
  let mut current := checkpoint prepared.next
  let mut monitor := O.Monitor.initial
  let mut remaining := losses
  let mut omitted : List Nat := []
  let mut negatives : List Nat := []
  let mut sawZeroRepeat := false
  for _ in List.range 650 do
    unless monitor.round.phase == .done do
      ensure (!(monitor.round.phase == .invalid)) "The selected actual step must preserve the recovery monitor."
      let some demand := O.nextDemand config current.report.final monitor
        | throw (IO.userError "Every unfinished recovery phase must have an actual demand.")
      let tag := selectedTag demand monitor
      if checkOmissions && !(omitted.contains tag) then
        omission config monitor current
        omitted := omitted ++ [tag]
      if checkOmissions && monitor.round.phase == .needAck && !(negatives.contains 1) then
        overdueAck current
        negatives := negatives ++ [1]
      let oldRank := monitor.rank config current.report.final
      let actor := match demand with
        | .tick _ | .timeout => Check.CampusTCPModel.Actor.server
        | _ => if monitor.round.phase == .dataIngress then .server else .client
      let selected ← load (endpoint current.report.final actor)
      let millis := match demand with
        | .tick _ | .timeout => selected.now
        | _ => selected.now + config.quantum
      let waitEvent : M.Event := .advanceClock actor millis
      ensure (O.allowed config current.report.final monitor waitEvent)
        "The service stall must be an allowed actual clock operation."
      let stalled ← appendOne current waitEvent
      monitor := O.observe config monitor stalled.actual
      current := stalled.next
      let some demandNow := O.nextDemand config current.report.final monitor
        | throw (IO.userError "The clock stall must retain the selected operation.")
      ensure (demand == demandNow) "A service stall must retain its exact demand."
      let mut event := demandNow.event
      let mut dropped := none
      match demandNow, remaining with
      | .resolution _ packet, loss :: rest =>
        if lossPoint monitor.round.phase == some loss then
          event := .dropPacket packet
          dropped := some packet
          remaining := rest
      | _, _ => pure ()
      ensure (O.allowed config current.report.final monitor event) "The selected operation must be allowed before evaluation."
      if checkOmissions && demandNow == .timeout && !(negatives.contains 2) then
        rejectedOperation current (.timeout .client false) .client (.reject .policy) true
        ensure (!(O.allowed config current.report.final monitor (.timeout .client false)))
          "Denied timeout policy must fall outside the positive recovery schedule."
        negatives := negatives ++ [2]
      if checkOmissions && monitor.drops.length == 2 && !(negatives.contains 3) then
        match Check.CampusTCPRecoveryRoundMonitor.packetAt monitor with
        | some packet =>
          ensure (!(O.allowed config current.report.final monitor (.dropPacket packet)))
            "A third selected drop must fail the combined suffix budget."
          negatives := negatives ++ [3]
        | none => pure ()
      if zeroWindow && monitor.retries > 0 && monitor.round.phase == .dataTicket then
        match current.report.final.primary.transport.admission.phase with
        | .data session =>
          ensure (session.original.peerWindow.val == 0)
            "The repeated data must reach a gateway with a zero advertised window."
          sawZeroRepeat := true
        | _ => throw (IO.userError "The repeated range must retain an established gateway session.")
      let before := current.report.final
      let moved ← appendOne current event
      monitor := O.observe config monitor moved.actual
      current := moved.next
      ensure (monitor.rank config current.report.final < oldRank)
        "Every demanded operation, retry tick, or selected drop must decrease the concrete rank."
      match event with
      | .send .client _ true =>
        if checkOmissions then
          rejectedOperation current (.timeout .client true) .client (.reject (.recovery .early)) true
          negatives := negatives ++ [4]
      | .timeout .client true =>
        checkRetry before current.report.final moved.actual bytes monitor.retries
        if checkOmissions && monitor.retries == 2 then
          exhaustedTimeout current
          negatives := negatives ++ [5]
      | _ => pure ()
      match dropped with
      | some id => noDropReplay current id
      | none => pure ()
  ensure (remaining.isEmpty && monitor.round.phase == .done) "The actual recovery must consume its loss word and complete."
  let used := current.recorded.length
  ensure (used ≤ 650) "The actual service-2 recovery must fit its 650-slot coarse bound."
  let client ← load (endpoint current.report.final .client)
  for _ in List.range (650 - used) do
    let padded ← appendOne current (.advanceClock .client client.now)
    monitor := O.observe config monitor padded.actual
    current := padded.next
  let allowed ← load (verify (B.actions config preparedState O.Monitor.initial current.recorded = true)
    "All actual selected suffix slots must satisfy the recovery schedule guards.")
  let _ := (B.actions_correct config preparedState O.Monitor.initial current.recorded).mp allowed.property
  let serviced ← load (verify (B.check config preparedState O.Monitor.initial current.recorded 2 = true)
    "Every persistent actual recovery demand must be served within two evaluated slots.")
  let _ := (B.check_correct config preparedState O.Monitor.initial current.recorded 2).mp serviced.property
  let enough ← load (verify (650 ≤ current.recorded.length) "The bounded theorem must receive at least 650 evaluated slots.")
  have actualRead := bounded_actual_read start.report prepared.next.report config witness.property current.recorded
    current.report.final current.suffix rfl allowed.property serviced.property enough.property
  let _ := actualRead
  ensure (current.recorded.length == 650) "The bounded theorem must use exactly the supplied 650 evaluated slots."
  checkComplete preparedState current.report.final current.recorded monitor bytes losses.length
  if zeroWindow then ensure sawZeroRepeat "The window regression must exercise a real repeated range at zero window."
  if checkOmissions then ensure (omitted.length == 11) "Omission cases must cover nine phases, retry ticks, and timeout service."
  if checkOmissions then ensure (negatives.length == 5) "Guard negatives must cover ACK time, retry policy, drop credit, early time, and exhausted retries."
  if keepHistorical then
    ensure (preparedState.custody.count .dropped == 1 && current.report.final.custody.count .dropped == 3)
      "The two-drop bound must apply to the selected suffix, with an earlier drop retained."
  IO.println s!"Recovery loss word {repr losses}: {used} active slots, {monitor.retries} retries, 650 evaluated slots."
  IO.println "Bounded recovery theorem applied to this same actual suffix."

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json"))
  ensure (lossWords.length == 21) "The recovery test must cover all zero-, one-, and two-loss words."
  for losses in lossWords do
    round input.model input.events [37] losses (losses == [.ackLink, .ackLink])
  let fullWindow := { input.model with passive := { input.model.passive with capacity := 8 } }
  round fullWindow input.events [1, 2, 3, 4, 5, 6, 7, 8] [.ackLink] false false true
  round input.model input.events [91] [.dataIngress, .ackLink] false true
  IO.println "Campus generated bounded recovery tests passed."

end NetlibTest.CampusTCPRecoveryRound
