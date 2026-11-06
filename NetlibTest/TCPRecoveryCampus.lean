import Netlib.Check.CampusTCP
import Netlib.Protocol.TCP.AdmissionRecoveryFacts

namespace NetlibTest.TCPRecoveryCampus

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Actor Connection Report Served)
end M
namespace F
export Check.CampusTCPFacts (At findStep)
end F
namespace A
export TCP.ApplicationTrace (Step OutputAt)
end A

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

def endpoint (actor : M.Actor) : M.Connection active passive → Option TCP.Endpoint.State
  | .startup .. => none
  | .application _ endpoints => some (match actor with | .client => endpoints.client.current | .server => endpoints.server.current)

def endpointSteps (actor : M.Actor) : M.Connection active passive → List A.Step
  | .startup .. => []
  | .application _ endpoints => match actor with | .client => endpoints.client.steps | .server => endpoints.server.steps

def wirePayload (step : A.Step) : List UInt8 :=
  match step.result.output with | none => [] | some output => output.packet.segment.payload

def dataAttempts (steps : List A.Step) : Nat :=
  (steps.filter (fun step => !(wirePayload step).isEmpty)).length

def uniqueThrough (steps : List A.Step) (cut : Nat) : List UInt8 :=
  (steps.filter (fun step => decide (step.stamp ≤ cut))).flatMap (·.emitted)

def wireThrough (report : M.Report input events) (actor : M.Actor) (cut : Nat) : List UInt8 :=
  (report.final.outputs.filter (fun output => output.actor == actor && decide (output.time ≤ cut))).flatMap
    (fun output => output.output.packet.segment.payload)

def attemptsThrough (report : M.Report input events) (actor : M.Actor) (cut : Nat) : Nat :=
  (report.final.outputs.filter (fun output => output.actor == actor && decide (output.time ≤ cut) &&
    !output.output.packet.segment.payload.isEmpty)).length

structure ApplicationAt (report : M.Report input events) (time : Nat) (actor : M.Actor) where
  joint : F.At report time
  step : A.Step
  present : joint.step.result.application = some (actor, step)

private def applicationAt (report : M.Report input events) (time : Nat) (actor : M.Actor) :
    Except String (ApplicationAt report time actor) := do
  let joint ← F.findStep report time
  match present : joint.step.result.application with
  | none => throw "The selected joint event has no actual endpoint operation."
  | some (selected, step) =>
    let same ← verify (selected = actor) "The endpoint operation used a different actor."
    return ⟨joint, step, by simpa only [same.property] using present⟩

theorem timeout_projection (step : A.Step) (count : Nat)
    (event : step.event = .timeout true)
    (accepted : step.result.decision = .accepted (.retry count))
    (before after : TCP.Recovery.State) (stored : step.before.recovery = some before)
    (updated : step.result.state.recovery = some after) :
    TCP.Recovery.timeout before = .ok (count, after) ∧
      step.result.state = { TCP.Endpoint.outputState step.before with recovery := some after } := by
  have result : step.result = TCP.Endpoint.timeout step.before true := by
    simpa only [event, TCP.ApplicationTrace.evaluate] using step.computed
  have chosen : (TCP.Endpoint.timeout step.before true).decision = .accepted (.retry count) := by
    rw [← result]
    exact accepted
  obtain ⟨source, next, _, sourceEq, timed, changed, _, _, _, _, _⟩ :=
    TCP.Endpoint.timeout_output step.before true count chosen
  have sourceSame : source = before := Option.some.inj (sourceEq.symm.trans stored)
  subst source
  have nextEq : step.result.state = { TCP.Endpoint.outputState step.before with recovery := some next } := by
    rw [result]
    exact changed
  have nextSame : next = after := (Option.some.inj (updated.symm.trans (congrArg TCP.Endpoint.State.recovery nextEq))).symm
  subst next
  exact ⟨timed, nextEq⟩

structure Attempt (steps : List A.Step) (time count : Nat) where
  output : A.OutputAt steps
  stamp : output.step.stamp = time
  event : output.step.event = .timeout true
  accepted : output.step.result.decision = .accepted (.retry count)
  before : TCP.Recovery.State
  after : TCP.Recovery.State
  stored : output.step.before.recovery = some before
  updated : output.step.result.state.recovery = some after

theorem Attempt.timed (value : Attempt steps time count) :
    TCP.Recovery.timeout value.before = .ok (count, value.after) :=
  (timeout_projection value.output.step count value.event value.accepted value.before value.after value.stored value.updated).1

theorem Attempt.unique (value : Attempt steps time count) :
    value.output.step.result.state.core = value.output.step.before.core ∧
      value.output.step.result.state.pending = value.output.step.before.pending ∧
      value.output.step.emitted = [] := by
  have changed := (timeout_projection value.output.step count value.event value.accepted value.before value.after value.stored value.updated).2
  exact ⟨(congrArg (·.core) changed).trans rfl, (congrArg (·.pending) changed).trans rfl,
    by simp only [TCP.ApplicationTrace.Step.emitted, value.event, TCP.ApplicationTrace.emitted]⟩

theorem Attempt.deadline (value : Attempt steps time count) :
    ∃ deadline, value.before.deadline = some deadline ∧ deadline ≤ value.before.now ∧
      value.after.rto = 2 * value.before.rto ∧
      value.after.deadline = some (value.before.now + 2 * value.before.rto) := by
  let facts := TCP.Recovery.timeout_facts value.before count value.after value.timed
  exact ⟨facts.deadline, facts.timer, facts.due, TCP.Recovery.timeout_backoff _ _ _ value.timed⟩

private def attempt (steps : List A.Step) (time count : Nat) : Except String (Attempt steps time count) := do
  let output ← TCP.ApplicationTrace.findOutput steps time
  let event ← match event : output.val.step.event with
    | .timeout true => pure (show { _value : Unit // output.val.step.event = .timeout true } from ⟨(), event⟩)
    | _ => throw "The selected output is not an actual timer retry."
  let accepted ← verify (output.val.step.result.decision = .accepted (.retry count)) "The timer retry count differs."
  match stored : output.val.step.before.recovery, updated : output.val.step.result.state.recovery with
  | some before, some after => return ⟨output.val, output.property, event.property, accepted.property, before, after, stored, updated⟩
  | _, _ => throw "The actual timer attempt has no recovery state."

structure Early (report : M.Report input events) (time : Nat) (actor : M.Actor) where
  application : ApplicationAt report time actor
  event : application.step.event = .timeout true
  rejected : application.step.result.decision = .reject (.recovery .early)
  before : TCP.Recovery.State
  stored : application.step.before.recovery = some before
  deadline : Nat
  armed : before.deadline = some deadline
  premature : before.now < deadline
  noOutput : application.step.result.output = none
  unchanged : application.step.result.state = application.step.before

private def early (report : M.Report input events) (time : Nat) (actor : M.Actor) :
    Except String (Early report time actor) := do
  let application ← applicationAt report time actor
  let event ← match event : application.step.event with
    | .timeout true => pure (show { _value : Unit // application.step.event = .timeout true } from ⟨(), event⟩)
    | _ => throw "The selected early event is not a timer operation."
  let rejected ← verify (application.step.result.decision = .reject (.recovery .early)) "The early timer decision differs."
  let unchanged ← verify (application.step.result.state = application.step.before) "An early timer operation changed endpoint state."
  match stored : application.step.before.recovery with
  | none => throw "The early timer operation has no recovery state."
  | some before =>
    match armed : before.deadline with
    | none => throw "The early timer operation has no stored deadline."
    | some deadline =>
      let premature ← verify (before.now < deadline) "The early timer operation reached its deadline."
      match noOutput : application.step.result.output with
      | some _ => throw "An early timer operation produced a packet."
      | none => return ⟨application, event.property, rejected.property, before, stored, deadline, armed,
          premature.property, noOutput, unchanged.property⟩

structure RecoveryAt (report : M.Report input events) (time : Nat) (actor : M.Actor) where
  application : ApplicationAt report time actor
  before : TCP.Recovery.State
  after : TCP.Recovery.State
  stored : application.step.before.recovery = some before
  updated : application.step.result.state.recovery = some after

private def recoveryAt (report : M.Report input events) (time : Nat) (actor : M.Actor) :
    Except String (RecoveryAt report time actor) := do
  let application ← applicationAt report time actor
  match stored : application.step.before.recovery, updated : application.step.result.state.recovery with
  | some before, some after => return ⟨application, before, after, stored, updated⟩
  | _, _ => throw "The selected endpoint operation has no actual recovery state."

structure RepeatedService (report : M.Report input events) (time : Nat) where
  joint : F.At report time
  served : M.Served input
  present : joint.step.result.service = some served
  processing : Check.CampusTCPService.Processing (input.contextFor served.ticket.value.gateway)
    served.before served.ticket.value.source input.zone
  computed : served.evidence.processing = some processing
  source : TCP.Admission.Session
  phase : served.before.admission.phase = .data source
  direction : processing.prepared.attachment.direction = .original
  known : TCP.Admission.KnownRange source.original source.entry .original served.ticket.value.source.packet.segment
    served.before.admission.observations

theorem RepeatedService.range (value : RepeatedService report time) :
    ∃ seen ∈ value.served.before.admission.observations,
      seen.attachment.entry = value.source.entry ∧ seen.attachment.direction = .original ∧
      value.served.ticket.value.source.packet.segment.payload =
        (seen.segment.payload.drop
          (TCP.Seq.distance value.source.original.base value.served.ticket.value.source.packet.segment.sequence -
            TCP.Seq.distance value.source.original.base seen.segment.sequence)).take
          value.served.ticket.value.source.packet.segment.payload.length := by
  have source := value.processing.admitted.repeated_source value.phase
    (by simpa only [value.direction, TCP.Admission.Session.lane, TCP.WireForwarding.Source.asInput] using value.known)
  simpa only [value.direction, TCP.Admission.Session.lane, TCP.WireForwarding.Source.asInput] using source

private def repeatedService (report : M.Report input events) (time : Nat) :
    Except String (RepeatedService report time) := do
  let joint ← F.findStep report time
  match present : joint.step.result.service with
  | none => throw "The selected repeated range has no actual gateway service."
  | some served =>
    match computed : served.evidence.processing with
    | none => throw "The repeated range has no actual admission computation."
    | some processing =>
      match phase : served.before.admission.phase with
      | .data source =>
        let direction ← verify (processing.prepared.attachment.direction = .original) "The copied range uses a different direction."
        let known ← verify (TCP.Admission.KnownRange source.original source.entry .original
          served.ticket.value.source.packet.segment served.before.admission.observations)
          "The selected service has no exact retained first source."
        return ⟨joint, served, present, processing, computed, source, phase, direction.property, known.property⟩
      | _ => throw "The repeated range has no established source history."

def fixturePayload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

def firstSample (value : RecoveryAt report time actor) (count sent acknowledged interval : Nat) : Prop :=
  value.application.step.result.decision = .accepted (.receive count 0) ∧
    TCP.Recovery.sample value.before count = some ⟨0, sent, acknowledged⟩ ∧
    value.after.lastSample = some ⟨0, sent, acknowledged⟩ ∧
    value.after.estimator = some (TCP.RTO.first (acknowledged - sent)) ∧
    value.after.rto = interval ∧ value.after.deadline = none

instance (value : RecoveryAt report time actor) (count sent acknowledged interval : Nat) :
    Decidable (firstSample value count sent acknowledged interval) := by unfold firstSample; infer_instance

def karn (value : RecoveryAt report time actor) (count interval : Nat) : Prop :=
  value.application.step.result.decision = .accepted (.receive count 0) ∧
    value.before.outstanding.any (·.retried) = true ∧ TCP.Recovery.sample value.before count = none ∧
    value.after.estimator = value.before.estimator ∧ value.after.lastSample = value.before.lastSample ∧
    value.after.rto = interval ∧ value.before.rto = interval ∧
    value.after.deadline = none ∧ TCP.Recovery.flight value.after = 0

instance (value : RecoveryAt report time actor) (count interval : Nat) : Decidable (karn value count interval) := by
  unfold karn
  infer_instance

def freshSample (value : RecoveryAt report time actor) (count sent acknowledged interval : Nat) : Prop :=
  value.application.step.result.decision = .accepted (.receive count 0) ∧
    TCP.Recovery.sample value.before count = some ⟨2, sent, acknowledged⟩ ∧
    value.after.lastSample = some ⟨2, sent, acknowledged⟩ ∧
    value.after.estimator = some (TCP.RTO.update (TCP.RTO.first (acknowledged - sent)) (acknowledged - sent)) ∧
    value.after.rto = interval ∧ value.after.deadline = none

instance (value : RecoveryAt report time actor) (count sent acknowledged interval : Nat) :
    Decidable (freshSample value count sent acknowledged interval) := by unfold freshSample; infer_instance

def timerImage (actor : M.Actor) (connection : M.Connection active passive) : Option (Nat × Nat × Option Nat × Nat) :=
  (endpoint actor connection).bind (fun state => state.recovery.map
    (fun recovery => (recovery.now, recovery.rto, recovery.deadline, TCP.Recovery.flight recovery)))

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  assurance : Check.CampusTCPTransferFacts.Assurance report
  clientFirst : Attempt assurance.application.endpoints.client.steps 80 800
  clientSecond : Attempt assurance.application.endpoints.client.steps 92 800
  serverFirst : Attempt assurance.application.endpoints.server.steps 107 1200
  serverSecond : Attempt assurance.application.endpoints.server.steps 119 1200
  queued : Attempt assurance.application.endpoints.client.steps 165 800
  earlyClient : Early report 77 .client
  earlyClientAgain : Early report 89 .client
  earlyServer : Early report 104 .server
  earlyServerAgain : Early report 116 .server
  learnedClient : RecoveryAt report 39 .client
  learnedServer : RecoveryAt report 52 .server
  learnedClientSample : firstSample learnedClient 800 100 356 1000
  learnedServerSample : firstSample learnedServer 1200 400 1296 2688
  clientKarn : RecoveryAt report 101 .client
  serverKarn : RecoveryAt report 128 .server
  excludedClient : karn clientKarn 800 4000
  excludedServer : karn serverKarn 1200 10752
  freshClient : RecoveryAt report 141 .client
  freshServer : RecoveryAt report 154 .server
  freshClientSample : freshSample freshClient 800 10000 10256 1000
  freshServerSample : freshSample freshServer 1200 10300 11196 2240
  clientThreshold : clientFirst.after.ssthresh = 1600 ∧ clientSecond.after.ssthresh = clientFirst.after.ssthresh
  serverThreshold : serverFirst.after.ssthresh = 2400 ∧ serverSecond.after.ssthresh = serverFirst.after.ssthresh
  timers : timerImage .client assurance.step.before.connection = some (1900, 1000, some 2400, 800) ∧
    timerImage .server assurance.step.before.connection = some (1900, 2688, some 4488, 1200)
  repeated : RepeatedService report 82
  copied : (⟨repeated.served.before.tracker, repeated.served.before.admission⟩ : TCP.Checkpoint.Gateway) =
    assurance.installation.checkpoint.snapshot.source
  copiedCut : assurance.installation.checkpoint.snapshot.cut = 9
  sourceCounts : repeated.source.original.observed = 1600 ∧ repeated.source.original.acknowledged = 800 ∧
    repeated.source.reply.observed = 2400 ∧ repeated.source.reply.acknowledged = 1200
  clientWire : (wireThrough report .client 156).length = 4000 ∧ attemptsThrough report .client 156 = 5
  serverWire : (wireThrough report .server 156).length = 6000 ∧ attemptsThrough report .server 156 = 5
  clientUnique : (uniqueThrough assurance.application.endpoints.client.steps 156).length = 2400
  serverUnique : (uniqueThrough assurance.application.endpoints.server.steps 156).length = 3600
  clientReadAt : F.At report 156
  serverReadAt : F.At report 155
  clientReadResult : clientReadAt.step.result.read = fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200
  serverReadResult : serverReadAt.step.result.read = fixturePayload 17 800 ++ fixturePayload 33 800 ++ fixturePayload 49 800
  clientRead : assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200
  serverRead : assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = fixturePayload 17 800 ++ fixturePayload 33 800 ++ fixturePayload 49 800
  denied : F.At report 170
  deniedService : M.Served input.model
  deniedPresent : denied.step.result.service = some deniedService
  deniedSource : deniedService.ticket.value.produced.time = 165 ∧
    deniedService.ticket.value.source.bytes = queued.output.output.bytes
  deniedSession : TCP.Admission.Session
  deniedPhase : deniedService.before.admission.phase = .data deniedSession
  knownDenied : TCP.Admission.KnownRange deniedSession.original deniedSession.entry .original
    deniedService.ticket.value.source.packet.segment deniedService.before.admission.observations
  currentLogoff : denied.step.before.authentication = 8 ∧
    (Check.SessionFirewall.stateAt input.model.context.authentication denied.step.before.authentication).auth.authorized = false

theorem Demonstration.prefixes (value : Demonstration input) :
    value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      (value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 2400 ∧
      (value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 3600 := by
  have server := congrArg List.length value.serverRead
  have client := congrArg List.length value.clientRead
  simp only [List.length_append, fixturePayload, List.length_map, List.length_range] at server client
  exact ⟨value.assurance.application_prefix.1, value.assurance.application_prefix.2, server, client⟩

theorem Demonstration.install_preserves_endpoint (value : Demonstration input) (actor : M.Actor) :
    endpoint actor value.assurance.step.result.state.connection = endpoint actor value.assurance.step.before.connection :=
  congrArg (endpoint actor) value.assurance.origin.connection

theorem Demonstration.install_preserves_timers (value : Demonstration input) :
    timerImage .client value.assurance.step.result.state.connection = some (1900, 1000, some 2400, 800) ∧
      timerImage .server value.assurance.step.result.state.connection = some (1900, 2688, some 4488, 1200) := by
  rw [value.assurance.origin.connection]
  exact value.timers

theorem Demonstration.copied_range (value : Demonstration input) :
    ∃ seen ∈ value.assurance.installation.checkpoint.snapshot.source.admission.observations,
      seen.attachment.entry = value.repeated.source.entry ∧ seen.attachment.direction = .original ∧
      value.repeated.served.ticket.value.source.packet.segment.payload =
        (seen.segment.payload.drop
          (TCP.Seq.distance value.repeated.source.original.base value.repeated.served.ticket.value.source.packet.segment.sequence -
            TCP.Seq.distance value.repeated.source.original.base seen.segment.sequence)).take
          value.repeated.served.ticket.value.source.packet.segment.payload.length := by
  have copied := congrArg (fun gateway : TCP.Checkpoint.Gateway => gateway.admission.observations) value.copied
  rw [← copied]
  exact value.repeated.range

theorem Demonstration.revoked_retry (value : Demonstration input) : value.deniedService.evidence.output = none :=
  Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.assurance.application.compliant
    value.denied.step value.denied.member value.deniedService value.deniedPresent value.currentLogoff.2

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let assurance ← Check.CampusTCPTransferFacts.assure report
  let clientFirst ← attempt assurance.application.endpoints.client.steps 80 800
  let clientSecond ← attempt assurance.application.endpoints.client.steps 92 800
  let serverFirst ← attempt assurance.application.endpoints.server.steps 107 1200
  let serverSecond ← attempt assurance.application.endpoints.server.steps 119 1200
  let queued ← attempt assurance.application.endpoints.client.steps 165 800
  let earlyClient ← early report 77 .client
  let earlyClientAgain ← early report 89 .client
  let earlyServer ← early report 104 .server
  let earlyServerAgain ← early report 116 .server
  let learnedClient ← recoveryAt report 39 .client
  let learnedServer ← recoveryAt report 52 .server
  let learnedClientSample ← verify (firstSample learnedClient 800 100 356 1000) "The first client RTT sample differs from the actual send and ACK."
  let learnedServerSample ← verify (firstSample learnedServer 1200 400 1296 2688) "The first server RTT sample differs from the actual send and ACK."
  let clientKarn ← recoveryAt report 101 .client
  let serverKarn ← recoveryAt report 128 .server
  let excludedClient ← verify (karn clientKarn 800 4000) "The recovered client range did not retain Karn exclusion."
  let excludedServer ← verify (karn serverKarn 1200 10752) "The recovered server range did not retain Karn exclusion."
  let freshClient ← recoveryAt report 141 .client
  let freshServer ← recoveryAt report 154 .server
  let freshClientSample ← verify (freshSample freshClient 800 10000 10256 1000) "The later client sample did not update the exact estimator."
  let freshServerSample ← verify (freshSample freshServer 1200 10300 11196 2240) "The later server sample did not update the exact estimator."
  let clientThreshold ← verify (clientFirst.after.ssthresh = 1600 ∧ clientSecond.after.ssthresh = clientFirst.after.ssthresh)
    "The client retry changed the threshold for the same original range."
  let serverThreshold ← verify (serverFirst.after.ssthresh = 2400 ∧ serverSecond.after.ssthresh = serverFirst.after.ssthresh)
    "The server retry changed the threshold for the same original range."
  let timers ← verify (timerImage .client assurance.step.before.connection = some (1900, 1000, some 2400, 800) ∧
    timerImage .server assurance.step.before.connection = some (1900, 2688, some 4488, 1200))
    "The installation cut lost endpoint clock or timer state."
  let repeated ← repeatedService report 82
  let copied ← verify ((⟨repeated.served.before.tracker, repeated.served.before.admission⟩ : TCP.Checkpoint.Gateway).same
    assurance.installation.checkpoint.snapshot.source = true) "The first retry did not use the exact copied transport state."
  let copiedCut ← verify (assurance.installation.checkpoint.snapshot.cut = 9) "The copied transition cut differs."
  let sourceCounts ← verify (repeated.source.original.observed = 1600 ∧ repeated.source.original.acknowledged = 800 ∧
    repeated.source.reply.observed = 2400 ∧ repeated.source.reply.acknowledged = 1200) "The copied unique ranges differ."
  let clientWire ← verify ((wireThrough report .client 156).length = 4000 ∧ attemptsThrough report .client 156 = 5)
    "The completed client transfer must use five actual data attempts."
  let serverWire ← verify ((wireThrough report .server 156).length = 6000 ∧ attemptsThrough report .server 156 = 5)
    "The completed server transfer must use five actual data attempts."
  let clientUnique ← verify ((uniqueThrough assurance.application.endpoints.client.steps 156).length = 2400)
    "Client retries must not add unique stream bytes."
  let serverUnique ← verify ((uniqueThrough assurance.application.endpoints.server.steps 156).length = 3600)
    "Server retries must not add unique stream bytes."
  let clientReadAt ← F.findStep report 156
  let serverReadAt ← F.findStep report 155
  let clientReadResult ← verify (clientReadAt.step.result.read = fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200)
    "The actual client read repeated or omitted bytes."
  let serverReadResult ← verify (serverReadAt.step.result.read = fixturePayload 17 800 ++ fixturePayload 33 800 ++ fixturePayload 49 800)
    "The actual server read repeated or omitted bytes."
  let clientRead ← verify (assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200) "The final client read history differs."
  let serverRead ← verify (assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    fixturePayload 17 800 ++ fixturePayload 33 800 ++ fixturePayload 49 800) "The final server read history differs."
  let denied ← F.findStep report 170
  match deniedPresent : denied.step.result.service with
  | none => throw "The final denied retry has no actual gateway service."
  | some deniedService =>
    let deniedSource ← verify (deniedService.ticket.value.produced.time = 165 ∧
      deniedService.ticket.value.source.bytes = queued.output.output.bytes)
      "The denied service did not retain the exact earlier queued retry."
    match deniedPhase : deniedService.before.admission.phase with
    | .data deniedSession =>
      let knownDenied ← verify (TCP.Admission.KnownRange deniedSession.original deniedSession.entry .original
        deniedService.ticket.value.source.packet.segment deniedService.before.admission.observations)
        "The denied retry lost its exact earlier range."
      let currentLogoff ← verify (denied.step.before.authentication = 8 ∧
        (Check.SessionFirewall.stateAt input.model.context.authentication denied.step.before.authentication).auth.authorized = false)
        "The retry service did not use the current Logoff state."
      return ⟨report, assurance, clientFirst, clientSecond, serverFirst, serverSecond, queued,
        earlyClient, earlyClientAgain, earlyServer, earlyServerAgain, learnedClient, learnedServer,
        learnedClientSample.property, learnedServerSample.property, clientKarn, serverKarn, excludedClient.property,
        excludedServer.property, freshClient, freshServer, freshClientSample.property, freshServerSample.property,
        clientThreshold.property, serverThreshold.property, timers.property, repeated,
        (TCP.Checkpoint.Gateway.same_correct _ _).mp copied.property, copiedCut.property, sourceCounts.property,
        clientWire.property, serverWire.property, clientUnique.property, serverUnique.property, clientReadAt, serverReadAt,
        clientReadResult.property, serverReadResult.property, clientRead.property, serverRead.property,
        denied, deniedService, deniedPresent, deniedSource.property, deniedSession, deniedPhase, knownDenied.property, currentLogoff.property⟩
    | _ => throw "The final denied retry lost the established gateway history."

def run : IO Unit := do
  let input ← match Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-recovery/trace.json") with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let value ← match demonstrate input with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := value.prefixes
  let _ := value.install_preserves_endpoint .client
  let _ := value.install_preserves_endpoint .server
  let _ := value.install_preserves_timers
  let _ := value.copied_range
  let _ := value.revoked_retry
  for attempt in [value.clientFirst.output.step, value.clientSecond.output.step,
      value.serverFirst.output.step, value.serverSecond.output.step, value.queued.output.step] do
    unless attempt.emitted.isEmpty do throw (IO.userError "A retry added unique emitted bytes.")
  let _ := value.clientFirst.deadline
  let _ := value.clientSecond.deadline
  let _ := value.serverFirst.deadline
  let _ := value.serverSecond.deadline
  let _ := value.queued.deadline
  let _ := value.clientFirst.unique
  let _ := value.clientSecond.unique
  let _ := value.serverFirst.unique
  let _ := value.serverSecond.unique
  let _ := value.queued.unique
  unless value.report.steps.length == 171 && value.report.remaining.isEmpty do
    throw (IO.userError "The recovery witness must contain the full actual replay.")
  unless value.deniedService.ticket.value.gateway == .standby && value.deniedService.evidence.output.isNone &&
      !value.denied.step.before.standby.transport.tracker.records.isEmpty &&
      value.denied.step.result.state.standby.transport.tracker == value.denied.step.before.standby.transport.tracker do
    throw (IO.userError "Current standby denial must retain the cached binding and emit no retry.")
  IO.println "Checked campus TCP recovery tests passed."

end NetlibTest.TCPRecoveryCampus
