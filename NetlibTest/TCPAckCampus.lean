import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPAckFacts
import Netlib.Check.CampusTCPTransferFacts

namespace NetlibTest.TCPAckCampus

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Actor Connection Report Served)
end M
namespace F
export Check.CampusTCPFacts (At findStep)
end F
namespace C
export Check.CampusTCPAckFacts (Evidence Assurance CampusCausal evidence assure)
end C

abbrev Work := TCP.AckReaction.Work
abbrev Cause := Theory.TimedReaction.Cause Unit TCP.AckReaction.Demand
abbrev Completion := Theory.TimedReaction.Discharge Unit TCP.AckReaction.Demand TCP.AckReaction.Acknowledgment

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

structure CauseCase (state : Work) where
  completion : Completion
  completed : completion ∈ state.completed
  cause : Cause
  member : cause ∈ completion.causes

private def findCause (state : Work) (id : Nat) : Except String (CauseCase state) := do
  match group : state.completed.find? (fun completion => completion.causes.any (fun cause => decide (cause.id = id))) with
  | none => throw "The actual completed ACK cause is missing."
  | some completion =>
    match found : completion.causes.find? (fun cause => decide (cause.id = id)) with
    | none => throw "The selected ACK group has no matching actual cause."
    | some cause => return ⟨completion, List.mem_of_find?_eq_some group, cause, List.mem_of_find?_eq_some found⟩

def workAt (actor : M.Actor) : M.Connection active passive → Work
  | .startup .. => Theory.TimedReaction.initial ()
  | .application _ endpoints => TCP.AckTrace.work (match actor with | .client => endpoints.client.current | .server => endpoints.server.current)

def nowAt (actor : M.Actor) : M.Connection active passive → Nat
  | .startup .. => 0
  | .application _ endpoints => (match actor with | .client => endpoints.client.current | .server => endpoints.server.current).now

structure ApplicationAt (report : M.Report input events) (time : Nat) (actor : M.Actor) where
  joint : F.At report time
  step : TCP.ApplicationTrace.Step
  present : joint.step.result.application = some (actor, step)

private def applicationAt (report : M.Report input events) (time : Nat) (actor : M.Actor) :
    Except String (ApplicationAt report time actor) := do
  let joint ← F.findStep report time
  match present : joint.step.result.application with
  | none => throw "The actual endpoint operation is missing."
  | some (selected, step) =>
    let same ← verify (selected = actor) "The actual endpoint operation used a different actor."
    return ⟨joint, step, by simpa only [same.property] using present⟩

structure ServiceAt (report : M.Report input events) (time : Nat) where
  joint : F.At report time
  served : M.Served input
  present : joint.step.result.service = some served

private def serviceAt (report : M.Report input events) (time : Nat) : Except String (ServiceAt report time) := do
  let joint ← F.findStep report time
  match present : joint.step.result.service with
  | none => throw "The actual gateway service is missing."
  | some served => return ⟨joint, served, present⟩

def fixturePayload (start count : Nat) : List UInt8 :=
  (List.range count).map (fun index => UInt8.ofNat ((start + index) % 251))

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  evidence : C.Evidence report
  assurance : C.Assurance report
  transfer : Check.CampusTCPTransferFacts.Assurance report
  clientEnabled : assurance.application.endpoints.client.current.ackReaction.isSome = true
  serverEnabled : assurance.application.endpoints.server.current.ackReaction.isSome = true
  client : TCP.AckReaction.State
  clientStored : assurance.application.endpoints.client.current.ackReaction = some client
  server : TCP.AckReaction.State
  serverStored : assurance.application.endpoints.server.current.ackReaction = some server
  offers : (TCP.Handshake.receiveOffer input.model.active).limit = 1200 ∧
    (TCP.Handshake.receiveOffer input.model.passive).limit = 800
  outgoing : assurance.application.endpoints.client.current.effectiveMSS = 800 ∧
    assurance.application.endpoints.server.current.effectiveMSS = 1200
  clientCases : List (CauseCase (TCP.AckTrace.work assurance.application.endpoints.client.current))
  serverCases : List (CauseCase (TCP.AckTrace.work assurance.application.endpoints.server.current))
  clientIDs : clientCases.map (fun selected => selected.cause.id) = List.range 5
  serverIDs : serverCases.map (fun selected => selected.cause.id) = List.range 5
  counts : client.work.nextID = 5 ∧ client.work.completed.length = 5 ∧
    server.work.nextID = 5 ∧ server.work.completed.length = 4
  delayedCause : CauseCase (TCP.AckTrace.work assurance.application.endpoints.client.current)
  serverFirst : CauseCase (TCP.AckTrace.work assurance.application.endpoints.server.current)
  serverSecond : CauseCase (TCP.AckTrace.work assurance.application.endpoints.server.current)
  serverWindow : CauseCase (TCP.AckTrace.work assurance.application.endpoints.server.current)
  keys : delayedCause.cause.id = 0 ∧ serverFirst.cause.id = 0 ∧ serverSecond.cause.id = 1 ∧ serverWindow.cause.id = 4
  preserved : (workAt .client transfer.step.before.connection).pending = [delayedCause.cause] ∧
    Theory.TimedReaction.pendingDue (workAt .client transfer.step.before.connection) = some 649 ∧
    nowAt .client transfer.step.before.connection = 200
  copiedCut : transfer.installation.checkpoint.snapshot.cut = 7
  delayed : TCP.ApplicationTrace.OutputAt assurance.application.endpoints.client.steps
  delayedStamp : delayed.step.stamp = 65
  delayedClock : delayed.step.before.now = 649
  delayedGroup : (TCP.AckTrace.work delayed.step.result.state).completed = [delayedCause.completion]
  delayBound : delayedCause.cause.issuedAt = 150 ∧ delayedCause.cause.due = 649 ∧ delayedCause.completion.time = 649
  piggyback : TCP.ApplicationTrace.OutputAt assurance.application.endpoints.server.steps
  piggybackStamp : piggyback.step.stamp = 43
  coalesced : serverFirst.completion = serverSecond.completion ∧
    serverFirst.completion.causes = [serverFirst.cause, serverSecond.cause] ∧
    serverFirst.cause.due = 599 ∧ serverSecond.cause.due = 649 ∧ serverFirst.completion.time = 150
  piggybackGroup : (TCP.AckTrace.work piggyback.step.result.state).completed = [serverFirst.completion]
  early : ApplicationAt report 62 .client
  earlyDecision : early.step.result.decision = .reject (.ack .early)
  earlyNoOutput : early.step.result.output = none
  suppressed : ApplicationAt report 127 .server
  suppressedCredit : Theory.TimedReaction.credit (TCP.AckTrace.work suppressed.step.result.state) = 0
  smallOutput : TCP.ApplicationTrace.OutputAt assurance.application.endpoints.server.steps
  smallOutputStamp : smallOutput.step.stamp = 131
  suppressedWindow : smallOutput.output.packet.segment.window.val = 2496 ∧ smallOutput.step.before.core.window = 3695
  thresholdRead : ApplicationAt report 136 .server
  thresholdAccepted : thresholdRead.step.result.decision = .accepted (.read 1)
  windowCause : serverWindow.cause.demand.kind = .window ∧ serverWindow.cause.issuedAt = 8400 ∧
    serverWindow.cause.due = 8400 ∧ serverWindow.cause.demand.minimumEdge = 5296
  windowOutput : TCP.ApplicationTrace.OutputAt assurance.application.endpoints.server.steps
  windowOutputStamp : windowOutput.step.stamp = 137
  reopenedWindow : windowOutput.output.packet.segment.window.val = 3696 ∧ serverWindow.completion.time = 8400
  serverRead : assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    fixturePayload 17 800 ++ fixturePayload 33 800
  clientRead : assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
    fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200
  deniedData : ServiceAt report 148
  deniedWindow : ServiceAt report 153
  currentData : (Check.SessionFirewall.stateAt input.model.context.authentication deniedData.joint.step.before.authentication).auth.authorized = false
  currentWindow : (Check.SessionFirewall.stateAt input.model.context.authentication deniedWindow.joint.step.before.authentication).auth.authorized = false
  deniedDataOrigin : deniedData.served.ticket.value.produced.time = 146
  deniedWindowOrigin : deniedWindow.served.ticket.value.produced.time = 151

theorem Demonstration.rmss (value : Demonstration input) : value.client.rmss = 1200 ∧ value.server.rmss = 800 := by
  exact ⟨(value.assurance.client.rmss value.client value.clientStored).trans value.offers.1,
    (value.assurance.server.rmss value.server value.serverStored).trans value.offers.2⟩

theorem Demonstration.transfer_preserves_cause (value : Demonstration input) :
    (workAt .client value.transfer.step.result.state.connection).pending = [value.delayedCause.cause] ∧
      Theory.TimedReaction.pendingDue (workAt .client value.transfer.step.result.state.connection) = some 649 ∧
      nowAt .client value.transfer.step.result.state.connection = 200 := by
  rw [value.transfer.origin.connection]
  exact value.preserved

theorem Demonstration.prefixes (value : Demonstration input) :
    value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      (value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 1600 ∧
      (value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes).length = 3600 := by
  have server := congrArg List.length value.serverRead
  have client := congrArg List.length value.clientRead
  simp only [fixturePayload, List.length_append, List.length_map, List.length_range] at server client
  exact ⟨value.assurance.application_prefix.1, value.assurance.application_prefix.2, server, client⟩

theorem Demonstration.client_causal (value : Demonstration input)
    (selected : CauseCase (TCP.AckTrace.work value.assurance.application.endpoints.client.current)) :
    ∃ scope : C.CampusCausal value.report value.assurance.application.endpoints.server.steps .client
        value.assurance.application.endpoints.client.steps selected.completion selected.cause,
      scope.causal.issuer.stamp < scope.causal.response.step.stamp ∧
      scope.causal.response.step.before.now - scope.causal.issuer.before.now < 500 ∧
      selected.cause.demand.cursor.add (selected.completion.output.position - selected.cause.demand.position) =
        scope.causal.response.output.packet.segment.acknowledgment := by
  obtain ⟨scope⟩ := value.assurance.client_causal value.clientEnabled selected.completion selected.completed selected.cause selected.member
  exact ⟨scope, scope.causal.strict_earlier value.assurance.application.endpoints.client.ordered,
    scope.causal.strict_delay, scope.causal.sequence_coverage.2⟩

theorem Demonstration.server_causal (value : Demonstration input)
    (selected : CauseCase (TCP.AckTrace.work value.assurance.application.endpoints.server.current)) :
    ∃ scope : C.CampusCausal value.report value.assurance.application.endpoints.client.steps .server
        value.assurance.application.endpoints.server.steps selected.completion selected.cause,
      scope.causal.issuer.stamp < scope.causal.response.step.stamp ∧
      scope.causal.response.step.before.now - scope.causal.issuer.before.now < 500 ∧
      selected.cause.demand.cursor.add (selected.completion.output.position - selected.cause.demand.position) =
        scope.causal.response.output.packet.segment.acknowledgment := by
  obtain ⟨scope⟩ := value.assurance.server_causal value.serverEnabled selected.completion selected.completed selected.cause selected.member
  exact ⟨scope, scope.causal.strict_earlier value.assurance.application.endpoints.server.ordered,
    scope.causal.strict_delay, scope.causal.sequence_coverage.2⟩

theorem Demonstration.current_denial (value : Demonstration input) :
    value.deniedData.served.evidence.output = none ∧ value.deniedWindow.served.evidence.output = none := by
  exact ⟨Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.assurance.application.compliant
      value.deniedData.joint.step value.deniedData.joint.member value.deniedData.served value.deniedData.present value.currentData,
    Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.assurance.application.compliant
      value.deniedWindow.joint.step value.deniedWindow.joint.member value.deniedWindow.served value.deniedWindow.present value.currentWindow⟩

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let evidence ← C.evidence report
  let assurance ← C.assure evidence
  let transfer ← Check.CampusTCPTransferFacts.assure report
  let clientEnabled ← verify (assurance.application.endpoints.client.current.ackReaction.isSome = true) "The client ACK profile is disabled."
  let serverEnabled ← verify (assurance.application.endpoints.server.current.ackReaction.isSome = true) "The server ACK profile is disabled."
  match clientStored : assurance.application.endpoints.client.current.ackReaction,
      serverStored : assurance.application.endpoints.server.current.ackReaction with
  | some client, some server =>
    let offers ← verify ((TCP.Handshake.receiveOffer input.model.active).limit = 1200 ∧
      (TCP.Handshake.receiveOffer input.model.passive).limit = 800) "The own startup receive offers differ."
    let outgoing ← verify (assurance.application.endpoints.client.current.effectiveMSS = 800 ∧
      assurance.application.endpoints.server.current.effectiveMSS = 1200) "The directional outgoing limits differ."
    let clientWork := TCP.AckTrace.work assurance.application.endpoints.client.current
    let serverWork := TCP.AckTrace.work assurance.application.endpoints.server.current
    let c0 ← findCause clientWork 0
    let c1 ← findCause clientWork 1
    let c2 ← findCause clientWork 2
    let c3 ← findCause clientWork 3
    let c4 ← findCause clientWork 4
    let s0 ← findCause serverWork 0
    let s1 ← findCause serverWork 1
    let s2 ← findCause serverWork 2
    let s3 ← findCause serverWork 3
    let s4 ← findCause serverWork 4
    let clientCases := [c0, c1, c2, c3, c4]
    let serverCases := [s0, s1, s2, s3, s4]
    let clientIDs ← verify (clientCases.map (fun selected => selected.cause.id) = List.range 5) "The client cause identities differ."
    let serverIDs ← verify (serverCases.map (fun selected => selected.cause.id) = List.range 5) "The server cause identities differ."
    let counts ← verify (client.work.nextID = 5 ∧ client.work.completed.length = 5 ∧
      server.work.nextID = 5 ∧ server.work.completed.length = 4) "The actual cause and discharge counts differ."
    let keys ← verify (c0.cause.id = 0 ∧ s0.cause.id = 0 ∧ s1.cause.id = 1 ∧ s4.cause.id = 4) "The selected cause keys differ."
    let preserved ← verify ((workAt .client transfer.step.before.connection).pending = [c0.cause] ∧
      Theory.TimedReaction.pendingDue (workAt .client transfer.step.before.connection) = some 649 ∧
      nowAt .client transfer.step.before.connection = 200) "The pending client cause did not reach the actual installation cut."
    let copiedCut ← verify (transfer.installation.checkpoint.snapshot.cut = 7) "The actual copied gateway cut differs."
    let delayed ← TCP.ApplicationTrace.findOutput assurance.application.endpoints.client.steps 65
    let delayedClock ← verify (delayed.val.step.before.now = 649) "The delayed response used a different local clock."
    let delayedGroup ← verify ((TCP.AckTrace.work delayed.val.step.result.state).completed = [c0.completion])
      "The actual dispatch did not create the selected completed group."
    let delayBound ← verify (c0.cause.issuedAt = 150 ∧ c0.cause.due = 649 ∧ c0.completion.time = 649)
      "The actual delayed ACK did not use the 499 millisecond boundary."
    let piggyback ← TCP.ApplicationTrace.findOutput assurance.application.endpoints.server.steps 43
    let coalesced ← verify (s0.completion = s1.completion ∧ s0.completion.causes = [s0.cause, s1.cause] ∧
      s0.cause.due = 599 ∧ s1.cause.due = 649 ∧ s0.completion.time = 150) "The piggyback response lost its coalesced causes."
    let piggybackGroup ← verify ((TCP.AckTrace.work piggyback.val.step.result.state).completed = [s0.completion])
      "The actual data send did not create the coalesced ACK group."
    let early ← applicationAt report 62 .client
    let earlyDecision ← verify (early.step.result.decision = .reject (.ack .early)) "The early dispatch decision differs."
    let earlyNoOutput ← match absent : early.step.result.output with
      | none => pure (show { _value : Unit // early.step.result.output = none } from ⟨(), absent⟩)
      | some _ => throw "The early dispatcher produced a packet."
    let suppressed ← applicationAt report 127 .server
    let suppressedCredit ← verify (Theory.TimedReaction.credit (TCP.AckTrace.work suppressed.step.result.state) = 0)
      "The small server read incorrectly granted response credit."
    let smallOutput ← TCP.ApplicationTrace.findOutput assurance.application.endpoints.server.steps 131
    let suppressedWindow ← verify (smallOutput.val.output.packet.segment.window.val = 2496 ∧ smallOutput.val.step.before.core.window = 3695)
      "The actual data output exposed the suppressed small-window advance."
    let thresholdRead ← applicationAt report 136 .server
    let thresholdAccepted ← verify (thresholdRead.step.result.decision = .accepted (.read 1)) "The threshold read differs."
    let windowCause ← verify (s4.cause.demand.kind = .window ∧ s4.cause.issuedAt = 8400 ∧
      s4.cause.due = 8400 ∧ s4.cause.demand.minimumEdge = 5296) "The threshold read lost its actual immediate window cause."
    let windowOutput ← TCP.ApplicationTrace.findOutput assurance.application.endpoints.server.steps 137
    let reopenedWindow ← verify (windowOutput.val.output.packet.segment.window.val = 3696 ∧ s4.completion.time = 8400)
      "The actual window response did not expose the permitted right-edge advance."
    let serverRead ← verify (assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
      fixturePayload 17 800 ++ fixturePayload 33 800) "The server read history repeated or omitted bytes."
    let clientRead ← verify (assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes =
      fixturePayload 81 1200 ++ fixturePayload 97 1200 ++ fixturePayload 113 1200) "The client read history repeated or omitted bytes."
    let deniedData ← serviceAt report 148
    let deniedWindow ← serviceAt report 153
    let currentData ← verify ((Check.SessionFirewall.stateAt input.model.context.authentication deniedData.joint.step.before.authentication).auth.authorized = false)
      "The data ACK service did not use current Logoff state."
    let currentWindow ← verify ((Check.SessionFirewall.stateAt input.model.context.authentication deniedWindow.joint.step.before.authentication).auth.authorized = false)
      "The window ACK service did not use current Logoff state."
    let deniedDataOrigin ← verify (deniedData.served.ticket.value.produced.time = 146) "The denied service selected a different data ACK."
    let deniedWindowOrigin ← verify (deniedWindow.served.ticket.value.produced.time = 151) "The denied service selected a different window ACK."
    return ⟨report, evidence, assurance, transfer, clientEnabled.property, serverEnabled.property,
      client, clientStored, server, serverStored, offers.property, outgoing.property, clientCases, serverCases,
      clientIDs.property, serverIDs.property, counts.property, c0, s0, s1, s4, keys.property, preserved.property,
      copiedCut.property, delayed.val, delayed.property, delayedClock.property, delayedGroup.property, delayBound.property,
      piggyback.val, piggyback.property, coalesced.property, piggybackGroup.property, early, earlyDecision.property,
      earlyNoOutput.property, suppressed, suppressedCredit.property, smallOutput.val, smallOutput.property,
      suppressedWindow.property, thresholdRead, thresholdAccepted.property, windowCause.property, windowOutput.val,
      windowOutput.property, reopenedWindow.property, serverRead.property, clientRead.property,
      deniedData, deniedWindow, currentData.property, currentWindow.property, deniedDataOrigin.property, deniedWindowOrigin.property⟩
  | _, _ => throw "The final campus endpoint lost its enabled ACK profile."

def run : IO Unit := do
  let input ← match Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json") with
    | .ok input => pure input
    | .error reason => throw (IO.userError reason)
  let value ← match demonstrate input with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let _ := value.rmss
  let _ := value.transfer_preserves_cause
  let _ := value.prefixes
  let _ := value.current_denial
  for selected in value.clientCases do let _ := value.client_causal selected; pure ()
  for selected in value.serverCases do let _ := value.server_causal selected; pure ()
  unless value.report.steps.length == 154 && value.report.remaining.isEmpty do
    throw (IO.userError "The ACK witness must retain the full actual replay.")
  unless value.deniedData.served.evidence.output.isNone && value.deniedWindow.served.evidence.output.isNone &&
      value.deniedData.served.ticket.value.gateway == .standby && value.deniedWindow.served.ticket.value.gateway == .standby &&
      !value.report.final.standby.transport.tracker.records.isEmpty do
    throw (IO.userError "Current standby denial must retain the cached binding and emit no gateway packet.")
  IO.println "Checked campus TCP ACK tests passed."

end NetlibTest.TCPAckCampus
