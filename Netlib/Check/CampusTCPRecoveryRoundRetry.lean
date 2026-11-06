import Netlib.Check.CampusTCPRecoveryRoundState
import Netlib.Check.CampusTCPTimedTimeout
import Netlib.Check.CampusTCPRoundMonitorFacts

namespace Netlib.Check.CampusTCPRecoveryRoundRetry

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move ApplicationOutput OriginalFields)
open CampusTCPRecoveryRoundState (Live)

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor observe observeTimeout nextDemand)
end M

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}
variable {sentAt retries : Nat} {released : Bool}

structure Retry (live : Live initial current sentAt retries released) (native : NativeEnv initial)
    (quantum : Nat) (monitor : M.Monitor) (actual : Step input) where
  move : Move current actual
  facts : CampusTCPTimedTimeout.TimeoutFacts current.report.final complete current.endpoints .client
    live.sender.recovery live.sender.entry actual
  next : Live initial move.after sentAt (retries + 1) released
  application : ApplicationOutput current actual .client
  localEvent : application.operation.event = .timeout true
  accepted : application.operation.result.decision = .accepted (.retry request.bytes.length)
  retryOrigin : ∃ present : application.operation.result.output = some application.packet,
    application.origin = .retry request.bytes.length true localEvent accepted present
  encoded : Endpoint.emitAt (endpoint current.endpoints .client) (endpoint current.endpoints .client).core.sendUna
    request.bytes = .ok application.packet
  fields : OriginalFields (complete := complete) (request := request) application.produced
  ttl : application.produced.source.packet.ip.packet.ttl.toNat = 64
  source : move.after.report.final.outputs[actual.before.outputs.length]? = some application.produced
  pending : IngressPending move.after.report.final actual.before.outputs.length
  minted : ∃ item ∈ move.after.report.final.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress actual.before.outputs.length application.produced
  packetID : Nat
  custody : move.after.report.final.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some packetID
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  observed : M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual =
    { monitor with
      round := { phase := .dataIngress, refs := { monitor.round.refs with
        dataOutput := some actual.before.outputs.length, dataIngressPacket := some packetID } }
      waiting := false, retries := monitor.retries + 1 }
  monitorRetries : (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).retries = retries + 1
  demand : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final
    (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) =
      some (if monitor.drops.length < 2 then .resolution (.assign actual.before.outputs.length native.dataIngress) packetID
        else .operation (.assign actual.before.outputs.length native.dataIngress))

theorem retry_at (live : Live initial current sentAt retries released) (native : NativeEnv initial)
    (quantum : Nat) (monitor : M.Monitor) (waiting : monitor.waiting = true) (count : monitor.retries = retries)
    (credit : retries < 2) (due : live.sender.entry.lastAt + live.sender.recovery.rto ≤ live.sender.recovery.now) :
    ∃ actual : Step input, Nonempty (Retry live native quantum monitor actual) := by
  let ready := live.sender.timeout_ready credit due
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPTimedTimeout.Report.timeout_enabled current.report complete current.endpoints
    current.connection .client live.sender.recovery live.sender.entry
    (live.sender.entry.lastAt + live.sender.recovery.rto) ready
  obtain ⟨appended⟩ := current.appendLocal actual facts.beforeEq facts.supported .client (.timeout true)
    (by rw [facts.event]; exact .timeout _) facts.localStep facts.application
  let move : Move current actual := ⟨appended.next, facts.beforeEq, facts.supported, facts.passed, appended.history, appended.final⟩
  have connected : Connection.application complete appended.next.endpoints = .application complete facts.after := by
    rw [← appended.next.connection, appended.final]
    exact facts.connection
  have endpoints : appended.next.endpoints = facts.after := eq_of_heq (Connection.application.inj connected).2
  have client : endpoint move.after.endpoints .client =
      Endpoint.retryState (endpoint current.endpoints .client) live.sender.recovery live.sender.entry := by
    rw [endpoints]
    exact facts.selected
  have peer : endpoint move.after.endpoints .server = endpoint current.endpoints .server := appended.peer
  have flight : CampusTCPRecoveryRoundSender.Flight initial sentAt (endpoint move.after.endpoints .client) (retries + 1) := by
    rw [client]
    exact live.sender.retry credit due
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by rw [move.final]; exact facts.environment
  have gateway (selected : Gateway) : beforeService input move.after.report.final selected = beforeService input current.report.final selected := by
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice actual (by rw [facts.event]; trivial), facts.beforeEq]
  have guards : CampusTCPRoundGuards.Guards move.after.endpoints := by
    intro actor
    cases actor
    · exact ⟨flight.coherent, flight.prepared, by rw [flight.runtime]; rfl⟩
    · rw [peer]; exact live.anchor.guards .server
  let next : Live initial move.after sentAt (retries + 1) released := {
    anchor := ⟨guards, live.anchor.retained.trans move.retained, live.anchor.environment.trans environment⟩
    sender := flight
    receiver := by rw [peer]; exact live.receiver
    gateway := live.gateway.frame (gateway .primary).symm
    history := live.history.client_local move (.timeout true) (by rw [facts.event]; exact .timeout _)
      facts.localStep facts.application
    observed := by
      intro released
      obtain ⟨seen⟩ := live.observed released
      exact ⟨seen.frame (congrArg CampusTCPService.Before.admission (gateway .primary).symm)⟩ }
  let application : ApplicationOutput current actual .client := ⟨facts.localStep, facts.application, facts.packet,
    facts.origin, facts.produced, facts.output, facts.production, facts.localBefore, facts.localStamp⟩
  have fieldsAt := facts.source_fields
  have sourceCore := live.sender.core
  have header : facts.produced.source.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound := by
    simpa only [sourceCore, CampusTCPRecoveryRoundSender.sent_core] using fieldsAt.1
  have sequence : facts.produced.source.packet.segment.sequence = input.active.iss.add 1 := by
    simpa only [sourceCore, CampusTCPRecoveryRoundSender.sent_core, complete.certificate.initial_sequences.1,
      complete.activeConfig] using fieldsAt.2.1
  have acknowledgment : facts.produced.source.packet.segment.acknowledgment = input.passive.iss.add 1 := by
    simpa only [sourceCore, CampusTCPRecoveryRoundSender.sent_core, complete.certificate.initial_sequences.2.2.1,
      complete.passiveConfig] using fieldsAt.2.2.1
  have payload : facts.produced.source.packet.segment.payload = request.bytes := fieldsAt.2.2.2.1.trans live.sender.sent
  have source : move.after.report.final.outputs[actual.before.outputs.length]? = some facts.produced := by
    rw [move.final, facts.beforeEq]
    exact facts.source
  obtain ⟨id, pendingID⟩ := CampusTCPRoundMonitorFacts.output_pending actual facts.produced facts.output
  have custody : move.after.report.final.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some id := by
    rw [move.final]; exact pendingID
  have actor : facts.produced.actor = .client := by rw [facts.production]; rfl
  have observed : M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual =
      { monitor with
        round := { phase := .dataIngress, refs := { monitor.round.refs with
          dataOutput := some actual.before.outputs.length, dataIngressPacket := some id } }
        waiting := false, retries := monitor.retries + 1 } := by
    simp only [CampusTCPRecoveryRoundMonitor.observe, facts.supported, facts.passed, Bool.and_self, ite_true,
      facts.event, waiting, CampusTCPRecoveryRoundMonitor.observeTimeout]
    rw [CampusTCPRoundMonitorFacts.observeOutput_eq monitor.round actual .client .dataIngress facts.produced
      facts.output actor pendingID]
  have accepted : application.operation.result.decision = .accepted (.retry request.bytes.length) := by
    simpa only [application, live.sender.count] using facts.accepted
  have encoded : Endpoint.emitAt (endpoint current.endpoints .client) (endpoint current.endpoints .client).core.sendUna
      request.bytes = .ok application.packet := by
    simpa only [live.sender.sent, live.sender.count, List.take_length] using facts.encoded
  refine ⟨actual, ⟨⟨move, facts, next, application, facts.localEvent, accepted, ?_,
    encoded, ⟨header, sequence, acknowledgment, payload, fieldsAt.2.2.2.2.1, ?_⟩, fieldsAt.2.2.2.2.2,
    source, ?_, ?_, id, custody, gateway, environment, observed, ?_, ?_⟩⟩⟩
  · have present : application.operation.result.output = some application.packet := by
      cases facts.origin <;> assumption
    exact ⟨present, Subsingleton.elim _ _⟩
  · rw [fieldsAt.2.2.2.2.2]
    decide
  · rw [move.final, facts.beforeEq]
    exact facts.pending
  · rw [move.final, facts.beforeEq]
    exact facts.minted
  · rw [observed]
    exact congrArg (· + 1) count
  · rw [observed]
    simp [CampusTCPRecoveryRoundMonitor.nextDemand, CampusTCPRoundMonitor.nextAction,
      CampusTCPRoundMonitor.ingressAction, CampusTCPRecoveryRoundMonitor.packetAt,
      source, custody, CampusTCPRecoveryRoundPhaseBase.config, CampusTCPRoundPhaseBase.config]
    split <;> rfl

theorem Step.retry (actual : Step input) (live : Live initial current sentAt retries released) (native : NativeEnv initial)
    (quantum : Nat) (monitor : M.Monitor) (waiting : monitor.waiting = true) (count : monitor.retries = retries)
    (credit : retries < 2) (due : live.sender.entry.lastAt + live.sender.recovery.rto ≤ live.sender.recovery.now)
    (before : actual.before = current.report.final) (event : actual.event = .timeout .client true) :
    Nonempty (Retry live native quantum monitor actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := retry_at live native quantum monitor waiting count credit due
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

end Netlib.Check.CampusTCPRecoveryRoundRetry
