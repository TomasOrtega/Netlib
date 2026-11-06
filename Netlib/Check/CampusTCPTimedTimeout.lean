import Netlib.Check.CampusTCPRoundLocal
import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Protocol.TCP.EndpointTimeoutEnabled

namespace Netlib.Check.CampusTCPTimedTimeout

open Protocol.TCP CampusTCPModel CampusTCPEnabled

variable {input : Input} {events : List Event}
variable {before : State input} {complete : H.Completed input.active input.passive}
variable {endpoints : Applications complete} {actor : Actor} {actual : Step input}
variable {recovery : Recovery.State} {entry : Recovery.Outstanding} {deadline : Nat}

structure TimeoutFacts (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actor : Actor) (recovery : Recovery.State)
    (entry : Recovery.Outstanding) (actual : Step input) where
  beforeEq : actual.before = before
  event : actual.event = .timeout actor true
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  localStep : T.Step
  made : localStep = ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.timeout true) before.time
  application : actual.result.application = some (actor, localStep)
  accepted : localStep.result.decision = .accepted (.retry entry.count)
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin localStep packet
  production : produced = .application actor localStep packet origin
  encoded : Endpoint.emitAt (endpoint endpoints actor) (endpoint endpoints actor).core.sendUna
    ((endpoint endpoints actor).core.sent.take entry.count) = .ok packet
  payload : packet.packet.segment.payload = (endpoint endpoints actor).core.sent
  header : packet.packet.header = Output.reverse (endpoint endpoints actor).core.inbound
  sequence : packet.packet.segment.sequence = (endpoint endpoints actor).core.sendUna
  acknowledgment : packet.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext
  window : packet.packet.segment.window.val = Endpoint.outputWindow (endpoint endpoints actor)
  profile : Admission.DataProfile packet.packet.segment
  ttl : packet.packet.ip.packet.ttl.toNat = 64
  after : Applications complete
  connection : actual.result.state.connection = .application complete after
  selected : endpoint after actor = Endpoint.retryState (endpoint endpoints actor) recovery entry
  peer : endpoint after actor.other = endpoint endpoints actor.other
  selectedSteps : applicationSteps after actor = applicationSteps endpoints actor ++ [localStep]
  peerSteps : applicationSteps after actor.other = applicationSteps endpoints actor.other
  localBefore : localStep.before = endpoint endpoints actor
  localEvent : localStep.event = .timeout true
  localStamp : localStep.stamp = before.time
  prepared : Endpoint.AckPrepared (endpoint after actor)
  coherent : Endpoint.RecoveryCoherent (endpoint after actor)
  runtime : (endpoint after actor).recovery = some (Recovery.timeoutState recovery entry [])
  clocked : (Recovery.timeoutState recovery entry []).Clocked
  positive : (Recovery.timeoutState recovery entry []).Positive
  karn : Recovery.sample (Recovery.timeoutState recovery entry []) entry.count = none
  source : actual.result.state.outputs[before.outputs.length]? = some produced
  pending : IngressPending actual.result.state before.outputs.length
  minted : ∃ item ∈ actual.result.state.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress before.outputs.length produced
  work : actual.result.state.work = before.work
  services : actual.result.state.services = before.services
  receipts : actual.result.state.receipts = before.receipts
  environment : CampusTCPRoundEnvironment.environment before =
    CampusTCPRoundEnvironment.environment actual.result.state
  resident : ∀ gateway, actual.result.state.resident gateway = before.resident gateway

private theorem application_frames (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.work = before.work ∧ effect.state.services = before.services ∧
      effect.state.receipts = before.receipts := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem timeout_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (recovery : Recovery.State) (entry : Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.TimeoutReady (endpoint endpoints actor) recovery entry deadline) :
    ∃ actual : Step input, Nonempty (TimeoutFacts before complete endpoints actor recovery entry actual) := by
  obtain ⟨wire, result, encoded⟩ := Endpoint.timeout_success_enabled (endpoint endpoints actor)
    recovery entry deadline (endpoint_valid endpoints actor) ready
  let localStep := ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.timeout true) before.time
  have accepted : localStep.result.decision = .accepted (.retry entry.count) := by
    change (Endpoint.timeout (endpoint endpoints actor) true).decision = _
    rw [result]
  have present : localStep.result.output = some wire := by
    change (Endpoint.timeout (endpoint endpoints actor) true).output = _
    rw [result]
  have retry : T.OutputOrigin localStep wire := .retry entry.count true rfl accepted present
  obtain ⟨effect, produced, computed, output, _, packetEq, supported, application⟩ :=
    application_emitting before complete endpoints connection actor (.timeout true) earlier wire retry
  have frames := application_frames before actor (.timeout true) effect computed
  obtain ⟨afterEffect, checked, supportEq, outputEq, appEq, _⟩ :=
    finish_step before (.timeout actor true) effect computed rfl
  let actual : Step input := ⟨before, .timeout actor true, afterEffect, checked⟩
  have recorded : actual.result.application = some (actor, localStep) := appEq.trans application
  have emitted : actual.result.output = some produced := outputEq.trans output
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete endpoints
    connection actor (.timeout true) (.timeout true) localStep recorded produced emitted
  have packetSame : packet = wire := by
    simpa only [production, Produced.output] using packetEq
  subst packet
  have fields := Endpoint.emitAt_transport _ _ _ _ encoded
  have localState : localStep.result.state = Endpoint.retryState (endpoint endpoints actor) recovery entry := by
    change (Endpoint.timeout (endpoint endpoints actor) true).state = _
    rw [result]
  obtain ⟨after, connected, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete endpoints connection actor (.timeout true)
      (.timeout true) localStep recorded
  have source : actual.result.state.outputs[before.outputs.length]? = some produced := by
    rw [CampusTCPOrigins.output_history actual, emitted]
    change (before.outputs ++ [produced])[before.outputs.length]? = some produced
    simp
  obtain ⟨item, member, parent, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced emitted
  have pending : IngressPending actual.result.state before.outputs.length := by
    refine ⟨item, member, ?_⟩
    simp only [minted, Transit.ingressAt]
    exact beq_self_eq_true _
  have stateFrames : actual.result.state.work = before.work ∧
      actual.result.state.services = before.services ∧ actual.result.state.receipts = before.receipts := by
    obtain ⟨core, custody, coreComputed, same⟩ := actual.processed
    have coreSame : core = effect := by
      have sameResult : Except.ok core = Except.ok effect := coreComputed.symm.trans computed
      exact Except.ok.inj sameResult
    simpa only [same, coreSame] using frames
  refine ⟨actual, ⟨⟨rfl, rfl, supportEq.trans supported,
    CampusTCPRoundLocal.step_local_passed actual actor (.timeout true) (.timeout true),
    localStep, rfl, recorded, accepted, produced, emitted, wire, origin, production, encoded,
    Endpoint.timeout_payload ready wire encoded, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
    ⟨.inl fields.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩, Endpoint.emitAt_ttl _ _ _ _ encoded,
    after, connected, selected.trans localState, peer, selectedSteps, peerSteps, localBefore, localEvent,
    localStamp, ?_, ?_, ?_, Endpoint.retryState_clocked ready, Endpoint.retryState_positive ready,
    Endpoint.retryState_karn ready, source, pending, ⟨item, member, parent, minted⟩,
    stateFrames.1, stateFrames.2.1, stateFrames.2.2, ?_, ?_⟩⟩⟩
  · rw [selected, localState]
    exact Endpoint.retryState_prepared ready
  · rw [selected, localState]
    exact Endpoint.retryState_coherent ready
  · rw [selected, localState]
    rfl
  · exact CampusTCPRoundEnvironment.Step.environment actual trivial
  · intro gateway
    exact CampusTCPRoundEnvironment.Step.resident_nonservice actual trivial gateway

theorem Report.timeout_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (recovery : Recovery.State) (entry : Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.TimeoutReady (endpoint endpoints actor) recovery entry deadline) :
    ∃ actual : Step input, Nonempty (TimeoutFacts report.final complete endpoints actor recovery entry actual) := by
  apply CampusTCPTimedTimeout.timeout_enabled report.final complete endpoints connection actor _ recovery entry deadline ready
  have earlier := CampusTCPChronology.Report.application_before report complete endpoints connection
  cases actor
  · exact earlier.1
  · exact earlier.2

theorem Step.timeout (actual : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : actual.before.connection = .application complete endpoints)
    (actor : Actor) (event : actual.event = .timeout actor true)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < actual.before.time)
    (recovery : Recovery.State) (entry : Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.TimeoutReady (endpoint endpoints actor) recovery entry deadline) :
    Nonempty (TimeoutFacts actual.before complete endpoints actor recovery entry actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := timeout_enabled actual.before complete endpoints connection actor earlier
    recovery entry deadline ready
  have sameResult : enabled.result = actual.result := by
    have checked := enabled.computed
    rw [facts.beforeEq, facts.event, ← event, actual.computed] at checked
    exact (Except.ok.inj checked).symm
  have same : enabled = actual := by
    have beforeEq := facts.beforeEq
    have eventEq := facts.event.trans event.symm
    cases enabled
    cases actual
    simp_all only
  exact ⟨same ▸ facts⟩

def TimeoutFacts.report (facts : TimeoutFacts before complete endpoints actor recovery entry actual)
    (report : Report input events) (same : before = report.final)
    (supported : report.supported = true) (finished : report.remaining = []) :
    Report input (events ++ [actual.event]) :=
  CampusTCPSchedule.Report.appendStep report supported finished actual (facts.beforeEq.trans same) facts.supported

theorem TimeoutFacts.report_supported (facts : TimeoutFacts before complete endpoints actor recovery entry actual)
    (report : Report input events) (same : before = report.final)
    (supported : report.supported = true) (finished : report.remaining = []) :
    (facts.report report same supported finished).supported = true :=
  CampusTCPSchedule.Report.appendStep_supported report supported finished actual
    (facts.beforeEq.trans same) facts.supported

theorem TimeoutFacts.report_member (facts : TimeoutFacts before complete endpoints actor recovery entry actual)
    (report : Report input events) (same : before = report.final)
    (supported : report.supported = true) (finished : report.remaining = []) :
    actual ∈ (facts.report report same supported finished).steps := by
  simp only [TimeoutFacts.report, CampusTCPSchedule.Report.appendStep, List.mem_append,
    List.mem_singleton, or_true]

theorem TimeoutFacts.retry_origin (facts : TimeoutFacts before complete endpoints actor recovery entry actual) :
    ∃ present : facts.localStep.result.output = some facts.packet,
      facts.origin = .retry entry.count true facts.localEvent facts.accepted present := by
  have present : facts.localStep.result.output = some facts.packet := by
    cases facts.origin <;> assumption
  exact ⟨present, Subsingleton.elim _ _⟩

theorem TimeoutFacts.source_fields (facts : TimeoutFacts before complete endpoints actor recovery entry actual) :
    facts.produced.source.packet.header = Output.reverse (endpoint endpoints actor).core.inbound ∧
      facts.produced.source.packet.segment.sequence = (endpoint endpoints actor).core.sendUna ∧
      facts.produced.source.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext ∧
      facts.produced.source.packet.segment.payload = (endpoint endpoints actor).core.sent ∧
      Admission.DataProfile facts.produced.source.packet.segment ∧
      facts.produced.source.packet.ip.packet.ttl.toNat = 64 := by
  simpa only [facts.production, Produced.source, Produced.output, WireForwarding.Source.ofInput] using
    And.intro facts.header ⟨facts.sequence, facts.acknowledgment, facts.payload, facts.profile, facts.ttl⟩

end Netlib.Check.CampusTCPTimedTimeout
