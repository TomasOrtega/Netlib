import Netlib.Check.CampusTCPRoundLocal
import Netlib.Check.CampusTCPCustodyFacts

/-!
# Actual ACK output in a campus TCP round

The preceding endpoint state supplies the ACK cause and packet fields.
The checked output creates the next ingress packet in the same history.
-/

namespace Netlib.Check.CampusTCPRoundAck

open Protocol.TCP CampusTCPModel CampusTCPEnabled

variable {input : Input} {events : List Event}

structure AckFacts (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actor : Actor) (actual : Step input) where
  beforeEq : actual.before = before
  event : actual.event = .emitAck actor true
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  localStep : T.Step
  made : localStep = ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.emitAck true) before.time
  application : actual.result.application = some (actor, localStep)
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin localStep packet
  production : produced = .application actor localStep packet origin
  encoded : Endpoint.emit (endpoint endpoints actor) [] = .ok packet
  payload : packet.packet.segment.payload = []
  header : packet.packet.header = Output.reverse (endpoint endpoints actor).core.inbound
  sequence : packet.packet.segment.sequence = (endpoint endpoints actor).core.sendNext
  acknowledgment : packet.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext
  profile : Admission.DataProfile packet.packet.segment
  ttl : 1 < packet.packet.ip.packet.ttl.toNat
  after : Applications complete
  connection : actual.result.state.connection = .application complete after
  selected : endpoint after actor = Endpoint.outputState (endpoint endpoints actor)
  peer : endpoint after actor.other = endpoint endpoints actor.other
  selectedSteps : applicationSteps after actor = applicationSteps endpoints actor ++ [localStep]
  peerSteps : applicationSteps after actor.other = applicationSteps endpoints actor.other
  localBefore : localStep.before = endpoint endpoints actor
  localEvent : localStep.event = .emitAck true
  localStamp : localStep.stamp = before.time
  prepared : Endpoint.AckPrepared (endpoint after actor)
  source : actual.result.state.outputs[before.outputs.length]? = some produced
  pending : IngressPending actual.result.state before.outputs.length
  minted : ∃ item ∈ actual.result.state.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress before.outputs.length produced
  environment : CampusTCPRoundEnvironment.environment before =
    CampusTCPRoundEnvironment.environment actual.result.state
  resident : ∀ gateway, actual.result.state.resident gateway = before.resident gateway

private theorem application_passed (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.passed = true := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem Report.emitAck_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (prepared : Endpoint.AckPrepared (endpoint endpoints actor))
    (available : Endpoint.ResponseAvailable (endpoint endpoints actor) false) :
    ∃ actual : Step input, Nonempty (AckFacts report.final complete endpoints actor actual) := by
  have chronology := CampusTCPChronology.Report.application_before report complete endpoints connection
  have earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < report.final.time := by
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨effect, produced, computed, supported, output, _, empty, _⟩ :=
    CampusTCPEnabled.emitAck_enabled report.final complete endpoints connection actor earlier prepared available
  let actual : Step input := ⟨report.final, .emitAck actor true, effect, computed⟩
  let localStep := ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.emitAck true) report.final.time
  have application : actual.result.application = some (actor, localStep) :=
    CampusTCPRoundLocal.step_application_recorded actual complete endpoints connection actor (.emitAck true)
      (.emitAck true) earlier
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete endpoints
    connection actor (.emitAck true) (.emitAck true) localStep application produced output
  have payload : packet.packet.segment.payload = [] := by
    simpa only [production, Produced.output] using empty
  have noRetry : ApplicationTrace.NoRetry localStep := by
    intro policy event
    cases event
  obtain ⟨bytes, original⟩ := CampusTCPRoundLocal.original_encoded origin noRetry
  have bytesEmpty : bytes = [] := (Endpoint.emit_payload _ _ _ original).symm.trans payload
  have encoded : Endpoint.emit (endpoint endpoints actor) [] = .ok packet := by
    simpa only [localStep, ApplicationTrace.Step.make, bytesEmpty] using original
  have fields := Endpoint.emit_transport _ _ _ encoded
  have profile := CampusTCPRoundLocal.emit_profile _ _ _ encoded
  obtain ⟨wire, sent, _⟩ := Endpoint.emitAck_success_enabled (endpoint endpoints actor)
    (endpoint_valid endpoints actor) prepared available
  have localState : localStep.result.state = Endpoint.outputState (endpoint endpoints actor) := by
    change (Endpoint.emitAck (endpoint endpoints actor) true).state = _
    rw [sent]
  obtain ⟨after, connected, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete endpoints connection actor (.emitAck true)
      (.emitAck true) localStep application
  have source : actual.result.state.outputs[report.final.outputs.length]? = some produced := by
    rw [CampusTCPOrigins.output_history actual, output]
    change (report.final.outputs ++ [produced])[report.final.outputs.length]? = some produced
    simp
  obtain ⟨item, member, parent, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced output
  have pending : IngressPending actual.result.state report.final.outputs.length := by
    refine ⟨item, member, ?_⟩
    simp only [minted, Transit.ingressAt]
    exact beq_self_eq_true _
  have passed : actual.result.passed = true := by
    obtain ⟨core, custody, accepted, same⟩ := actual.processed
    have applied : applyApplication input report.final actor (.emitAck true) = .ok core := accepted
    simpa only [same] using application_passed report.final actor (.emitAck true) core applied
  refine ⟨actual, ⟨⟨rfl, rfl, supported, passed, localStep, rfl, application, produced, output,
    packet, origin, production, encoded, payload, fields.1, fields.2.1, fields.2.2.1,
    profile.1, profile.2.2.2, after, connected, selected.trans localState, peer, selectedSteps, peerSteps,
    localBefore, localEvent, localStamp, ?_, source, pending, ⟨item, member, parent, minted⟩, ?_, ?_⟩⟩⟩
  · rw [selected, localState]
    exact Endpoint.outputState_ackPrepared _ prepared
  · exact CampusTCPRoundEnvironment.Step.environment actual trivial
  · intro gateway
    exact CampusTCPRoundEnvironment.Step.resident_nonservice actual trivial gateway

theorem AckFacts.source_fields (facts : AckFacts before complete endpoints actor actual) :
    facts.produced.source.packet.header = Output.reverse (endpoint endpoints actor).core.inbound ∧
      facts.produced.source.packet.segment.sequence = (endpoint endpoints actor).core.sendNext ∧
      facts.produced.source.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext ∧
      facts.produced.source.packet.segment.payload = [] ∧
      Admission.DataProfile facts.produced.source.packet.segment ∧
      1 < facts.produced.source.packet.ip.packet.ttl.toNat := by
  simpa only [facts.production, Produced.source, Produced.output, WireForwarding.Source.ofInput] using
    And.intro facts.header ⟨facts.sequence, facts.acknowledgment, facts.payload, facts.profile, facts.ttl⟩

end Netlib.Check.CampusTCPRoundAck
