import Netlib.Protocol.TCP.EndpointHeadTimeoutEnabled
import Netlib.Check.CampusTCPTimedTimeout
import Netlib.Check.CampusTCPRoundPhaseBase

namespace Netlib.Check.CampusTCPGapTimeout

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

variable {input : Input} {events : List Event} {complete : H.Completed input.active input.passive}
variable {before : State input} {endpoints : Applications complete} {actor : Actor} {actual : Step input}
variable {recovery : Recovery.State} {head : Recovery.Outstanding} {tail : List Recovery.Outstanding} {deadline : Nat}

structure HeadTimeoutFacts (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (actor : Actor) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (actual : Step input) where
  beforeEq : actual.before = before
  event : actual.event = .timeout actor true
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  localStep : T.Step
  made : localStep = ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.timeout true) before.time
  application : actual.result.application = some (actor, localStep)
  accepted : localStep.result.decision = .accepted (.retry head.count)
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin localStep packet
  production : produced = .application actor localStep packet origin
  encoded : Endpoint.emitAt (endpoint endpoints actor) (endpoint endpoints actor).core.sendUna
    ((endpoint endpoints actor).core.sent.take head.count) = .ok packet
  payload : packet.packet.segment.payload = (endpoint endpoints actor).core.sent.take head.count
  length : packet.packet.segment.payload.length = head.count
  header : packet.packet.header = Output.reverse (endpoint endpoints actor).core.inbound
  sequence : packet.packet.segment.sequence = (endpoint endpoints actor).core.sendUna
  acknowledgment : packet.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext
  window : packet.packet.segment.window.val = Endpoint.outputWindow (endpoint endpoints actor)
  profile : Admission.DataProfile packet.packet.segment
  ttl : packet.packet.ip.packet.ttl.toNat = 64
  after : Applications complete
  connection : actual.result.state.connection = .application complete after
  selected : endpoint after actor = Endpoint.headRetryState (endpoint endpoints actor) recovery head tail
  peer : endpoint after actor.other = endpoint endpoints actor.other
  selectedSteps : applicationSteps after actor = applicationSteps endpoints actor ++ [localStep]
  peerSteps : applicationSteps after actor.other = applicationSteps endpoints actor.other
  localBefore : localStep.before = endpoint endpoints actor
  localEvent : localStep.event = .timeout true
  localStamp : localStep.stamp = before.time
  valid : (endpoint after actor).Valid
  prepared : Endpoint.AckPrepared (endpoint after actor)
  coherent : Endpoint.RecoveryCoherent (endpoint after actor)
  storage : Endpoint.StorageCoherent (endpoint after actor)
  runtime : (endpoint after actor).recovery = some (Recovery.timeoutState recovery head tail)
  outstanding : (Recovery.timeoutState recovery head tail).outstanding =
    { head with lastAt := recovery.now, retried := true } :: tail
  clocked : (Recovery.timeoutState recovery head tail).Clocked
  positive : (Recovery.timeoutState recovery head tail).Positive
  karn : Recovery.sample (Recovery.timeoutState recovery head tail) head.count = none
  fullKarn : Recovery.sample (Recovery.timeoutState recovery head tail)
    (Recovery.flight (Recovery.timeoutState recovery head tail)) = none
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

theorem timeout_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (recovery : Recovery.State) (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.HeadTimeoutReady (endpoint endpoints actor) recovery head tail deadline)
    (storage : Endpoint.StorageCoherent (endpoint endpoints actor)) :
    ∃ actual : Step input, Nonempty (HeadTimeoutFacts before complete endpoints actor recovery head tail actual) := by
  obtain ⟨wire, result, encoded⟩ := Endpoint.head_timeout_success_enabled (endpoint endpoints actor)
    recovery head tail deadline (endpoint_valid endpoints actor) ready
  let localStep := ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
    (.timeout true) before.time
  have accepted : localStep.result.decision = .accepted (.retry head.count) := by
    change (Endpoint.timeout (endpoint endpoints actor) true).decision = _
    rw [result]
  have present : localStep.result.output = some wire := by
    change (Endpoint.timeout (endpoint endpoints actor) true).output = _
    rw [result]
  have retry : T.OutputOrigin localStep wire := .retry head.count true rfl accepted present
  obtain ⟨effect, produced, computed, output, _, packetEq, supported, application⟩ :=
    application_emitting before complete endpoints connection actor (.timeout true) earlier wire retry
  have frames := CampusTCPTimedTimeout.application_frames before actor (.timeout true) effect computed
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
  have payload := Endpoint.head_timeout_payload ready wire encoded
  have localState : localStep.result.state = Endpoint.headRetryState (endpoint endpoints actor) recovery head tail := by
    change (Endpoint.timeout (endpoint endpoints actor) true).state = _
    rw [result]
  obtain ⟨after, connected, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete endpoints connection actor (.timeout true)
      (.timeout true) localStep recorded
  have selectedState := selected.trans localState
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
  have karn : Recovery.sample (Recovery.timeoutState recovery head tail) head.count = none := by
    apply Recovery.sample_retried _ _ { head with lastAt := recovery.now, retried := true } _ rfl
    simp only [Recovery.timeoutState, Recovery.retired, Nat.ne_of_gt ready.head_positive, ite_false,
      Nat.le_refl, ite_true, List.mem_cons_self]
  refine ⟨actual, ⟨{
    beforeEq := rfl, event := rfl, supported := supportEq.trans supported,
    passed := CampusTCPRoundLocal.step_local_passed actual actor (.timeout true) (.timeout true),
    localStep, made := rfl, application := recorded, accepted, produced, output := emitted,
    packet := wire, origin, production, encoded, payload := payload.1, length := payload.2,
    header := fields.1, sequence := fields.2.1, acknowledgment := fields.2.2.1, window := fields.2.2.2.1,
    profile := ⟨.inl fields.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩,
    ttl := Endpoint.emitAt_ttl _ _ _ _ encoded,
    after, connection := connected, selected := selectedState, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp,
    valid := endpoint_valid after actor, prepared := ?_, coherent := ?_, storage := ?_, runtime := ?_, outstanding := rfl,
    clocked := Endpoint.headRetryState_clocked ready, positive := Endpoint.headRetryState_positive ready,
    karn, fullKarn := (Endpoint.headRetryState_full_ack ready).1, source, pending, minted := ⟨item, member, parent, minted⟩,
    work := stateFrames.1, services := stateFrames.2.1, receipts := stateFrames.2.2,
    environment := CampusTCPRoundEnvironment.Step.environment actual trivial,
    resident := fun gateway => CampusTCPRoundEnvironment.Step.resident_nonservice actual trivial gateway }⟩⟩
  · rw [selectedState]
    exact Endpoint.headRetryState_prepared ready
  · rw [selectedState]
    exact Endpoint.headRetryState_coherent ready
  · rw [selectedState]
    exact Endpoint.headRetryState_storage_coherent ready storage
  · rw [selectedState]
    rfl

theorem Report.timeout_enabled (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (recovery : Recovery.State) (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.HeadTimeoutReady (endpoint endpoints actor) recovery head tail deadline)
    (storage : Endpoint.StorageCoherent (endpoint endpoints actor)) :
    ∃ actual : Step input, Nonempty (HeadTimeoutFacts report.final complete endpoints actor recovery head tail actual) := by
  apply CampusTCPGapTimeout.timeout_enabled report.final complete endpoints connection actor _ recovery head tail deadline ready storage
  have earlier := CampusTCPChronology.Report.application_before report complete endpoints connection
  cases actor
  · exact earlier.1
  · exact earlier.2

def HeadTimeoutFacts.move {current : Cut input complete}
    (facts : HeadTimeoutFacts current.report.final complete current.endpoints actor recovery head tail actual) : Move current actual :=
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual facts.beforeEq facts.supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _,
    rfl, facts.after, facts.connection⟩
  ⟨next, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩

structure TimeoutMove (current : Cut input complete) (actor : Actor) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (actual : Step input) where
  facts : HeadTimeoutFacts current.report.final complete current.endpoints actor recovery head tail actual
  move : Move current actual
  endpointsEq : move.after.endpoints = facts.after

theorem timeout_at (current : Cut input complete) (actor : Actor) (recovery : Recovery.State)
    (head : Recovery.Outstanding) (tail : List Recovery.Outstanding) (deadline : Nat)
    (ready : Endpoint.HeadTimeoutReady (endpoint current.endpoints actor) recovery head tail deadline)
    (storage : Endpoint.StorageCoherent (endpoint current.endpoints actor)) :
    ∃ actual, Nonempty (TimeoutMove current actor recovery head tail actual) := by
  obtain ⟨actual, ⟨facts⟩⟩ := Report.timeout_enabled current.report complete current.endpoints current.connection actor
    recovery head tail deadline ready storage
  exact ⟨actual, ⟨⟨facts, facts.move, rfl⟩⟩⟩

theorem Step.timeout (actual : Step input) (current : Cut input complete) (actor : Actor)
    (before : actual.before = current.report.final) (event : actual.event = .timeout actor true)
    (ready : Endpoint.HeadTimeoutReady (endpoint current.endpoints actor) recovery head tail deadline)
    (storage : Endpoint.StorageCoherent (endpoint current.endpoints actor)) :
    Nonempty (TimeoutMove current actor recovery head tail actual) := by
  obtain ⟨enabled, ⟨result⟩⟩ := timeout_at current actor recovery head tail deadline ready storage
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (result.facts.beforeEq.trans before.symm) (result.facts.event.trans event.symm)
  subst enabled
  exact ⟨result⟩

theorem TimeoutMove.selected (result : TimeoutMove current actor recovery head tail actual) :
    endpoint result.move.after.endpoints actor = Endpoint.headRetryState (endpoint current.endpoints actor) recovery head tail := by
  rw [result.endpointsEq]
  exact result.facts.selected

theorem TimeoutMove.peer (result : TimeoutMove current actor recovery head tail actual) :
    endpoint result.move.after.endpoints actor.other = endpoint current.endpoints actor.other := by
  rw [result.endpointsEq]
  exact result.facts.peer

theorem TimeoutMove.selectedSteps (result : TimeoutMove current actor recovery head tail actual) :
    applicationSteps result.move.after.endpoints actor = applicationSteps current.endpoints actor ++ [result.facts.localStep] := by
  rw [result.endpointsEq]
  exact result.facts.selectedSteps

theorem TimeoutMove.peerSteps (result : TimeoutMove current actor recovery head tail actual) :
    applicationSteps result.move.after.endpoints actor.other = applicationSteps current.endpoints actor.other := by
  rw [result.endpointsEq]
  exact result.facts.peerSteps

theorem HeadTimeoutFacts.retry_origin (facts : HeadTimeoutFacts before complete endpoints actor recovery head tail actual) :
    ∃ present : facts.localStep.result.output = some facts.packet,
      facts.origin = .retry head.count true facts.localEvent facts.accepted present := by
  have present : facts.localStep.result.output = some facts.packet := by
    cases facts.origin <;> assumption
  exact ⟨present, Subsingleton.elim _ _⟩

theorem HeadTimeoutFacts.source_fields (facts : HeadTimeoutFacts before complete endpoints actor recovery head tail actual) :
    facts.produced.source.packet.header = Output.reverse (endpoint endpoints actor).core.inbound ∧
      facts.produced.source.packet.segment.sequence = (endpoint endpoints actor).core.sendUna ∧
      facts.produced.source.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext ∧
      facts.produced.source.packet.segment.payload = (endpoint endpoints actor).core.sent.take head.count ∧
      Admission.DataProfile facts.produced.source.packet.segment ∧
      facts.produced.source.packet.ip.packet.ttl.toNat = 64 := by
  simpa only [facts.production, Produced.source, Produced.output, WireForwarding.Source.ofInput] using
    And.intro facts.header ⟨facts.sequence, facts.acknowledgment, facts.payload, facts.profile, facts.ttl⟩

theorem HeadTimeoutFacts.recovery_fields (facts : HeadTimeoutFacts before complete endpoints actor recovery head tail actual) :
    let next := Recovery.timeoutState recovery head tail
    next.outstanding = { head with lastAt := recovery.now, retried := true } :: tail ∧
      next.rto = 2 * recovery.rto ∧ next.deadline = some (recovery.now + 2 * recovery.rto) ∧
      next.now = recovery.now ∧ next.frontier = recovery.frontier ∧ next.nextId = recovery.nextId ∧
      next.estimator = recovery.estimator ∧ next.lastSample = recovery.lastSample ∧ next.duplicateAcks = 0 := by
  exact ⟨facts.outstanding, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPGapTimeout
