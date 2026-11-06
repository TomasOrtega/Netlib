import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPRecoveryRoundSender
import Netlib.Check.CampusTCPRoundMonitorFacts

namespace Netlib.Check.CampusTCPRecoveryRoundSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move ApplicationOutput OriginalFields)
open CampusTCPRecoveryRoundPhaseBase (At)

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Monitor.initial observe nextDemand)
end M
namespace F
export CampusTCPRoundMonitorFacts (observe_action observeOutput_eq output_pending)
end F
namespace Sender
export CampusTCPRecoveryRoundSender (Flight preparedClient first_send_enabled prepared_clock_ready)
end Sender

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

theorem At.monitor_clocks (placement : At anchor current) (config : CampusTCPRecoveryRoundMonitor.Config) :
    ∃ extra, current.report.steps = anchor.report.steps ++ extra ∧
      ∀ monitor, extra.foldl (M.observe config) monitor = monitor := by
  obtain ⟨extra, history, clocks⟩ := placement.clocks
  have fixed : ∀ actual ∈ extra, ∀ monitor, M.observe config monitor actual = monitor := by
    intro actual member monitor
    obtain ⟨actor, millis, event⟩ := clocks actual member
    have inside : actual ∈ current.report.steps := by rw [history]; exact List.mem_append.mpr (.inr member)
    have supported := List.all_eq_true.mp current.supported actual inside
    have passed := CampusTCPRoundLocal.step_local_passed actual actor (.advanceClock millis)
      (by rw [event]; exact .advanceClock _)
    simp only [CampusTCPRecoveryRoundMonitor.observe, supported, passed, Bool.and_self, ite_true, event]
  refine ⟨extra, history, ?_⟩
  intro monitor
  clear history clocks placement
  induction extra generalizing monitor with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, fixed head List.mem_cons_self monitor]
    exact ih (fun actual member => fixed actual (List.mem_cons_of_mem head member)) monitor

structure Sent (initial : Initial report complete request) (native : NativeEnv initial)
    (before : Cut input complete) (quantum : Nat) (actual : Step input) where
  move : Move before actual
  event : actual.event = .send .client request.bytes.length true
  application : ApplicationOutput before actual .client
  sendEvent : application.operation.event = .send request.bytes.length true
  accepted : application.operation.result.decision = .accepted (.send request.bytes.length)
  encoded : Endpoint.emit (endpoint before.endpoints .client) request.bytes = .ok application.packet
  fields : OriginalFields (complete := complete) (request := request) application.produced
  ttl : application.produced.source.packet.ip.packet.ttl.toNat = 64
  flight : Sender.Flight initial (endpoint before.endpoints .client).now
    (endpoint move.after.endpoints .client) 0
  receiver : Endpoint.ClockFrame (endpoint initial.start.next.endpoints .server)
    (endpoint move.after.endpoints .server)
  gateway : beforeService input move.after.report.final .primary = initial.beforeService
  environment : CampusTCPRoundEnvironment.environment initial.state =
    CampusTCPRoundEnvironment.environment move.after.report.final
  source : move.after.report.final.outputs[actual.before.outputs.length]? = some application.produced
  pending : IngressPending move.after.report.final actual.before.outputs.length
  minted : ∃ item ∈ move.after.report.final.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress actual.before.outputs.length application.produced
  packetID : Nat
  custody : move.after.report.final.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some packetID
  observed : M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) M.Monitor.initial actual =
    { round := { phase := .dataIngress, refs := {
      dataOutput := some actual.before.outputs.length, dataIngressPacket := some packetID } } }
  demand : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final
    (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) M.Monitor.initial actual) =
      some (.resolution (.assign actual.before.outputs.length native.dataIngress) packetID)
  anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial move.after

theorem send_at (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (placement : At (Cut.ofPrepared initial.start) current) (quantum : Nat) :
    ∃ actual : Step input, Nonempty (Sent initial native current quantum actual) := by
  let state := endpoint current.endpoints .client
  have clientFrame : Endpoint.ClockFrame (Sender.preparedClient initial) state := placement.frame.endpointFrame .client
  obtain ⟨_, _, prepared, _, ready, _⟩ := Sender.prepared_clock_ready initial state clientFrame
  obtain ⟨wire, sent, ⟨sendFlight⟩⟩ := Sender.first_send_enabled initial state clientFrame
  have earlier := (CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection).1
  obtain ⟨effect, produced, computed, supported, output, actor, payload, recorded⟩ := send_enabled
    current.report.final complete current.endpoints current.connection .client request.bytes.length earlier ready prepared
  let actual : Step input := ⟨_, _, effect, computed⟩
  let operation := ApplicationTrace.Step.make state (endpoint_valid current.endpoints .client)
    (.send request.bytes.length true) current.report.final.time
  have application : actual.result.application = some (.client, operation) := recorded
  have emitted : actual.result.output = some produced := output
  obtain ⟨appended⟩ := current.appendLocal actual rfl supported .client (.send request.bytes.length true)
    (.send request.bytes.length true) operation application
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual .client
    (.send request.bytes.length true) (.send request.bytes.length true)
  let move : Move current actual := ⟨appended.next, rfl, supported, passed, appended.history, appended.final⟩
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete
    current.endpoints current.connection .client (.send request.bytes.length true)
    (.send request.bytes.length true) operation application produced emitted
  have packetPayload : packet.packet.segment.payload = request.bytes := by
    have value := payload
    rw [production] at value
    have fixed : (endpoint current.endpoints .client).pending = (Sender.preparedClient initial).pending := clientFrame.pending
    rw [fixed, Sender.preparedClient, initial.start.client] at value
    simpa only [Produced.output,
      Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
      CampusTCPRoundSetup.recoveryState, complete.certificate.empty.1, List.nil_append, List.take_length] using value
  have noRetry : ApplicationTrace.NoRetry operation := by intro policy event; cases event
  obtain ⟨bytes, encodedBytes⟩ := CampusTCPRoundLocal.original_encoded origin noRetry
  have bytesEq : bytes = request.bytes :=
    (Endpoint.emit_payload _ _ _ encodedBytes).symm.trans packetPayload
  have encoded : Endpoint.emit state request.bytes = .ok packet := by
    simpa only [operation, ApplicationTrace.Step.make, bytesEq] using encodedBytes
  have transport := Endpoint.emit_transport _ _ _ encoded
  rw [clientFrame.core, Sender.preparedClient, initial.start.client] at transport
  have profile := CampusTCPRoundLocal.emit_profile _ _ _ encoded
  have sourcePacket : produced.source.packet = packet.packet := by rw [production]; rfl
  have fields : OriginalFields (complete := complete) (request := request) produced := by
    constructor
    · rw [sourcePacket]; exact transport.1
    · rw [sourcePacket]
      simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
        CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.1, complete.activeConfig] using transport.2.1
    · rw [sourcePacket]
      simpa only [Endpoint.writeState, CampusTCPRoundSetup.preparedSeed, CampusTCPRoundSetup.ackState,
        CampusTCPRoundSetup.recoveryState, complete.certificate.initial_sequences.2.2.1, complete.passiveConfig] using transport.2.2.1
    · rw [sourcePacket]; exact packetPayload
    · rw [sourcePacket]; exact profile.1
    · rw [sourcePacket]; exact profile.2.2.2
  have accepted : operation.result.decision = .accepted (.send request.bytes.length) := by
    change (Endpoint.send state request.bytes.length true).decision = _
    rw [sent]
  have flight : Sender.Flight initial state.now (endpoint move.after.endpoints .client) 0 := by
    rw [appended.selected]
    exact sendFlight
  have receiver : Endpoint.ClockFrame (endpoint initial.start.next.endpoints .server)
      (endpoint move.after.endpoints .server) := by
    have peer : endpoint move.after.endpoints .server = endpoint current.endpoints .server := appended.peer
    rw [peer]
    exact placement.frame.endpointFrame .server
  have source : move.after.report.final.outputs[actual.before.outputs.length]? = some produced := by
    rw [move.final, CampusTCPOrigins.output_history actual, emitted]
    simp
  obtain ⟨item, member, parent, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced emitted
  have pending : IngressPending move.after.report.final actual.before.outputs.length := by
    rw [move.final]
    exact ⟨item, member, by simp only [minted, Transit.ingressAt, beq_self_eq_true]⟩
  obtain ⟨id, pendingID⟩ := F.output_pending actual produced emitted
  have custody : move.after.report.final.custody.pendingID (Transit.ingressAt actual.before.outputs.length) = some id := by
    rw [move.final]
    exact pendingID
  have ordinary : CampusTCPRoundMonitor.observe (CampusTCPRoundPhaseBase.config initial native)
      CampusTCPRoundMonitor.Monitor.initial actual =
      { phase := .dataIngress, refs := { dataOutput := some actual.before.outputs.length, dataIngressPacket := some id } } := by
    rw [F.observe_action _ CampusTCPRoundMonitor.Monitor.initial actual (.send .client request.bytes.length true)
      supported passed rfl rfl]
    exact F.observeOutput_eq CampusTCPRoundMonitor.Monitor.initial actual .client .dataIngress produced emitted actor pendingID
  have actualSupported : actual.result.supported = true := supported
  have observed : M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) M.Monitor.initial actual =
      { round := { phase := .dataIngress, refs := {
        dataOutput := some actual.before.outputs.length, dataIngressPacket := some id } } } := by
    simp only [CampusTCPRecoveryRoundMonitor.observe, actualSupported, passed, Bool.and_self, ite_true,
      CampusTCPRecoveryRoundMonitor.Monitor.initial, CampusTCPRecoveryRoundMonitor.observeOrdinary,
      Bool.false_eq_true, ite_false, CampusTCPRecoveryRoundPhaseBase.config, ordinary]
    rfl
  have environment : CampusTCPRoundEnvironment.environment initial.state =
      CampusTCPRoundEnvironment.environment move.after.report.final :=
    placement.frame.environment.symm.trans (move.final ▸ CampusTCPRoundEnvironment.Step.environment actual trivial)
  have gateway : beforeService input move.after.report.final .primary = initial.beforeService := by
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice actual trivial]
    exact placement.frame.beforeService .primary
  have guards : CampusTCPRoundGuards.Guards move.after.endpoints := by
    intro receiverActor
    cases receiverActor
    · exact ⟨flight.coherent, flight.prepared, by rw [flight.runtime]; rfl⟩
    · apply CampusTCPRecoveryRoundPhaseBase.Guarded.clock
        (CampusTCPRoundGuards.PreparedStart.server_guards initial.start) receiver
      intro reaction stored
      rw [initial.start.server] at stored
      cases stored
      exact AckReaction.initial_within _ _ _ _
  refine ⟨actual, ⟨⟨move, rfl, ⟨operation, application, packet, origin, produced, emitted, production,
    appended.localBefore, rfl⟩, rfl, accepted, encoded, fields, ?_, flight, receiver, gateway, environment,
    source, pending, ?_, id, custody, observed, ?_,
    ⟨guards, placement.retained.trans move.retained, environment⟩⟩⟩⟩
  · rw [sourcePacket]
    exact CampusTCPRoundLocal.emit_ttl state request.bytes packet encoded
  · rw [move.final]
    exact ⟨item, member, parent, minted⟩
  · rw [observed]
    simp [CampusTCPRecoveryRoundMonitor.nextDemand, CampusTCPRoundMonitor.nextAction,
      CampusTCPRoundMonitor.ingressAction, CampusTCPRecoveryRoundMonitor.packetAt,
      source, custody, CampusTCPRecoveryRoundPhaseBase.config, CampusTCPRoundPhaseBase.config]

theorem Step.send (actual : Step input) (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (placement : At (Cut.ofPrepared initial.start) current) (quantum : Nat)
    (before : actual.before = current.report.final) (event : actual.event = .send .client request.bytes.length true) :
    Nonempty (Sent initial native current quantum actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := send_at initial native current placement quantum
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

end Netlib.Check.CampusTCPRecoveryRoundSend
