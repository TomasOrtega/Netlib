import Netlib.Check.CampusTCPGapProgressWire
import Netlib.Protocol.TCP.CheckpointCoverageFacts
import Netlib.Check.CampusTCPStartupBasisOrdinary

/-!
# Actual post-write cuts for two TCP records

The selected writer is already in the retained endpoint history.
Packet outputs and their origins are derived only after their actual sends.
-/

namespace Netlib.Check.CampusTCPTwoProgressStart

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut : Cut input complete} {actor : Actor} {bytes lower upper : List UInt8}

abbrev StartupBasis (cut : Cut input complete) := CampusTCPStartupBasis.Basis cut.report complete
abbrev Identity (seed current : Admission.Session) := CampusTCPGapProgressStart.Identity seed current

structure WrittenBatch (cut : Cut input complete) (actor : Actor) (bytes : List UInt8) where
  writer : T.Step
  prior : List T.Step
  later : List T.Step
  history : applicationSteps cut.endpoints actor = prior ++ writer :: later
  event : writer.event = .write bytes
  accepted : writer.result.decision = .accepted (.write bytes.length)
  emptyPending : writer.before.pending = []
  emptySent : writer.before.core.sent = []
  laterWritten : later.flatMap ApplicationTrace.Step.written = []
  laterEmitted : later.flatMap ApplicationTrace.Step.emitted = []

theorem WrittenBatch.writer_member (batch : WrittenBatch cut actor bytes) :
    batch.writer ∈ applicationSteps cut.endpoints actor := by
  rw [batch.history]
  simp

theorem WrittenBatch.joint (batch : WrittenBatch cut actor bytes) :
    ∃ actual ∈ cut.report.steps, actual.result.application = some (actor, batch.writer) := by
  apply CampusTCPRecoveryRoundOrigins.Report.application_origin cut.report actor batch.writer
  simpa only [cut.connection, CampusTCPRoundPhaseHistory.connectionSteps] using batch.writer_member

theorem WrittenBatch.before_chain (batch : WrittenBatch cut actor bytes) :
    ApplicationTrace.Chain (CampusTCPGapProgressStart.seed complete actor) batch.prior batch.writer.before := by
  have chain := CampusTCPGapProgressStart.endpoint_chain cut actor
  rw [batch.history] at chain
  exact chain.cut.1

theorem WrittenBatch.after_chain (batch : WrittenBatch cut actor bytes) :
    ApplicationTrace.Chain batch.writer.result.state batch.later (endpoint cut.endpoints actor) := by
  have chain := CampusTCPGapProgressStart.endpoint_chain cut actor
  rw [batch.history] at chain
  exact chain.cut.2

theorem WrittenBatch.writer_state (batch : WrittenBatch cut actor bytes) :
    batch.writer.result.state = Endpoint.writeState batch.writer.before bytes := by
  have selected : (Endpoint.write batch.writer.before bytes).decision = .accepted (.write bytes.length) := by
    simpa only [batch.writer.computed, batch.event, ApplicationTrace.evaluate] using batch.accepted
  have computed := (Endpoint.write_accepted _ _ selected).2.2
  rw [batch.writer.computed, batch.event]
  change (Endpoint.write batch.writer.before bytes).state = _
  rw [computed]

theorem WrittenBatch.pending (batch : WrittenBatch cut actor bytes) :
    (endpoint cut.endpoints actor).pending = bytes := by
  have balance := batch.after_chain.pending
  rw [batch.writer_state] at balance
  simpa only [Endpoint.writeState, batch.emptyPending, batch.laterWritten, batch.laterEmitted,
    List.nil_append, List.append_nil] using balance.symm

theorem WrittenBatch.coordinate (batch : WrittenBatch cut actor bytes) :
    ((applicationSteps cut.endpoints actor).flatMap ApplicationTrace.Step.emitted).length =
      (batch.prior.flatMap ApplicationTrace.Step.emitted).length := by
  have quiet : batch.writer.emitted = [] := by
    simp only [ApplicationTrace.Step.emitted, ApplicationTrace.emitted, batch.event]
  simp only [batch.history, List.flatMap_append, List.flatMap_cons, quiet, batch.laterEmitted,
    List.append_nil]

def WrittenBatch.ofLast (writer : T.Step) (prior : List T.Step)
    (history : applicationSteps cut.endpoints actor = prior ++ [writer])
    (event : writer.event = .write bytes)
    (accepted : writer.result.decision = .accepted (.write bytes.length))
    (emptyPending : writer.before.pending = []) (emptySent : writer.before.core.sent = []) :
    WrittenBatch cut actor bytes :=
  ⟨writer, prior, [], history, event, accepted, emptyPending, emptySent, rfl, rfl⟩

structure IdleEndpoint (state : Endpoint.State) where
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : state.recovery = some recovery
  ackRuntime : state.ackReaction = some reaction
  outstanding : recovery.outstanding = []
  sent : state.core.sent = []
  deadline : recovery.deadline = none
  timedOut : recovery.lastTimedOut = none
  timeoutCount : recovery.timeoutCount = 0
  duplicate : recovery.duplicateAcks = 0
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state

theorem IdleEndpoint.recovery_valid (idle : IdleEndpoint state) : idle.recovery.Valid := by
  have fields := idle.coherent
  rw [Endpoint.RecoveryCoherent, idle.runtime] at fields
  exact fields.1

theorem IdleEndpoint.smss (idle : IdleEndpoint state) : idle.recovery.smss = state.effectiveMSS := by
  have fields := idle.coherent
  rw [Endpoint.RecoveryCoherent, idle.runtime] at fields
  exact fields.2.1

theorem IdleEndpoint.flight (idle : IdleEndpoint state) : Recovery.flight idle.recovery = 0 := by
  simp only [Recovery.flight, idle.outstanding, List.map_nil, List.sum_nil]

theorem IdleEndpoint.clocked (idle : IdleEndpoint state) : idle.recovery.Clocked := by
  simp only [Recovery.State.Clocked, idle.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem IdleEndpoint.positive (idle : IdleEndpoint state) : idle.recovery.Positive := by
  simp only [Recovery.State.Positive, idle.outstanding, List.not_mem_nil, false_implies, implies_true]

theorem IdleEndpoint.cursor (idle : IdleEndpoint state) : state.core.sendUna = state.core.sendNext := by
  have cursor := idle.valid.1.2.2.2.2.1
  simpa only [idle.sent, List.length_nil, Seq.add_zero] using cursor

structure WrittenSender (cut : Cut input complete) (actor : Actor) (lower upper : List UInt8) where
  idle : IdleEndpoint (endpoint cut.endpoints actor)
  pending : (endpoint cut.endpoints actor).pending = lower ++ upper
  held : (endpoint cut.endpoints actor).receiveStore.held = []
  window : lower.length + upper.length ≤ (endpoint cut.endpoints actor).sendWindow
  mss : lower.length + upper.length ≤ (endpoint cut.endpoints actor).effectiveMSS

theorem WrittenSender.send_ready (sender : WrittenSender cut actor lower upper)
    (positive : 0 < count) (within : count ≤ lower.length + upper.length) :
    Endpoint.SendReady (endpoint cut.endpoints actor) count := by
  have valid := sender.idle.valid
  have recoveryValid := sender.idle.recovery_valid
  refine ⟨positive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sender.pending, List.length_append] using within
  · simpa only [sender.idle.sent, List.length_nil, Nat.zero_add] using Nat.le_trans within sender.window
  · have limit := valid.2.2.2.1
    have countBound := Nat.le_trans within sender.window
    simpa only [sender.idle.sent, List.length_nil, Nat.zero_add, EstablishedReceive.maxSendWindow] using Nat.le_trans countBound limit
  · exact Nat.le_trans within sender.mss
  · exact Nat.le_trans (Nat.add_le_add_left (Nat.le_trans within sender.mss) 40) valid.2.2.2.2.2.1
  · rw [Endpoint.recoveryReady, sender.idle.runtime]
    refine ⟨sender.idle.coherent, positive, ?_, ?_⟩
    · rw [sender.idle.flight, Nat.zero_add, sender.idle.smss]
      exact Nat.le_trans within sender.mss
    · rw [sender.idle.flight, Nat.zero_add, recoveryValid.2.2.1, sender.idle.smss]
      exact Nat.le_trans within sender.mss

structure EmptyReceiver (cut : Cut input complete) (actor : Actor) (bytes : List UInt8) where
  idle : IdleEndpoint (endpoint cut.endpoints actor)
  pending : (endpoint cut.endpoints actor).pending = []
  unread : (endpoint cut.endpoints actor).core.received = []
  held : (endpoint cut.endpoints actor).receiveStore.held = []
  space : bytes.length ≤ Endpoint.offeredWindow (endpoint cut.endpoints actor)

theorem EmptyReceiver.fits (receiver : EmptyReceiver cut actor bytes) :
    bytes.length ≤ (endpoint cut.endpoints actor).core.window :=
  Nat.le_trans receiver.space (Endpoint.offeredWindow_le _ receiver.idle.prepared.1)

structure GatewayStart (cut : Cut input complete) (basis : StartupBasis cut) (gateway : Gateway) where
  session : Admission.Session
  identity : Identity basis.session session
  phase : (beforeService input cut.report.final gateway).admission.phase = .data session
  trackerValid : (beforeService input cut.report.final gateway).tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ (beforeService input cut.report.final gateway).tracker.records
  entry : record.entry = session.entry
  confirmed : record.seenReply = true

theorem GatewayStart.coverage_sources (_start : GatewayStart cut basis gateway) :
    (beforeService input cut.report.final gateway).admission.CoverageSources :=
  (cut.report.final.resident gateway).history.coverage_sources

def GatewayStart.source (start : GatewayStart cut basis gateway) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (start.session.lane direction).coverage.runs) :
    Admission.CoverageSource (beforeService input cut.report.final gateway).admission.observations
      start.session.entry direction (start.session.lane direction) run :=
  (start.session.lane direction).coverageSource _ _ _
    (Admission.State.coverage_sources_lane _ start.coverage_sources start.session start.phase direction) run member

def GatewayStart.origin (start : GatewayStart cut basis gateway) (direction : Admission.Direction)
    (run : Admission.Coverage.Run Nat) (member : run ∈ (start.session.lane direction).coverage.runs) :
    Checkpoint.CoverageOrigin (cut.report.final.resident gateway).history start.session direction run :=
  (cut.report.final.resident gateway).history.coverageOrigin start.session start.phase direction run member

structure Geometry (start : GatewayStart cut basis gateway) (sender : Actor) (lower upper : List UInt8) where
  «prefix» : Nat
  acknowledged : (start.session.lane sender.direction).acknowledged = «prefix»
  observed : (start.session.lane sender.direction).observed = «prefix»
  highEnd : (start.session.lane sender.direction).highEnd = «prefix»
  senderCursor : (endpoint cut.endpoints sender).core.sendNext =
    (start.session.lane sender.direction).base.add «prefix»
  receiverCursor : (endpoint cut.endpoints sender.other).core.receiveNext =
    (endpoint cut.endpoints sender).core.sendNext
  senderAck : (endpoint cut.endpoints sender).core.receiveNext =
    (start.session.peer sender.direction).base.add (start.session.peer sender.direction).observed
  receiverSequence : (endpoint cut.endpoints sender.other).core.sendNext =
    (start.session.peer sender.direction).base.add (start.session.peer sender.direction).highEnd
  peerComplete : (start.session.peer sender.direction).observed = (start.session.peer sender.direction).highEnd
  window : lower.length + upper.length ≤ (start.session.lane sender.direction).peerWindow.val
  epoch : «prefix» + lower.length + upper.length + 2 < Seq.halfSpace

structure TwoWriteInitial (cut : Cut input complete) (sender : Actor) (gateway : Gateway)
    (lower upper : List UInt8) where
  basis : StartupBasis cut
  lowerNonempty : lower ≠ []
  upperNonempty : upper ≠ []
  write : WrittenBatch cut sender (lower ++ upper)
  senderState : WrittenSender cut sender lower upper
  receiverState : EmptyReceiver cut sender.other (lower ++ upper)
  gatewayState : GatewayStart cut basis gateway
  geometry : Geometry gatewayState sender lower upper

variable {sender : Actor} {gateway : Gateway} {initial : TwoWriteInitial cut sender gateway lower upper}

theorem TwoWriteInitial.entry_eq (initial : TwoWriteInitial cut sender gateway lower upper) :
    initial.gatewayState.session.entry = initial.basis.entry :=
  initial.gatewayState.identity.entry.trans initial.basis.aligned.entryEq

theorem TwoWriteInitial.input_tuple (initial : TwoWriteInitial cut sender gateway lower upper) (actor : Actor) :
    Output.reverse (endpoint cut.endpoints actor).core.inbound = initial.gatewayState.session.entry.flow.input actor.direction := by
  rw [CampusTCPGapProgressWire.endpoint_inbound cut actor, initial.entry_eq]
  cases actor
  · exact initial.basis.aligned.clientInput
  · exact initial.basis.aligned.serverInput

theorem TwoWriteInitial.output_tuple (initial : TwoWriteInitial cut sender gateway lower upper) (actor : Actor) :
    initial.gatewayState.session.entry.flow.output actor.direction = (endpoint cut.endpoints actor.other).core.inbound := by
  rw [CampusTCPGapProgressWire.endpoint_inbound cut actor.other, initial.entry_eq]
  cases actor
  · exact initial.basis.aligned.serverOutput.symm
  · exact initial.basis.aligned.clientOutput.symm

theorem TwoWriteInitial.endpoint_peer_mss (initial : TwoWriteInitial cut sender gateway lower upper) (actor : Actor) :
    (endpoint cut.endpoints actor).effectiveMSS ≤ (initial.gatewayState.session.peerMSS actor.direction).limit := by
  rw [CampusTCPGapProgressWire.endpoint_effectiveMSS cut actor]
  cases actor
  · change complete.certificate.activeSeed.effectiveMSS ≤ initial.gatewayState.session.serverMSS.limit
    rw [initial.gatewayState.identity.serverMSS, initial.basis.aligned.serverMSS,
      complete.certificate.directional_mss.2.2.1, complete.activeConfig, complete.passiveConfig]
    exact (Handshake.effectiveMSS_bounds _ _ (CampusTCPRoundStart.active_valid complete)).2.1
  · change complete.certificate.passiveSeed.effectiveMSS ≤ initial.gatewayState.session.clientMSS.limit
    rw [initial.gatewayState.identity.clientMSS, initial.basis.aligned.clientMSS,
      complete.certificate.directional_mss.2.2.2, complete.activeConfig, complete.passiveConfig]
    exact (Handshake.effectiveMSS_bounds _ _ (CampusTCPRoundStart.passive_valid complete)).2.1

structure NativeEnv (cut : Cut input complete) (gateway : Gateway) (entry : NetfilterNAT.Entry) where
  ingress : Actor → I.InterfaceRef
  paths : ∀ actor, CampusTCPRoundGateway.Native (input.contextFor gateway)
    (beforeService input cut.report.final gateway) (ingress actor) entry actor.direction actor.nextHop
  owners : ∀ actor, cut.report.final.owner actor = gateway
  configured : input.configured gateway = true
  unpaused : cut.report.final.assignmentPaused = false
  primary : gateway = .primary → cut.report.final.primarySealed = false ∧ cut.report.final.primaryFenced = false
  standby : gateway = .standby → ∃ installation : InstalledCheckpoint,
    cut.report.final.installation = some installation ∧
      cut.report.final.primarySealed = true ∧ cut.report.final.primaryFenced = true

theorem NativeEnv.route (env : NativeEnv cut gateway entry) (actor : Actor) : RouteReady cut.report.final actor := by
  refine ⟨env.unpaused, ?_, ?_, ?_⟩
  · rw [env.owners actor]
    exact env.configured
  · intro primary
    exact env.primary ((env.owners actor).symm.trans primary)
  · intro standby
    obtain ⟨installation, installed, _, _⟩ := env.standby ((env.owners actor).symm.trans standby)
    rw [installed]
    rfl

theorem NativeEnv.service_phase (env : NativeEnv cut gateway entry) :
    CampusTCPGatewayEnabled.ServicePhaseReady cut.report.final gateway := by
  refine ⟨env.primary, ?_⟩
  intro standby
  obtain ⟨installation, installed, _, _⟩ := env.standby standby
  exact ⟨env.unpaused, by rw [installed]; rfl⟩

end Netlib.Check.CampusTCPTwoProgressStart
