import Netlib.Check.CampusTCPRecoveredSetup
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Protocol.TCP.RecoveryEnabled

/-!
# Actual endpoint setup after recovery drain

Each operation extends the same report and both real endpoint histories.
The startup timer data comes from the retained drain archive.
-/

namespace Netlib.Check.CampusTCPRecoveredSetupAppend

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRecoveredSetup

variable {input : Input} {events : List Event}
variable {archive : RecoveryArchive input.active input.passive}
variable {report : Report input events} {ready : DrainReady report}

private def quietEvent : T.Event → Bool
  | .send .. | .receive .. => false
  | _ => true

private theorem before_append (prior : Cursor seed) (after : Cursor seed) (actual : T.Step)
    (history : after.steps = prior.steps ++ [actual])
    (ready : prior.beforeRecoveryTransport drained = true) (quiet : quietEvent actual.event = true) :
    after.beforeRecoveryTransport drained = true := by
  unfold Cursor.beforeRecoveryTransport
  rw [history, List.all_append]
  rw [Bool.and_eq_true]
  refine ⟨ready, ?_⟩
  cases event : actual.event <;> simp_all only [quietEvent, List.all_cons, List.all_nil, Bool.and_self, Bool.false_eq_true]

private theorem extend_before (prior after : Applications archive.complete) (actor : Actor) (actual : T.Step)
    (selected : applicationSteps after actor = applicationSteps prior actor ++ [actual])
    (other : applicationSteps after actor.other = applicationSteps prior actor.other)
    (client : prior.client.beforeRecoveryTransport archive.time = true)
    (server : prior.server.beforeRecoveryTransport archive.time = true)
    (quiet : quietEvent actual.event = true) :
    after.client.beforeRecoveryTransport archive.time = true ∧ after.server.beforeRecoveryTransport archive.time = true := by
  cases actor
  · have same : after.server.steps = prior.server.steps := other
    exact ⟨before_append prior.client after.client actual selected client quiet, by
      unfold Cursor.beforeRecoveryTransport at server ⊢
      rw [same]
      exact server⟩
  · have same : after.client.steps = prior.client.steps := other
    exact ⟨by
      unfold Cursor.beforeRecoveryTransport at client ⊢
      rw [same]
      exact client,
      before_append prior.server after.server actual selected server quiet⟩

structure QuietAppend (prior : Prefix input events archive) (actor : Actor)
    (event : T.Event) (joint : Event) (result : Endpoint.Result) where
  next : Prefix input (events ++ [joint]) archive
  actual : Step input
  eventEq : actual.event = joint
  before : actual.before = prior.report.final
  supported : actual.result.supported = true
  operation : T.Step
  recorded : actual.result.application = some (actor, operation)
  localBefore : operation.before = endpoint prior.endpoints actor
  localEvent : operation.event = event
  localStamp : operation.stamp = prior.report.final.time
  accepted : operation.result.decision = result.decision
  localState : operation.result.state = result.state
  last : next.report.steps = prior.report.steps ++ [actual]
  final : next.report.final = actual.result.state
  selected : endpoint next.endpoints actor = result.state
  peer : endpoint next.endpoints actor.other = endpoint prior.endpoints actor.other
  selectedSteps : applicationSteps next.endpoints actor = applicationSteps prior.endpoints actor ++ [operation]
  peerSteps : applicationSteps next.endpoints actor.other = applicationSteps prior.endpoints actor.other
  quiet : actual.result.output = none
  read : actual.result.read = result.read

private theorem QuietAppend.client_frame {prior : Prefix input events archive}
    (value : QuietAppend prior .server event joint result) :
    endpoint value.next.endpoints .client = endpoint prior.endpoints .client := value.peer

private theorem QuietAppend.server_frame {prior : Prefix input events archive}
    (value : QuietAppend prior .client event joint result) :
    endpoint value.next.endpoints .server = endpoint prior.endpoints .server := value.peer

private theorem QuietAppend.client_history {prior : Prefix input events archive}
    (value : QuietAppend prior .server event joint result) :
    applicationSteps value.next.endpoints .client = applicationSteps prior.endpoints .client := value.peerSteps

private theorem QuietAppend.server_history {prior : Prefix input events archive}
    (value : QuietAppend prior .client event joint result) :
    applicationSteps value.next.endpoints .server = applicationSteps prior.endpoints .server := value.peerSteps

private theorem append_quiet (prior : Prefix input events archive) (actor : Actor)
    (event : T.Event) (joint : Event) (result : Endpoint.Result) (action : Endpoint.Accepted)
    (evaluated : ApplicationTrace.evaluate (endpoint prior.endpoints actor) event = result)
    (quiet : result.output = none) (accepted : result.decision = .accepted action)
    (localEvent : quietEvent event = true)
    (core : processCore input prior.report.final joint = applyApplication input prior.report.final actor event)
    (custody : prepareCustody prior.report.final joint = .ok prior.report.final.custody) :
    Nonempty (QuietAppend prior actor event joint result) := by
  have bounds := CampusTCPChronology.Report.application_before prior.report archive.complete prior.endpoints prior.connection
  have earlier : ∀ old ∈ applicationSteps prior.endpoints actor, old.stamp < prior.report.final.time := by
    cases actor
    · exact bounds.1
    · exact bounds.2
  obtain ⟨effect, computed, supported, output, read, recorded⟩ := application_quiet
    prior.report.final archive.complete prior.endpoints prior.connection actor event earlier result action evaluated quiet accepted
  let actual : Step input := ⟨prior.report.final, joint,
    { effect with state := { effect.state with
      custody := finishCustody prior.report.final effect prior.report.final.custody,
      time := prior.report.final.time + 1 } }, by
        simp only [step, process, core, computed, custody, bind, Except.bind, pure, Except.pure]⟩
  let operation := ApplicationTrace.Step.make (endpoint prior.endpoints actor)
    (endpoint_valid prior.endpoints actor) event prior.report.final.time
  have actualSupported : actual.result.supported = true := supported
  obtain ⟨after, connected, selected, peer, history, other, before, eventEq, stamp⟩ :=
    application_frame prior.report.final archive.complete prior.endpoints prior.connection actor event effect operation computed recorded
  have beforeEvents := extend_before prior.endpoints after actor operation history other prior.clientBefore prior.serverBefore
    (by simpa only [eventEq] using localEvent)
  have archived : actual.result.state.recoveryArchive = some archive := by
    cases CampusTCPRecoveryStartupOrigins.Step.archive_change actual with
    | frame same => exact same.trans prior.archived
    | drain selected connection after retained =>
      rw [prior.connection] at connection
      cases connection
  let report := CampusTCPSchedule.Report.appendStep prior.report prior.supported prior.finished actual rfl actualSupported
  let next : Prefix input (events ++ [joint]) archive :=
    ⟨report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl,
      after, connected, archived, beforeEvents.1, beforeEvents.2⟩
  refine ⟨⟨next, actual, rfl, rfl, actualSupported, operation, recorded, before, eventEq, stamp,
    congrArg Endpoint.Result.decision evaluated, congrArg Endpoint.Result.state evaluated,
    rfl, rfl, ?_, peer, history, other, output, read⟩⟩
  exact selected.trans (congrArg Endpoint.Result.state evaluated)

def recoveryResult (state : Endpoint.State) (data : HandshakeTimer.Data) : Endpoint.Result :=
  ⟨Endpoint.startupRecoveryState state data, .accepted .enableRecovery, none, [], none⟩

def ackState (state : Endpoint.State) : Endpoint.State :=
  { state with ackReaction := some (AckReaction.initial state.core.receiveNext state.core.capacity state.localReceiveMSS.limit) }

def ackResult (state : Endpoint.State) : Endpoint.Result :=
  ⟨ackState state, .accepted .enableAck, none, [], none⟩

def writeResult (state : Endpoint.State) (bytes : List UInt8) : Endpoint.Result :=
  ⟨Endpoint.writeState state bytes, .accepted (.write bytes.length), none, [], none⟩

theorem append_recovery (prior : Prefix input events archive) (actor : Actor)
    (disabled : (endpoint prior.endpoints actor).recovery = none) (empty : (endpoint prior.endpoints actor).core.sent = []) :
    Nonempty (QuietAppend prior actor (.enableStartupRecovery (archive.data actor)) (.enableStartupRecovery actor)
      (recoveryResult (endpoint prior.endpoints actor) (archive.data actor))) := by
  apply append_quiet prior actor (.enableStartupRecovery (archive.data actor)) (.enableStartupRecovery actor) _ .enableRecovery
  · exact Endpoint.enableStartupRecovery_of_ready _ _ (endpoint_valid _ _) disabled empty (startup_data_floor archive actor)
  · rfl
  · rfl
  · rfl
  · simp only [processCore, CampusTCPModel.enableStartupRecovery, prior.archived]
  · rfl

theorem append_ack (prior : Prefix input events archive) (actor : Actor)
    (coherent : Endpoint.RecoveryCoherent (endpoint prior.endpoints actor))
    (disabled : (endpoint prior.endpoints actor).ackReaction = none)
    (recovery : (endpoint prior.endpoints actor).recovery.isSome = true)
    (received : (endpoint prior.endpoints actor).core.received = [])
    (sent : (endpoint prior.endpoints actor).core.sent = [])
    (initial : (endpoint prior.endpoints actor).receiveStore = ReceiveStore.initial) :
    Nonempty (QuietAppend prior actor .enableAck (.enableAck actor) (ackResult (endpoint prior.endpoints actor))) := by
  apply append_quiet prior actor .enableAck (.enableAck actor) _ .enableAck
  · exact (Endpoint.enableAck_success_prepared _ (endpoint_valid _ _) coherent disabled recovery received sent initial).1
  · rfl
  · rfl
  · rfl
  · cases actor
    · simp only [processCore, CampusTCPModel.enableAck, prior.connection, prior.archived, prior.clientBefore,
        Bool.or_true, ↓reduceIte]
    · simp only [processCore, CampusTCPModel.enableAck, prior.connection, prior.archived, prior.serverBefore,
        Bool.or_true, ↓reduceIte]
  · rfl

theorem append_write (prior : Prefix input events archive) (actor : Actor) (bytes : List UInt8)
    (fits : (endpoint prior.endpoints actor).pending.length + bytes.length ≤ (endpoint prior.endpoints actor).pendingLimit) :
    Nonempty (QuietAppend prior actor (.write bytes) (.write actor bytes) (writeResult (endpoint prior.endpoints actor) bytes)) := by
  apply append_quiet prior actor (.write bytes) (.write actor bytes) _ (.write bytes.length)
  · exact Endpoint.write_of_fits _ _ (endpoint_valid _ _) fits
  all_goals rfl


structure Prepared (start : Prefix input events archive) (bytes : List UInt8) where
  clientRecovery : QuietAppend start .client (.enableStartupRecovery archive.activeData) (.enableStartupRecovery .client)
    (recoveryResult (endpoint start.endpoints .client) archive.activeData)
  serverRecovery : QuietAppend clientRecovery.next .server (.enableStartupRecovery archive.passiveData) (.enableStartupRecovery .server)
    (recoveryResult (endpoint clientRecovery.next.endpoints .server) archive.passiveData)
  clientAck : QuietAppend serverRecovery.next .client .enableAck (.enableAck .client)
    (ackResult (endpoint serverRecovery.next.endpoints .client))
  serverAck : QuietAppend clientAck.next .server .enableAck (.enableAck .server)
    (ackResult (endpoint clientAck.next.endpoints .server))
  written : QuietAppend serverAck.next .client (.write bytes) (.write .client bytes)
    (writeResult (endpoint serverAck.next.endpoints .client) bytes)

variable {start : Prefix input events archive} {bytes : List UInt8}

def Prepared.next (value : Prepared start bytes) := value.written.next

def Prepared.joints (value : Prepared start bytes) : List (Step input) :=
  [value.clientRecovery.actual, value.serverRecovery.actual, value.clientAck.actual, value.serverAck.actual, value.written.actual]

theorem Prepared.history (value : Prepared start bytes) :
    value.next.report.steps = start.report.steps ++ value.joints := by
  rw [Prepared.next, value.written.last, value.serverAck.last, value.clientAck.last,
    value.serverRecovery.last, value.clientRecovery.last]
  simp only [Prepared.joints, List.append_assoc, List.cons_append, List.nil_append]

theorem Prepared.joint_events (value : Prepared start bytes) :
    value.joints.map (·.event) =
      [.enableStartupRecovery .client, .enableStartupRecovery .server, .enableAck .client, .enableAck .server, .write .client bytes] := by
  simp only [Prepared.joints, List.map_cons, List.map_nil, value.clientRecovery.eventEq, value.serverRecovery.eventEq,
    value.clientAck.eventEq, value.serverAck.eventEq, value.written.eventEq]

theorem Prepared.client_state (value : Prepared start bytes) :
    endpoint value.next.endpoints .client = Endpoint.writeState
      (ackState (Endpoint.startupRecoveryState (endpoint start.endpoints .client) archive.activeData)) bytes := by
  rw [Prepared.next, value.written.selected, value.serverAck.client_frame, value.clientAck.selected,
    value.serverRecovery.client_frame, value.clientRecovery.selected]
  rfl

theorem Prepared.server_state (value : Prepared start bytes) :
    endpoint value.next.endpoints .server =
      ackState (Endpoint.startupRecoveryState (endpoint start.endpoints .server) archive.passiveData) := by
  rw [Prepared.next, value.written.server_frame, value.serverAck.selected, value.clientAck.server_frame,
    value.serverRecovery.selected, value.clientRecovery.server_frame]
  rfl

theorem Prepared.client_steps (value : Prepared start bytes) :
    applicationSteps value.next.endpoints .client = applicationSteps start.endpoints .client ++
      [value.clientRecovery.operation, value.clientAck.operation, value.written.operation] := by
  rw [Prepared.next, value.written.selectedSteps, value.serverAck.client_history, value.clientAck.selectedSteps,
    value.serverRecovery.client_history, value.clientRecovery.selectedSteps]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem Prepared.server_steps (value : Prepared start bytes) :
    applicationSteps value.next.endpoints .server = applicationSteps start.endpoints .server ++
      [value.serverRecovery.operation, value.serverAck.operation] := by
  rw [Prepared.next, value.written.server_history, value.serverAck.selectedSteps, value.clientAck.server_history,
    value.serverRecovery.selectedSteps, value.clientRecovery.server_history]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem prepare (drained : Drained ready archive) (bytes : List UInt8)
    (fits : bytes.length ≤ archive.client.current.pendingLimit) : Nonempty (Prepared drained.next bytes) := by
  obtain ⟨clientDisabled, clientAck, clientStore, clientPending, clientSent, clientReceived, clientCore⟩ :=
    drained.next.archive_clean.1.fields
  obtain ⟨serverDisabled, serverAck, serverStore, serverPending, serverSent, serverReceived, serverCore⟩ :=
    drained.next.archive_clean.2.fields
  have clientStart : endpoint drained.next.endpoints .client = archive.client.current := drained.cursors.1
  have serverStart : endpoint drained.next.endpoints .server = archive.server.current := drained.cursors.2.1
  obtain ⟨clientRecovery⟩ := append_recovery drained.next .client
    (by rw [clientStart]; exact clientDisabled) (by rw [clientStart]; exact clientSent)
  have serverBefore : endpoint clientRecovery.next.endpoints .server = archive.server.current := clientRecovery.server_frame.trans serverStart
  obtain ⟨serverRecovery⟩ := append_recovery clientRecovery.next .server
    (by rw [serverBefore]; exact serverDisabled) (by rw [serverBefore]; exact serverSent)
  have clientAfter : endpoint serverRecovery.next.endpoints .client =
      Endpoint.startupRecoveryState archive.client.current archive.activeData := by
    rw [serverRecovery.client_frame, clientRecovery.selected, clientStart]
    rfl
  have clientCoherent : Endpoint.RecoveryCoherent (endpoint serverRecovery.next.endpoints .client) := by
    rw [clientAfter]
    exact Endpoint.startupRecoveryState_coherent _ _ archive.client.valid clientSent (startup_data_floor archive .client)
  obtain ⟨clientAcked⟩ := append_ack serverRecovery.next .client clientCoherent
    (by rw [clientAfter]; exact clientAck) (by rw [clientAfter]; rfl)
    (by rw [clientAfter]; exact clientReceived) (by rw [clientAfter]; exact clientSent)
    (by rw [clientAfter]; exact clientStore)
  have serverAfter : endpoint clientAcked.next.endpoints .server =
      Endpoint.startupRecoveryState archive.server.current archive.passiveData := by
    rw [clientAcked.server_frame, serverRecovery.selected, serverBefore]
    rfl
  have serverCoherent : Endpoint.RecoveryCoherent (endpoint clientAcked.next.endpoints .server) := by
    rw [serverAfter]
    exact Endpoint.startupRecoveryState_coherent _ _ archive.server.valid serverSent (startup_data_floor archive .server)
  obtain ⟨serverAcked⟩ := append_ack clientAcked.next .server serverCoherent
    (by rw [serverAfter]; exact serverAck) (by rw [serverAfter]; rfl)
    (by rw [serverAfter]; exact serverReceived) (by rw [serverAfter]; exact serverSent)
    (by rw [serverAfter]; exact serverStore)
  have clientPrepared : endpoint serverAcked.next.endpoints .client =
      ackState (Endpoint.startupRecoveryState archive.client.current archive.activeData) := by
    rw [serverAcked.client_frame, clientAcked.selected, clientAfter]
    rfl
  obtain ⟨written⟩ := append_write serverAcked.next .client bytes (by
    rw [clientPrepared]
    simpa only [ackState, Endpoint.startupRecoveryState, clientPending, List.length_nil, Nat.zero_add] using fits)
  exact ⟨⟨clientRecovery, serverRecovery, clientAcked, serverAcked, written⟩⟩


theorem Prepared.client_chain (value : Prepared start bytes) :
    T.Chain archive.complete.certificate.activeSeed
      (applicationSteps start.endpoints .client ++ [value.clientRecovery.operation, value.clientAck.operation, value.written.operation])
      (Endpoint.writeState (ackState (Endpoint.startupRecoveryState (endpoint start.endpoints .client) archive.activeData)) bytes) := by
  have chain := value.next.endpoints.client.chain
  change T.Chain _ (applicationSteps value.next.endpoints .client) (endpoint value.next.endpoints .client) at chain
  rw [value.client_steps, value.client_state] at chain
  exact chain

theorem Prepared.server_chain (value : Prepared start bytes) :
    T.Chain archive.complete.certificate.passiveSeed
      (applicationSteps start.endpoints .server ++ [value.serverRecovery.operation, value.serverAck.operation])
      (ackState (Endpoint.startupRecoveryState (endpoint start.endpoints .server) archive.passiveData)) := by
  have chain := value.next.endpoints.server.chain
  change T.Chain _ (applicationSteps value.next.endpoints .server) (endpoint value.next.endpoints .server) at chain
  rw [value.server_steps, value.server_state] at chain
  exact chain

theorem Prepared.runtime (value : Prepared start bytes) :
    (endpoint value.next.endpoints .client).recovery =
        some (Endpoint.startupRecovery (endpoint start.endpoints .client).effectiveMSS archive.activeData) ∧
      (endpoint value.next.endpoints .server).recovery =
        some (Endpoint.startupRecovery (endpoint start.endpoints .server).effectiveMSS archive.passiveData) := by
  rw [value.client_state, value.server_state]
  exact ⟨rfl, rfl⟩

theorem Prepared.timer_fields (value : Prepared start bytes) :
    (endpoint value.next.endpoints .client).recovery.map (·.now) = some archive.activeData.now ∧
      (endpoint value.next.endpoints .client).recovery.map (·.rto) = some archive.activeData.rto ∧
      (endpoint value.next.endpoints .client).recovery.map (·.estimator) = some archive.activeData.estimator ∧
      (endpoint value.next.endpoints .server).recovery.map (·.now) = some archive.passiveData.now ∧
      (endpoint value.next.endpoints .server).recovery.map (·.rto) = some archive.passiveData.rto ∧
      (endpoint value.next.endpoints .server).recovery.map (·.estimator) = some archive.passiveData.estimator := by
  rw [value.runtime.1, value.runtime.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Prepared.window_markers (value : Prepared start bytes) :
    (endpoint value.next.endpoints .client).sendWL1 = (endpoint start.endpoints .client).sendWL1 ∧
      (endpoint value.next.endpoints .client).sendWL2 = (endpoint start.endpoints .client).sendWL2 ∧
      (endpoint value.next.endpoints .server).sendWL1 = (endpoint start.endpoints .server).sendWL1 ∧
      (endpoint value.next.endpoints .server).sendWL2 = (endpoint start.endpoints .server).sendWL2 := by
  rw [value.client_state, value.server_state]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem prepared_geometry (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    (endpoint value.next.endpoints .client).core = archive.client.current.core ∧
      (endpoint value.next.endpoints .server).core = archive.server.current.core ∧
      (endpoint value.next.endpoints .client).pending = bytes ∧
      (endpoint value.next.endpoints .server).pending = [] ∧
      (endpoint value.next.endpoints .client).receiveStore = ReceiveStore.initial ∧
      (endpoint value.next.endpoints .server).receiveStore = ReceiveStore.initial := by
  have client := drained.next.archive_clean.1.fields
  have server := drained.next.archive_clean.2.fields
  have clientStart : endpoint drained.next.endpoints .client = archive.client.current := drained.cursors.1
  have serverStart : endpoint drained.next.endpoints .server = archive.server.current := drained.cursors.2.1
  rw [value.client_state, value.server_state, clientStart, serverStart]
  exact ⟨rfl, rfl, by simp only [Endpoint.writeState, ackState, Endpoint.startupRecoveryState, client.2.2.2.1, List.nil_append],
    server.2.2.2.1, client.2.2.1, server.2.2.1⟩

private theorem startup_guards (state : Endpoint.State) (data : HandshakeTimer.Data) (valid : state.Valid)
    (minimum : 1000 ≤ data.rto) (disabled : state.ackReaction = none) (sent : state.core.sent = [])
    (received : state.core.received = []) (store : state.receiveStore = ReceiveStore.initial) :
    Endpoint.RecoveryCoherent (ackState (Endpoint.startupRecoveryState state data)) ∧
      Endpoint.AckPrepared (ackState (Endpoint.startupRecoveryState state data)) ∧
      Endpoint.StorageCoherent (ackState (Endpoint.startupRecoveryState state data)) := by
  have coherent := Endpoint.startupRecoveryState_coherent state data valid sent minimum
  refine ⟨coherent, (Endpoint.enableAck_success_prepared (Endpoint.startupRecoveryState state data) valid coherent disabled rfl received sent store).2, ?_⟩
  have window : state.core.window = state.core.capacity := by
    simp only [EstablishedReceive.State.window, received, List.length_nil, Nat.sub_zero]
  have initial := ReceiveStore.initial_valid (Meta := ReceiveReassembly.Receipt)
    state.core.capacity state.core.capacity (Nat.le_refl _)
  constructor
  · exact Endpoint.storage_valid_of_empty _ (by simp only [ackState, Endpoint.startupRecoveryState, store, ReceiveStore.initial])
  · constructor
    · simp only [ackState, Endpoint.startupRecoveryState, AckReaction.initial,
        ReceiveAdvertisement.initial, store, ReceiveStore.initial]
    · change state.receiveStore.Valid (state.receiveStore.frontier + state.core.capacity) state.core.window
      rw [store, window]
      simpa only [ReceiveStore.initial, Nat.zero_add] using initial

theorem prepared_guards (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    ∀ actor, Endpoint.RecoveryCoherent (endpoint value.next.endpoints actor) ∧
      Endpoint.AckPrepared (endpoint value.next.endpoints actor) ∧ Endpoint.StorageCoherent (endpoint value.next.endpoints actor) := by
  have client := drained.next.archive_clean.1.fields
  have server := drained.next.archive_clean.2.fields
  have clientReady := startup_guards archive.client.current archive.activeData archive.client.valid
    (startup_data_floor archive .client) client.2.1 client.2.2.2.2.1 client.2.2.2.2.2.1 client.2.2.1
  have serverReady := startup_guards archive.server.current archive.passiveData archive.server.valid
    (startup_data_floor archive .server) server.2.1 server.2.2.2.2.1 server.2.2.2.2.2.1 server.2.2.1
  have clientStart : endpoint drained.next.endpoints .client = archive.client.current := drained.cursors.1
  have serverStart : endpoint drained.next.endpoints .server = archive.server.current := drained.cursors.2.1
  intro actor
  cases actor
  · rw [value.client_state, clientStart]
    exact ⟨clientReady.1, Endpoint.writeState_ackPrepared _ bytes clientReady.2.1, clientReady.2.2⟩
  · rw [value.server_state, serverStart]
    exact serverReady


private theorem service_frame (actual : Step input) (selected : CampusTCPRoundEnvironment.Nonservice actual.event)
    (gateway : Gateway) : beforeService input actual.result.state gateway = beforeService input actual.before gateway := by
  have transport : CampusTCPRoundEnvironment.TransportOnly actual.event := by
    cases event : actual.event <;> simp_all only [CampusTCPRoundEnvironment.Nonservice, CampusTCPRoundEnvironment.TransportOnly]
  have fixed := CampusTCPRoundEnvironment.Step.environment actual transport
  have authentication := congrArg CampusTCPRoundEnvironment.Environment.authentication fixed
  change actual.before.authentication = actual.result.state.authentication at authentication
  simp only [beforeService, CampusTCPRoundEnvironment.Step.resident_nonservice actual selected gateway, ← authentication]

private theorem QuietAppend.gateway {prior : Prefix input events archive}
    (value : QuietAppend prior actor event joint result) (selected : CampusTCPRoundEnvironment.Nonservice joint)
    (gateway : Gateway) : beforeService input value.next.report.final gateway = beforeService input prior.report.final gateway := by
  rw [value.final, ← value.before]
  exact service_frame value.actual (by rw [value.eventEq]; exact selected) gateway

theorem Prepared.gateway_frame (value : Prepared start bytes) (gateway : Gateway) :
    beforeService input value.next.report.final gateway = beforeService input start.report.final gateway :=
  (value.written.gateway trivial gateway).trans ((value.serverAck.gateway trivial gateway).trans
    ((value.clientAck.gateway trivial gateway).trans ((value.serverRecovery.gateway trivial gateway).trans
      (value.clientRecovery.gateway trivial gateway))))

theorem Drained.gateway_frame (drained : Drained ready archive) (gateway : Gateway) :
    beforeService input drained.next.report.final gateway = beforeService input report.final gateway := by
  rw [drained.final, ← drained.before]
  exact service_frame drained.actual (by rw [drained.event]; trivial) gateway

theorem Drained.pendingLimit (drained : Drained ready archive) :
    archive.client.current.pendingLimit = ready.client.current.pendingLimit := by
  have same := archive.phase.symm.trans ((congrArg TCPHandshakeRecovery.State.phase drained.current).trans ready.phase)
  have limit := congrArg (fun phase => match phase with
    | .complete _ client _ => client.current.pendingLimit
    | _ => 0) same
  exact limit

theorem setup (ready : DrainReady report) (bytes : List UInt8)
    (fits : bytes.length ≤ ready.client.current.pendingLimit) :
    ∃ archive, ∃ drained : Drained ready archive, Nonempty (Prepared drained.next bytes) := by
  obtain ⟨archive, ⟨drained⟩⟩ := drain ready
  exact ⟨archive, drained, prepare drained bytes (by rw [Drained.pendingLimit drained]; exact fits)⟩

end Netlib.Check.CampusTCPRecoveredSetupAppend
