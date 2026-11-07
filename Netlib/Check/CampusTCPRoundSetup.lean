import Netlib.Check.CampusTCPEnabled
import Netlib.Check.CampusTCPChronology
import Netlib.Check.CampusTCPSchedule
import Netlib.Protocol.TCP.RecoveryEnabled

/-!
# Actual setup for a campus TCP round

Setup appends endpoint operations to the same checked report.
The endpoint states come from the completed startup exchange.
-/

namespace Netlib.Check.CampusTCPRoundSetup

open CampusTCPModel CampusTCPEnabled
namespace E
export Netlib.Protocol.TCP.Endpoint (State Result Accepted)
end E
open Protocol.TCP

variable {input : Input}
variable {events : List Event} {complete : H.Completed input.active input.passive}
variable {bytes : List UInt8} {report : Report input events}

structure Prefix (input : Input) (events : List Event)
    (complete : H.Completed input.active input.passive) where
  report : Report input events
  supported : report.supported = true
  finished : report.remaining = []
  endpoints : Applications complete
  connection : report.final.connection = .application complete endpoints
  clientBefore : endpoints.client.beforeTransport = true
  serverBefore : endpoints.server.beforeTransport = true

def Prefix.ofStartup (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (complete : H.Completed input.active input.passive)
    (connection : report.final.connection = .application complete (Applications.initial complete)) :
    Prefix input events complete :=
  ⟨report, supported, finished, Applications.initial complete, connection, rfl, rfl⟩

theorem cursor_initial (cursor : Cursor seed) (valid : seed.Valid) (empty : cursor.steps = []) :
    cursor = Cursor.initial seed valid := by
  cases cursor with
  | mk current valid steps chain ordered =>
    dsimp only at empty
    subst steps
    cases chain
    rfl

theorem applications_initial (endpoints : Applications complete)
    (client : endpoints.client.steps = []) (server : endpoints.server.steps = []) :
    endpoints = Applications.initial complete := by
  have first := cursor_initial endpoints.client complete.certificate.valid.1 client
  have second := cursor_initial endpoints.server complete.certificate.valid.2 server
  cases endpoints
  simp_all only [Applications.initial]

private def beforeTransportEvent : T.Event → Bool
  | .send .. | .receive .. => false
  | _ => true

private theorem extend_before (endpoints : Applications complete) (after : Applications complete)
    (actor : Actor) (actual : T.Step)
    (selected : applicationSteps after actor = applicationSteps endpoints actor ++ [actual])
    (other : applicationSteps after actor.other = applicationSteps endpoints actor.other)
    (oldClient : endpoints.client.beforeTransport = true) (oldServer : endpoints.server.beforeTransport = true)
    (quiet : beforeTransportEvent actual.event = true) :
    after.client.beforeTransport = true ∧ after.server.beforeTransport = true := by
  have old : ∀ receiver, (applicationSteps endpoints receiver).all (fun step => beforeTransportEvent step.event) = true := by
    intro receiver
    cases receiver
    · exact oldClient
    · exact oldServer
  have next : ∀ receiver, (applicationSteps after receiver).all (fun step => beforeTransportEvent step.event) = true := by
    intro receiver
    by_cases same : receiver = actor
    · subst receiver
      rw [selected, List.all_append]
      simp only [old actor, List.all_cons, quiet, List.all_nil, Bool.and_self]
    · have opposite : receiver = actor.other := by cases actor <;> cases receiver <;> simp_all [Actor.other]
      rw [opposite, other]
      exact old _
  exact ⟨next .client, next .server⟩

structure QuietAppend (prior : Prefix input events complete) (actor : Actor)
    (event : T.Event) (joint : Event) (result : E.Result) where
  next : Prefix input (events ++ [joint]) complete
  actual : Step input
  eventEq : actual.event = joint
  before : actual.before = prior.report.final
  supported : actual.result.supported = true
  recorded : actual.result.application = some (actor,
    ApplicationTrace.Step.make (endpoint prior.endpoints actor)
      (endpoint_valid prior.endpoints actor) event prior.report.final.time)
  last : next.report.steps = prior.report.steps ++ [actual]
  final : next.report.final = actual.result.state
  selected : endpoint next.endpoints actor = result.state
  peer : endpoint next.endpoints actor.other = endpoint prior.endpoints actor.other

private theorem append_quiet (prior : Prefix input events complete) (actor : Actor)
    (event : T.Event) (joint : Event) (result : E.Result) (action : E.Accepted)
    (evaluated : ApplicationTrace.evaluate (endpoint prior.endpoints actor) event = result)
    (quiet : result.output = none) (accepted : result.decision = .accepted action)
    (localEvent : beforeTransportEvent event = true)
    (core : processCore input prior.report.final joint =
      applyApplication input prior.report.final actor event)
    (custody : prepareCustody prior.report.final joint = .ok prior.report.final.custody) :
    Nonempty (QuietAppend prior actor event joint result) := by
  have bounds := CampusTCPChronology.Report.application_before prior.report complete prior.endpoints prior.connection
  have earlier : ∀ old ∈ applicationSteps prior.endpoints actor, old.stamp < prior.report.final.time := by
    cases actor
    · exact bounds.1
    · exact bounds.2
  obtain ⟨effect, computed, supported, output, _, recorded⟩ := application_quiet
    prior.report.final complete prior.endpoints prior.connection actor event earlier result action evaluated quiet accepted
  let actual : Step input := ⟨prior.report.final, joint,
    { effect with state := { effect.state with
      custody := finishCustody prior.report.final effect prior.report.final.custody,
      time := prior.report.final.time + 1 } }, by
        simp only [step, process, core, computed, custody, bind, Except.bind, pure, Except.pure]⟩
  let app := ApplicationTrace.Step.make (endpoint prior.endpoints actor)
    (endpoint_valid prior.endpoints actor) event prior.report.final.time
  have actualSupported : actual.result.supported = true := supported
  obtain ⟨after, connection, selected, peer, history, other, _, eventEq, _⟩ :=
    application_frame prior.report.final complete prior.endpoints prior.connection actor event effect app computed recorded
  have beforeEvents : after.client.beforeTransport = true ∧ after.server.beforeTransport = true :=
    extend_before prior.endpoints after actor app history other prior.clientBefore prior.serverBefore
      (by simpa only [eventEq] using localEvent)
  let report := CampusTCPSchedule.Report.appendStep prior.report prior.supported prior.finished
    actual rfl actualSupported
  let next : Prefix input (events ++ [joint]) complete :=
    ⟨report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl,
      after, connection, beforeEvents.1, beforeEvents.2⟩
  refine ⟨⟨next, actual, rfl, rfl, actualSupported, recorded, rfl, rfl, ?_, peer⟩⟩
  exact selected.trans (congrArg Endpoint.Result.state evaluated)

def recoveryState (seed : E.State) : E.State :=
  { seed with recovery := some (Recovery.initial seed.effectiveMSS), lastAckWindow := some seed.sendWindow }

def ackState (seed : E.State) : E.State :=
  { seed with ackReaction := some (AckReaction.initial seed.core.receiveNext
    seed.core.capacity seed.localReceiveMSS.limit) }

private theorem enable_recovery (seed : E.State) (valid : seed.Valid)
    (disabled : seed.recovery = none) (empty : seed.core.sent = []) :
    Endpoint.enableRecovery seed = ⟨recoveryState seed, .accepted .enableRecovery, none, [], none⟩ := by
  simp only [Endpoint.enableRecovery, valid, not_true_eq_false, ite_false, disabled,
    Option.isSome_none, empty, List.isEmpty_nil, Bool.not_true, Bool.or_self, Bool.false_eq_true,
    recoveryState]

private theorem recovery_coherent (seed : E.State) (valid : seed.Valid) (empty : seed.core.sent = []) :
    Endpoint.RecoveryCoherent (recoveryState seed) := by
  have initial := Recovery.initial_valid seed.effectiveMSS valid.2.2.2.2.1
  refine ⟨initial, rfl, ?_, ?_⟩
  · simp only [recoveryState, Recovery.flight, Recovery.initial, empty, List.map_nil, List.sum_nil, List.length_nil]
  · exact valid.2.2.2.1

private theorem seed_recovery (complete : H.Completed input.active input.passive) :
    complete.certificate.activeSeed.recovery = none ∧ complete.certificate.passiveSeed.recovery = none := by
  simp only [HandshakeExchange.Complete.activeSeed, HandshakeExchange.Complete.passiveSeed,
    complete.certificate.active.derived, complete.certificate.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, and_self]

private theorem seed_ack (complete : H.Completed input.active input.passive) :
    complete.certificate.activeSeed.ackReaction = none ∧ complete.certificate.passiveSeed.ackReaction = none := by
  simp only [HandshakeExchange.Complete.activeSeed, HandshakeExchange.Complete.passiveSeed,
    complete.certificate.active.derived, complete.certificate.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, and_self]

private theorem append_recovery (prior : Prefix input events complete) (actor : Actor)
    (disabled : (endpoint prior.endpoints actor).recovery = none)
    (empty : (endpoint prior.endpoints actor).core.sent = []) :
    Nonempty (QuietAppend prior actor .enableRecovery (.enableRecovery actor)
      ⟨recoveryState (endpoint prior.endpoints actor), .accepted .enableRecovery, none, [], none⟩) := by
  apply append_quiet prior actor .enableRecovery (.enableRecovery actor) _ .enableRecovery
  · exact enable_recovery _ (endpoint_valid _ _) disabled empty
  all_goals rfl

private theorem append_ack (prior : Prefix input events complete) (actor : Actor)
    (coherent : Endpoint.RecoveryCoherent (endpoint prior.endpoints actor))
    (disabled : (endpoint prior.endpoints actor).ackReaction = none)
    (recovery : (endpoint prior.endpoints actor).recovery.isSome = true)
    (received : (endpoint prior.endpoints actor).core.received = [])
    (sent : (endpoint prior.endpoints actor).core.sent = [])
    (initial : (endpoint prior.endpoints actor).receiveStore = ReceiveStore.initial) :
    Nonempty (QuietAppend prior actor .enableAck (.enableAck actor)
      ⟨ackState (endpoint prior.endpoints actor), .accepted .enableAck, none, [], none⟩) := by
  apply append_quiet prior actor .enableAck (.enableAck actor) _ .enableAck
  · exact (Endpoint.enableAck_success_prepared _ (endpoint_valid _ _) coherent disabled recovery received sent initial).1
  · rfl
  · rfl
  · rfl
  · cases actor
    · simp only [processCore, CampusTCPModel.enableAck, prior.connection, prior.clientBefore,
        Bool.or_true, Bool.true_or, ↓reduceIte]
    · simp only [processCore, CampusTCPModel.enableAck, prior.connection, prior.serverBefore,
        Bool.or_true, Bool.true_or, ↓reduceIte]
  · rfl

private theorem append_write (prior : Prefix input events complete) (bytes : List UInt8)
    (fits : (endpoint prior.endpoints .client).pending.length + bytes.length ≤
      (endpoint prior.endpoints .client).pendingLimit) :
    Nonempty (QuietAppend prior .client (.write bytes) (.write .client bytes)
      ⟨Endpoint.writeState (endpoint prior.endpoints .client) bytes,
        .accepted (.write bytes.length), none, [], none⟩) := by
  apply append_quiet prior .client (.write bytes) (.write .client bytes) _ (.write bytes.length)
  · exact Endpoint.write_of_fits _ _ (endpoint_valid _ _) fits
  all_goals rfl

def preparedSeed (seed : E.State) : E.State := ackState (recoveryState seed)

def setupEvents (bytes : List UInt8) : List Event :=
  [.enableRecovery .client, .enableRecovery .server, .enableAck .client, .enableAck .server, .write .client bytes]

def withSetup (events : List Event) (bytes : List UInt8) : List Event :=
  ((((events ++ [.enableRecovery .client]) ++ [.enableRecovery .server]) ++
    [.enableAck .client]) ++ [.enableAck .server]) ++ [.write .client bytes]

theorem withSetup_eq (events : List Event) (bytes : List UInt8) :
    withSetup events bytes = events ++ setupEvents bytes := by simp [withSetup, setupEvents, List.append_assoc]

structure PreparedStart (report : Report input events) (complete : H.Completed input.active input.passive)
    (bytes : List UInt8) where
  next : Prefix input (withSetup events bytes) complete
  retained : report.steps <+: next.report.steps
  setupSteps : List (Step input)
  evaluated : next.report.steps = report.steps ++ setupSteps
  suffix : Trace input report.final (setupEvents bytes) setupSteps next.report.final []
  client : endpoint next.endpoints .client = Endpoint.writeState (preparedSeed complete.certificate.activeSeed) bytes
  server : endpoint next.endpoints .server = preparedSeed complete.certificate.passiveSeed
  writeStep : Step input
  writeMember : writeStep ∈ next.report.steps
  writeEvent : writeStep.event = .write .client bytes
  actualWrite : T.Step
  recordedWrite : writeStep.result.application = some (.client, actualWrite)
  localWrite : actualWrite.event = .write bytes
  writtenFrom : actualWrite.before = preparedSeed complete.certificate.activeSeed

theorem prepare (report : Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (complete : H.Completed input.active input.passive)
    (connection : report.final.connection = .application complete (Applications.initial complete))
    (bytes : List UInt8) (fits : bytes.length ≤ input.active.pendingLimit) :
    Nonempty (PreparedStart report complete bytes) := by
  let prior := Prefix.ofStartup report supported finished complete connection
  let client := complete.certificate.activeSeed
  let server := complete.certificate.passiveSeed
  have clientValid : client.Valid := complete.certificate.valid.1
  have serverValid : server.Valid := complete.certificate.valid.2
  have clientEmpty : client.core.sent = [] := complete.certificate.empty.2.1
  have serverEmpty : server.core.sent = [] := complete.certificate.empty.2.2.2.2.1
  obtain ⟨r1⟩ := append_recovery prior .client (seed_recovery complete).1 clientEmpty
  have r1Client : endpoint r1.next.endpoints .client = recoveryState client := r1.selected
  have r1Server : endpoint r1.next.endpoints .server = server := r1.peer
  obtain ⟨r2⟩ := append_recovery r1.next .server
    (by rw [r1Server]; exact (seed_recovery complete).2) (by rw [r1Server]; exact serverEmpty)
  have r2Client : endpoint r2.next.endpoints .client = recoveryState client := r2.peer.trans r1Client
  have r2Server : endpoint r2.next.endpoints .server = recoveryState server := by
    simpa only [r1Server] using r2.selected
  obtain ⟨r3⟩ := append_ack r2.next .client
    (by rw [r2Client]; exact recovery_coherent client clientValid clientEmpty)
    (by rw [r2Client]; exact (seed_ack complete).1)
    (by rw [r2Client]; rfl)
    (by rw [r2Client]; exact complete.certificate.empty.2.2.1)
    (by rw [r2Client]; exact clientEmpty)
    (by rw [r2Client]; exact complete.certificate.receiveStore_initial.1)
  have r3Client : endpoint r3.next.endpoints .client = preparedSeed client := by
    simpa only [r2Client, preparedSeed] using r3.selected
  have r3Server : endpoint r3.next.endpoints .server = recoveryState server := r3.peer.trans r2Server
  obtain ⟨r4⟩ := append_ack r3.next .server
    (by rw [r3Server]; exact recovery_coherent server serverValid serverEmpty)
    (by rw [r3Server]; exact (seed_ack complete).2)
    (by rw [r3Server]; rfl)
    (by rw [r3Server]; exact complete.certificate.empty.2.2.2.2.2)
    (by rw [r3Server]; exact serverEmpty)
    (by rw [r3Server]; exact complete.certificate.receiveStore_initial.2)
  have r4Client : endpoint r4.next.endpoints .client = preparedSeed client := r4.peer.trans r3Client
  have r4Server : endpoint r4.next.endpoints .server = preparedSeed server := by
    simpa only [r3Server, preparedSeed] using r4.selected
  have writeFits : (endpoint r4.next.endpoints .client).pending.length + bytes.length ≤
      (endpoint r4.next.endpoints .client).pendingLimit := by
    rw [r4Client]
    simpa only [preparedSeed, ackState, recoveryState, client, complete.certificate.empty.1,
      List.length_nil, Nat.zero_add, complete.certificate.configuration.2.1, complete.activeConfig] using fits
  obtain ⟨r5⟩ := append_write r4.next bytes writeFits
  have t5 : Trace input r4.next.report.final [.write .client bytes] [r5.actual] r5.next.report.final [] := by
    simpa only [r5.before, r5.eventEq, ← r5.final] using
      Trace.next r5.actual r5.supported (.done r5.actual.result.state)
  have t4 : Trace input r3.next.report.final [.enableAck .server, .write .client bytes]
      [r4.actual, r5.actual] r5.next.report.final [] := by
    have tail := r4.final ▸ t5
    simpa only [r4.before, r4.eventEq] using Trace.next r4.actual r4.supported tail
  have t3 : Trace input r2.next.report.final [.enableAck .client, .enableAck .server, .write .client bytes]
      [r3.actual, r4.actual, r5.actual] r5.next.report.final [] := by
    have tail := r3.final ▸ t4
    simpa only [r3.before, r3.eventEq] using Trace.next r3.actual r3.supported tail
  have t2 : Trace input r1.next.report.final [.enableRecovery .server, .enableAck .client,
      .enableAck .server, .write .client bytes]
      [r2.actual, r3.actual, r4.actual, r5.actual] r5.next.report.final [] := by
    have tail := r2.final ▸ t3
    simpa only [r2.before, r2.eventEq] using Trace.next r2.actual r2.supported tail
  have t1 : Trace input report.final (setupEvents bytes)
      [r1.actual, r2.actual, r3.actual, r4.actual, r5.actual] r5.next.report.final [] := by
    change Trace input prior.report.final _ _ _ _
    have tail := r1.final ▸ t2
    simpa only [setupEvents, r1.before, r1.eventEq] using Trace.next r1.actual r1.supported tail
  refine ⟨⟨r5.next, ?_, _, ?_, t1, ?_, r5.peer.trans r4Server, r5.actual, ?_, r5.eventEq,
    ApplicationTrace.Step.make (endpoint r4.next.endpoints .client) (endpoint_valid _ _) (.write bytes)
      r4.next.report.final.time, r5.recorded, rfl, r4Client⟩⟩
  · rw [r5.last, r4.last, r3.last, r2.last, r1.last]
    simp only [List.append_assoc]
    exact List.prefix_append _ _
  · rw [r5.last, r4.last, r3.last, r2.last, r1.last]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  · simpa only [r4Client] using r5.selected
  · rw [r5.last]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem prepared_ack (seed : E.State) (valid : seed.Valid)
    (disabled : seed.ackReaction = none) (received : seed.core.received = [])
    (sent : seed.core.sent = []) (store : seed.receiveStore = ReceiveStore.initial) :
    Endpoint.AckPrepared (preparedSeed seed) :=
  (Endpoint.enableAck_success_prepared (recoveryState seed) valid (recovery_coherent seed valid sent)
    disabled rfl received sent store).2

theorem PreparedStart.client_ack (start : PreparedStart report complete bytes) :
    Endpoint.AckPrepared (endpoint start.next.endpoints .client) := by
  rw [start.client]
  apply Endpoint.writeState_ackPrepared
  exact prepared_ack _ complete.certificate.valid.1 (seed_ack complete).1
    complete.certificate.empty.2.2.1 complete.certificate.empty.2.1
    complete.certificate.receiveStore_initial.1

theorem PreparedStart.server_ack (start : PreparedStart report complete bytes) :
    Endpoint.AckPrepared (endpoint start.next.endpoints .server) := by
  rw [start.server]
  exact prepared_ack _ complete.certificate.valid.2 (seed_ack complete).2
    complete.certificate.empty.2.2.2.2.2 complete.certificate.empty.2.2.2.2.1
    complete.certificate.receiveStore_initial.2

theorem PreparedStart.send_ready (start : PreparedStart report complete bytes)
    (nonempty : bytes ≠ [])
    (mss : bytes.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive))
    (window : bytes.length ≤ input.passive.capacity) :
    Endpoint.SendReady (endpoint start.next.endpoints .client) bytes.length := by
  rw [start.client]
  let seed := complete.certificate.activeSeed
  have valid : seed.Valid := complete.certificate.valid.1
  have empty : seed.core.sent = [] := complete.certificate.empty.2.1
  have pending : seed.pending = [] := complete.certificate.empty.1
  have size : bytes.length ≤ seed.effectiveMSS := by
    simpa only [seed, complete.certificate.directional_mss.2.2.1, complete.activeConfig, complete.passiveConfig] using mss
  have peer : seed.sendWindow = input.passive.capacity := by
    simpa only [seed, complete.passiveConfig] using complete.certificate.peer_capacities.1
  have positive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  have limit : 40 + seed.effectiveMSS ≤ seed.ipSendLimit := valid.2.2.2.2.2.1
  have peerBound : seed.sendWindow ≤ 65535 := valid.2.2.2.1
  have recovery : Endpoint.RecoveryCoherent (Endpoint.writeState (preparedSeed seed) bytes) :=
    recovery_coherent seed valid empty
  change Endpoint.SendReady (Endpoint.writeState (preparedSeed seed) bytes) bytes.length
  simp only [Endpoint.SendReady, Endpoint.writeState, preparedSeed, ackState, recoveryState, pending,
    List.nil_append, empty, List.length_nil, Nat.zero_add]
  refine ⟨positive, Nat.le_refl _, ?_, ?_, size, ?_, recovery, ?_⟩
  · omega
  · change bytes.length ≤ 65535
    omega
  · omega
  · change 0 < bytes.length ∧ 0 + bytes.length ≤ seed.effectiveMSS ∧ 0 + bytes.length ≤ seed.effectiveMSS
    exact ⟨positive, by omega, by omega⟩

theorem PreparedStart.send (start : PreparedStart report complete bytes)
    (nonempty : bytes ≠ [])
    (mss : bytes.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive))
    (window : bytes.length ≤ input.passive.capacity) :
    ∃ actual : Step input, actual.before = start.next.report.final ∧
      actual.event = .send .client bytes.length true ∧ actual.result.supported = true ∧
      ∃ produced, actual.result.output = some produced ∧ produced.actor = .client ∧
        produced.output.packet.segment.payload = bytes := by
  have earlier := (CampusTCPChronology.Report.application_before start.next.report complete
    start.next.endpoints start.next.connection).1
  obtain ⟨effect, produced, computed, supported, output, actor, payload, _⟩ :=
    send_enabled start.next.report.final complete start.next.endpoints start.next.connection .client bytes.length earlier
      (start.send_ready nonempty mss window) start.client_ack
  refine ⟨⟨_, _, effect, computed⟩, rfl, rfl, supported, produced, output, actor, ?_⟩
  rw [payload, start.client]
  simp only [Endpoint.writeState, preparedSeed, ackState, recoveryState, complete.certificate.empty.1,
    List.nil_append, List.take_length]


end Netlib.Check.CampusTCPRoundSetup
