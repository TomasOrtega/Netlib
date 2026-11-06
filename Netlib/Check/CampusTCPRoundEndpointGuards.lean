import Netlib.Check.CampusTCPRoundEndpointGeometry
import Netlib.Check.CampusTCPRoundDelivery
import Netlib.Check.CampusTCPRoundAck

/-!
# Endpoint clock guards through a TCP round

The actual endpoint operations retain recovery and prepared ACK state.
These facts permit same-clock operations at every phase.
-/

namespace Netlib.Check.CampusTCPRoundGuards

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundSetup

structure Guarded (state : Endpoint.State) : Prop where
  recoveryCoherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  runtime : state.recovery.isSome = true

def Guards (endpoints : Applications complete) : Prop := ∀ actor, Guarded (endpoint endpoints actor)

theorem Guarded.outputState (guarded : Guarded state) : Guarded (Endpoint.outputState state) := by
  refine ⟨?_, Endpoint.outputState_ackPrepared state guarded.prepared, guarded.runtime⟩
  simpa only [Endpoint.RecoveryCoherent, Endpoint.outputState, Endpoint.AckWindowKnown] using guarded.recoveryCoherent

theorem Guarded.writeState (guarded : Guarded state) (bytes : List UInt8) : Guarded (Endpoint.writeState state bytes) := by
  refine ⟨?_, Endpoint.writeState_ackPrepared state bytes guarded.prepared, guarded.runtime⟩
  simpa only [Endpoint.RecoveryCoherent, Endpoint.writeState, Endpoint.AckWindowKnown] using guarded.recoveryCoherent

theorem Guarded.readState (guarded : Guarded state) (count : Nat) (valid : state.Valid)
    (fits : count ≤ state.core.received.length) : Guarded (Endpoint.readState state count) := by
  refine ⟨?_, Endpoint.readState_ackPrepared state count valid fits guarded.prepared, guarded.runtime⟩
  simpa only [Endpoint.RecoveryCoherent, Endpoint.readState, Endpoint.AckWindowKnown] using guarded.recoveryCoherent

theorem Guarded.sendState (guarded : Guarded state) (count : Nat) (ready : Endpoint.SendReady state count) :
    Guarded (Endpoint.sendState state count) := by
  cases runtime : state.recovery with
  | none =>
    have active := guarded.runtime
    simp only [runtime, Option.isSome_none, Bool.false_eq_true] at active
  | some recovery =>
    have coherent : recovery.Valid ∧ recovery.smss = state.effectiveMSS ∧
        Recovery.flight recovery = state.core.sent.length ∧ Endpoint.AckWindowKnown state := by
      simpa only [Endpoint.RecoveryCoherent, runtime] using guarded.recoveryCoherent
    have recoveryReady : Recovery.SendReady recovery count := by
      have bounded : Endpoint.RecoveryCoherent state ∧ Recovery.SendReady recovery count := by
        simpa only [Endpoint.recoveryReady, runtime] using ready.2.2.2.2.2.2
      exact bounded.2
    refine ⟨?_, Endpoint.sendState_ackPrepared state count guarded.prepared, ?_⟩
    · simp only [Endpoint.RecoveryCoherent, Endpoint.sendState, runtime, Option.map_some]
      refine ⟨Recovery.sent_valid recovery count coherent.1 recoveryReady, coherent.2.1, ?_, coherent.2.2.2⟩
      rw [Recovery.sent_flight, coherent.2.2.1]
      simp only [List.length_append, List.length_take, Nat.min_eq_left ready.2.1]
    · simp only [Endpoint.sendState, runtime, Option.map_some, Option.isSome_some]

theorem read_step_guarded (actual : ApplicationTrace.Step) (count : Nat) (event : actual.event = .read count)
    (fits : count ≤ actual.before.core.received.length) (guarded : Guarded actual.before) : Guarded actual.result.state := by
  have computed := congrArg Endpoint.Result.state actual.computed
  rw [event] at computed
  simp only [ApplicationTrace.evaluate, Endpoint.read_of_fits actual.before count actual.beforeValid fits] at computed
  rw [computed]
  exact guarded.readState count actual.beforeValid fits

variable {input : Input} {events : List Event} {complete : H.Completed input.active input.passive}
variable {report : Report input events} {bytes : List UInt8}

theorem PreparedStart.client_guards (start : PreparedStart report complete bytes) :
    Guarded (endpoint start.next.endpoints .client) := by
  refine ⟨?_, start.client_ack, ?_⟩
  · rw [start.client]
    simpa only [Endpoint.RecoveryCoherent, Endpoint.writeState, Endpoint.AckWindowKnown] using
      CampusTCPRoundEndpointGeometry.prepared_recovery complete.certificate.activeSeed
        complete.certificate.valid.1 complete.certificate.empty.2.1
  · rw [start.client]
    rfl

theorem PreparedStart.server_guards (start : PreparedStart report complete bytes) :
    Guarded (endpoint start.next.endpoints .server) := by
  refine ⟨?_, start.server_ack, ?_⟩
  · rw [start.server]
    exact CampusTCPRoundEndpointGeometry.prepared_recovery complete.certificate.passiveSeed
      complete.certificate.valid.2 complete.certificate.empty.2.2.2.2.1
  · rw [start.server]
    rfl

theorem PreparedStart.guards (start : PreparedStart report complete bytes) : Guards start.next.endpoints := by
  intro actor
  cases actor
  · exact PreparedStart.client_guards start
  · exact PreparedStart.server_guards start

theorem PreparedStart.sent_guards (start : PreparedStart report complete bytes)
    (nonempty : bytes ≠ [])
    (mss : bytes.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive))
    (window : bytes.length ≤ input.passive.capacity) :
    Guarded (Endpoint.sendState (endpoint start.next.endpoints .client) bytes.length) :=
  (PreparedStart.client_guards start).sendState bytes.length (start.send_ready nonempty mss window)

theorem guards_frame (before after : Applications complete) (actor : Actor) (guarded : Guarded selected)
    (changed : endpoint after actor = selected) (peer : endpoint after actor.other = endpoint before actor.other)
    (prior : Guards before) : Guards after := by
  intro receiver
  by_cases same : receiver = actor
  · rw [same, changed]
    exact guarded
  · have opposite : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
    rw [opposite, peer]
    exact prior actor.other

section

variable {endpoints : Applications complete} {index : Nat} {served : Served input}
  {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

theorem DataDelivered.after_guarded
    (delivery : CampusTCPRoundDelivery.DataDelivered report complete endpoints index served emission emitted)
    (recovery : Recovery.State) (reaction : AckReaction.State)
    (ready : CampusTCPDeliveryEnabled.InOrderReady (endpoint endpoints served.ticket.value.produced.actor.other)
      emission.asInput recovery reaction) : Guarded delivery.after := by
  refine ⟨delivery.recoveryCoherent, delivery.prepared, ?_⟩
  obtain ⟨acknowledged, witnessed, _, witnessedEq, accepted, _, _, _, _, _, _⟩ :=
    Endpoint.receive_inOrder_prepared (endpoint endpoints served.ticket.value.produced.actor.other) emission.asInput
      recovery reaction (endpoint_valid endpoints _) ready.recoveryCoherent ready.ackPrepared ready.storageCoherent
      ready.runtime ready.ackRuntime ready.sent ready.empty ready.tuple ready.controls ready.acknowledgment ready.sequence
      ready.nonempty ready.fits ready.bounded
  have afterEq : delivery.after = witnessed := by
    have computed := congrArg Endpoint.Result.state delivery.localStep.computed
    rw [delivery.localBefore, delivery.localEvent] at computed
    simp only [ApplicationTrace.evaluate] at computed
    rw [accepted] at computed
    exact delivery.resultState.symm.trans computed
  rw [afterEq, witnessedEq]
  change (Endpoint.windowState _ _ _).recovery.isSome = true
  rw [Endpoint.windowState_recovery]
  rfl

theorem DataDelivered.guards
    (delivery : CampusTCPRoundDelivery.DataDelivered report complete endpoints index served emission emitted)
    (recovery : Recovery.State) (reaction : AckReaction.State)
    (ready : CampusTCPDeliveryEnabled.InOrderReady (endpoint endpoints served.ticket.value.produced.actor.other)
      emission.asInput recovery reaction) (prior : Guards endpoints) : Guards delivery.updated :=
  guards_frame endpoints delivery.updated _ (DataDelivered.after_guarded delivery recovery reaction ready)
    delivery.selected delivery.peer prior

theorem AckDelivered.after_guarded
    (delivery : CampusTCPRoundDelivery.AckDelivered report complete endpoints index served emission emitted) :
    Guarded delivery.after := by
  refine ⟨delivery.recoveryCoherent, delivery.prepared, ?_⟩
  rw [delivery.runtime]
  rfl

theorem AckDelivered.guards
    (delivery : CampusTCPRoundDelivery.AckDelivered report complete endpoints index served emission emitted)
    (prior : Guards endpoints) : Guards delivery.updated :=
  guards_frame endpoints delivery.updated _ (AckDelivered.after_guarded delivery) delivery.selected delivery.peer prior

end

theorem AckFacts.guards (facts : CampusTCPRoundAck.AckFacts before complete endpoints actor actual)
    (prior : Guards endpoints) : Guards facts.after :=
  guards_frame endpoints facts.after actor (Guarded.outputState (prior actor)) facts.selected facts.peer prior

end Netlib.Check.CampusTCPRoundGuards
