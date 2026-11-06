import Netlib.Check.CampusTCPRoundSetup
import Netlib.Check.CampusTCPRoundEnvironment
import Netlib.Protocol.TCP.EndpointReceiveEnabled

/-!
# Local endpoint facts for a campus round

The packet facts follow from actual output encoding.
An advance to the stored clock keeps the endpoint state fixed.
-/

namespace Netlib.Check.CampusTCPRoundLocal

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundSetup

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {bytes : List UInt8}

private theorem setup_nonservice (start : PreparedStart report complete bytes)
    (actual : Step input) (member : actual ∈ start.setupSteps) :
    CampusTCPRoundEnvironment.Nonservice actual.event := by
  have covered := start.suffix.covered
  simp only [List.append_nil] at covered
  have event : actual.event ∈ setupEvents bytes := by
    rw [← covered]
    exact List.mem_map.mpr ⟨actual, member, rfl⟩
  simp only [setupEvents, List.mem_cons, List.not_mem_nil, or_false] at event
  rcases event with same | same | same | same | same
  all_goals rw [same]; trivial

theorem setup_resident (start : PreparedStart report complete bytes) (gateway : Gateway) :
    start.next.report.final.resident gateway = report.final.resident gateway :=
  CampusTCPRoundEnvironment.Trace.resident_nonservice start.suffix (setup_nonservice start) gateway

theorem setup_service (start : PreparedStart report complete bytes) (gateway : Gateway) :
    beforeService input start.next.report.final gateway = beforeService input report.final gateway := by
  have fixed := CampusTCPRoundEnvironment.Trace.environment start.suffix (by
    intro actual member
    have selected := setup_nonservice start actual member
    cases event : actual.event <;> simp_all [CampusTCPRoundEnvironment.Nonservice, CampusTCPRoundEnvironment.TransportOnly])
  have authentication := congrArg CampusTCPRoundEnvironment.Environment.authentication fixed
  change report.final.authentication = start.next.report.final.authentication at authentication
  simp only [beforeService, setup_resident start gateway, ← authentication]

theorem step_service_nonservice (actual : Step input)
    (selected : CampusTCPRoundEnvironment.Nonservice actual.event) (gateway : Gateway) :
    beforeService input actual.result.state gateway = beforeService input actual.before gateway := by
  have transport : CampusTCPRoundEnvironment.TransportOnly actual.event := by
    cases event : actual.event <;> simp_all [CampusTCPRoundEnvironment.Nonservice, CampusTCPRoundEnvironment.TransportOnly]
  have fixed := CampusTCPRoundEnvironment.Step.environment actual transport
  have authentication := congrArg CampusTCPRoundEnvironment.Environment.authentication fixed
  change actual.before.authentication = actual.result.state.authentication at authentication
  simp only [beforeService, CampusTCPRoundEnvironment.Step.resident_nonservice actual selected gateway, ← authentication]

theorem application_output (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (effect : Effect input) (actual : T.Step)
    (computed : applyApplication input before actor event = .ok effect)
    (recorded : effect.application = some (actor, actual))
    (produced : Produced input.active input.passive) (output : effect.output = some produced) :
    ∃ packet origin, produced = .application actor actual packet origin := by
  cases actor with
  | client =>
    cases found : endpoints.client.apply event before.time with
    | error reason =>
      simp [applyApplication, connection, found, parsed, Except.mapError, bind, Except.bind] at computed
    | ok applied =>
      simp only [applyApplication, connection, found, parsed, Except.mapError, bind, Except.bind,
        pure, Except.pure] at computed
      repeat' first
        | (solve | cases computed; dsimp only at output; cases output)
        | (solve
            | cases computed
              simp only [Option.some.injEq, Prod.mk.injEq, true_and] at recorded
              subst actual
              cases output
              exact ⟨_, _, rfl⟩)
        | (cases computed)
        | (split at computed)
        | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

  | server =>
    cases found : endpoints.server.apply event before.time with
    | error reason =>
      simp [applyApplication, connection, found, parsed, Except.mapError, bind, Except.bind] at computed
    | ok applied =>
      simp only [applyApplication, connection, found, parsed, Except.mapError, bind, Except.bind,
        pure, Except.pure] at computed
      repeat' first
        | (solve | cases computed; dsimp only at output; cases output)
        | (solve
            | cases computed
              simp only [Option.some.injEq, Prod.mk.injEq, true_and] at recorded
              subst actual
              cases output
              exact ⟨_, _, rfl⟩)
        | (cases computed)
        | (split at computed)
        | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem application_recorded (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time) :
    effect.application = some (actor, ApplicationTrace.Step.make (endpoint endpoints actor)
      (endpoint_valid endpoints actor) event before.time) := by
  cases actor
  all_goals
    obtain ⟨applied, found, same⟩ := cursor_apply_enabled _ event before.time earlier
    simp only [applyApplication, connection, found, parsed, Except.mapError, bind, Except.bind,
      pure, Except.pure] at computed
    repeat' first
      | (solve | cases computed; simp only [same, endpoint])
      | (cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem application_passed (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.passed = true := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem step_local_passed (joint : Step input) (actor : Actor) (event : T.Event)
    (action : LocalAction actor joint.event event) : joint.result.passed = true := by
  cases joint with
  | mk before jointEvent jointResult checked =>
    obtain ⟨effect, custody, core, same⟩ :=
      (⟨before, jointEvent, jointResult, checked⟩ : Step input).processed
    dsimp only at core same
    have applied : applyApplication input before actor event = .ok effect := by
      cases action <;> exact core
    simpa only [same] using application_passed before actor event effect applied

theorem step_application_recorded (joint : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : joint.before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (action : LocalAction actor joint.event event)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < joint.before.time) :
    joint.result.application = some (actor, ApplicationTrace.Step.make (endpoint endpoints actor)
      (endpoint_valid endpoints actor) event joint.before.time) := by
  cases joint with
  | mk before jointEvent jointResult checked =>
    obtain ⟨effect, custody, core, same⟩ :=
      (⟨before, jointEvent, jointResult, checked⟩ : Step input).processed
    dsimp only at core same
    have applied : applyApplication input before actor event = .ok effect := by
      cases action <;> exact core
    simpa only [same] using application_recorded before complete endpoints connection actor event effect applied earlier

theorem step_application_output (joint : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : joint.before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (action : LocalAction actor joint.event event) (actual : T.Step)
    (recorded : joint.result.application = some (actor, actual))
    (produced : Produced input.active input.passive) (output : joint.result.output = some produced) :
    ∃ packet origin, produced = .application actor actual packet origin := by
  cases joint with
  | mk before jointEvent jointResult checked =>
    obtain ⟨effect, custody, core, same⟩ :=
      (⟨before, jointEvent, jointResult, checked⟩ : Step input).processed
    dsimp only at core same
    have applied : applyApplication input before actor event = .ok effect := by
      cases action <;> exact core
    apply application_output before complete endpoints connection actor event effect actual applied
    · simpa only [same] using recorded
    · simpa only [same] using output

theorem original_encoded (origin : T.OutputOrigin actual packet) (original : ApplicationTrace.NoRetry actual) :
    ∃ bytes, Endpoint.emit actual.before bytes = .ok packet := by
  cases origin with
  | send count policy event accepted present =>
    have selected : (Endpoint.send actual.before count policy).decision = .accepted (.send count) := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using accepted
    obtain ⟨output, same, encoded, _, _, _⟩ := Endpoint.send_output _ _ _ selected
    have present' : (Endpoint.send actual.before count policy).output = some packet := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using present
    have equal : output = packet := Option.some.inj (same.symm.trans present')
    exact ⟨_, equal ▸ encoded⟩
  | ack policy event accepted present =>
    have selected : (Endpoint.emitAck actual.before policy).decision = .accepted .emitAck := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using accepted
    obtain ⟨output, same, encoded⟩ := Endpoint.emitAck_output _ _ selected
    have present' : (Endpoint.emitAck actual.before policy).output = some packet := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using present
    have equal : output = packet := Option.some.inj (same.symm.trans present')
    exact ⟨_, equal ▸ encoded⟩
  | dispatchAck policy event accepted present =>
    have selected : (Endpoint.dispatchAck actual.before policy).decision = .accepted .dispatchAck := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using accepted
    obtain ⟨output, same, encoded⟩ := Endpoint.dispatchAck_output _ _ selected
    have present' : (Endpoint.dispatchAck actual.before policy).output = some packet := by
      simpa only [actual.computed, event, ApplicationTrace.evaluate] using present
    have equal : output = packet := Option.some.inj (same.symm.trans present')
    exact ⟨_, equal ▸ encoded⟩
  | retry count policy event accepted present => exact False.elim (original policy event)

theorem emit_ttl (state : Endpoint.State) (bytes : List UInt8) (packet : EstablishedReceive.Input)
    (encoded : Endpoint.emit state bytes = .ok packet) : packet.packet.ip.packet.ttl.toNat = 64 := by
  cases selected : state.ackReaction with
  | none =>
    have actual : Output.emit state.core bytes = .ok packet := by simpa only [Endpoint.emit, selected] using encoded
    rw [(Output.emit_fields _ _ _ actual).2.2.2]
    rfl
  | some reaction =>
    have actual : Output.emitAtWindow state.core state.core.sendNext (Endpoint.outputWindow state) bytes = .ok packet := by
      simpa only [Endpoint.emit, selected, Output.emitWindow] using encoded
    rw [(Output.emitAtWindow_fields _ _ _ _ _ actual).2.2.2.2]
    rfl

theorem emit_profile (state : Endpoint.State) (bytes : List UInt8) (packet : EstablishedReceive.Input)
    (encoded : Endpoint.emit state bytes = .ok packet) :
    Admission.DataProfile packet.packet.segment ∧ EstablishedReceive.control packet.packet.segment = none ∧
      Flags.ack packet.packet.segment.flags = true ∧ 1 < packet.packet.ip.packet.ttl.toNat := by
  obtain ⟨_, _, _, _, flags, _, options, _⟩ := Endpoint.emit_transport _ _ _ encoded
  refine ⟨⟨.inl flags, options⟩, ?_, ?_, ?_⟩
  · simp only [EstablishedReceive.control, flags, options]
    rfl
  · rw [flags]
    rfl
  · rw [emit_ttl state bytes packet encoded]
    decide

theorem advance_same (state : Endpoint.State) (valid : state.Valid)
    (coherent : Endpoint.RecoveryCoherent state) (prepared : Endpoint.AckPrepared state)
    (recovery : state.recovery.isSome = true) :
    Endpoint.advanceClock state state.now = ⟨state, .accepted .advanceClock, none, [], none⟩ := by
  cases runtime : state.recovery with
  | none => simp only [runtime, Option.isSome_none, Bool.false_eq_true] at recovery
  | some stored =>
    have now : state.now = stored.now := by simp only [Endpoint.State.now, runtime, Option.map_some, Option.getD_some]
    have moved : Recovery.advance stored state.now = .ok stored := by
      rw [now, Recovery.advance_of_monotone stored stored.now (Nat.le_refl _)]
    simp only [Endpoint.advanceClock, valid, coherent, not_true_eq_false, ite_false, runtime, moved]
    cases reaction : state.ackReaction with
    | none =>
      dsimp only
      have same : { state with recovery := some stored, ackReaction := none } = state := by
        rw [← runtime, ← reaction]
      exact congrArg (fun after => (⟨after, .accepted .advanceClock, none, [], none⟩ : Endpoint.Result)) same
    | some value =>
      have fields : value.WithinTime state.now ∧
          value.Covered state.core.capacity state.core.window state.effectiveMSS := by
        simpa only [reaction] using prepared.2
      dsimp only
      rw [AckReaction.checkTime_of_within value state.now fields.1]
      have same : { state with recovery := some stored, ackReaction := some value } = state := by
        rw [← runtime, ← reaction]
      exact congrArg (fun after => (⟨after, .accepted .advanceClock, none, [], none⟩ : Endpoint.Result)) same

theorem prepared_storage (seed : Endpoint.State) (received : seed.core.received = [])
    (store : seed.receiveStore = ReceiveStore.initial) : Endpoint.StorageCoherent (preparedSeed seed) := by
  have window : seed.core.window = seed.core.capacity := by
    simp only [EstablishedReceive.State.window, received, List.length_nil, Nat.sub_zero]
  have valid := ReceiveStore.initial_valid (Meta := ReceiveReassembly.Receipt)
    seed.core.capacity seed.core.capacity (Nat.le_refl _)
  constructor
  · exact Endpoint.storage_valid_of_empty _ (by simp only [preparedSeed, ackState, recoveryState, store, ReceiveStore.initial])
  · constructor
    · simp only [preparedSeed, ackState, recoveryState, AckReaction.initial,
        ReceiveAdvertisement.initial, store, ReceiveStore.initial]
    · change seed.receiveStore.Valid (seed.receiveStore.frontier + seed.core.capacity) seed.core.window
      rw [store, window]
      simpa only [ReceiveStore.initial, Nat.zero_add] using valid

end Netlib.Check.CampusTCPRoundLocal
