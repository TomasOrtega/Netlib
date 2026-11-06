import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Protocol.TCP.EndpointAckEnabled

/-!
# Campus operations from preceding guards

Readiness uses stored packets, routes, endpoint state, and clocks.
It does not contain a successful operation result.
-/

namespace Netlib.Check.CampusTCPEnabled

open CampusTCPModel
namespace C
export Netlib.Theory.PacketCustody (State Item resolve)
end C

variable {input : Input}

def RouteReady (before : State input) (actor : Actor) : Prop :=
  before.assignmentPaused = false ∧ input.configured (before.owner actor) = true ∧
    (before.owner actor = .primary → before.primarySealed = false ∧ before.primaryFenced = false) ∧
    (before.owner actor = .standby → before.installation.isSome = true)

def IngressPending (before : State input) (index : Nat) : Prop :=
  ∃ item ∈ before.custody.pending, Transit.ingressAt index item.value.payload = true

theorem prepare_assign_exists (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (pending : IngressPending before index) :
    ∃ custody, prepareCustody before (.assign index ingress) = .ok custody := by
  obtain ⟨id, selected⟩ := before.custody.pendingID_exists (Transit.ingressAt index) pending
  obtain ⟨item, member, same, _⟩ := before.custody.pendingID_source (Transit.ingressAt index) id selected
  obtain ⟨result, resolved⟩ := Theory.PacketCustody.resolve_completes before.custody item member .assigned
  subst id
  exact ⟨result.state, by simp only [prepareCustody, selected, resolved, Except.mapError, bind, Except.bind, pure, Except.pure]⟩

theorem assign_enabled (before : State input) (index : Nat) (ingress : I.InterfaceRef)
    (produced : Produced input.active input.passive) (source : before.outputs[index]? = some produced)
    (route : RouteReady before produced.actor) (pending : IngressPending before index) :
    ∃ effect, step input before (.assign index ingress) = .ok effect ∧
      effect.supported = true ∧ effect.passed = true ∧
      effect.state.work = Theory.Outstanding.enqueue before.work
        ⟨index, produced, ingress, before.owner produced.actor, before.routeEpoch⟩ := by
  obtain ⟨custody, prepared⟩ := prepare_assign_exists before index ingress pending
  have primary : (before.owner produced.actor == .primary && (before.primarySealed || before.primaryFenced)) = false := by
    cases owner : before.owner produced.actor with
    | primary => simp [(route.2.2.1 owner).1, (route.2.2.1 owner).2]
    | standby => rfl
  have standby : (before.owner produced.actor == .standby && before.installation.isNone) = false := by
    cases owner : before.owner produced.actor with
    | primary => rfl
    | standby =>
      have installed := route.2.2.2 owner
      cases selected : before.installation <;> simp_all
  simp only [step, process, processCore, route.1, Bool.false_eq_true, ↓reduceIte,
    CampusTCPModel.get, source, bind, Except.bind, pure, Except.pure, route.2.1, Bool.not_true,
    primary, standby, prepared]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem assignment_after_output (actual : Step input) (produced : Produced input.active input.passive)
    (output : actual.result.output = some produced) (route : RouteReady actual.result.state produced.actor)
    (ingress : I.InterfaceRef) :
    ∃ effect, step input actual.result.state (.assign actual.before.outputs.length ingress) = .ok effect ∧
      effect.supported = true ∧ effect.passed = true ∧
      effect.state.work = Theory.Outstanding.enqueue actual.result.state.work
        ⟨actual.before.outputs.length, produced, ingress, actual.result.state.owner produced.actor,
          actual.result.state.routeEpoch⟩ := by
  have source : actual.result.state.outputs[actual.before.outputs.length]? = some produced := by
    rw [CampusTCPOrigins.output_history actual, output]
    simp
  obtain ⟨item, member, _, packet⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced output
  have pending : IngressPending actual.result.state actual.before.outputs.length :=
    ⟨item, member, by simp only [packet, Transit.ingressAt, beq_self_eq_true]⟩
  exact assign_enabled _ _ _ _ source route pending


theorem cursor_apply_enabled (before : Cursor seed) (event : T.Event) (stamp : Nat)
    (earlier : ∀ old ∈ before.steps, old.stamp < stamp) :
    ∃ applied, before.apply event stamp = .ok applied ∧
      applied.step = Protocol.TCP.ApplicationTrace.Step.make before.current before.valid event stamp := by
  have ordered : before.steps.all (fun old => decide (old.stamp < stamp)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using earlier
  simp only [Cursor.apply, ordered, dite_true, pure, Except.pure]
  exact ⟨_, rfl, rfl⟩

def endpoint (endpoints : Applications complete) : Actor → Protocol.TCP.Endpoint.State
  | .client => endpoints.client.current
  | .server => endpoints.server.current

def applicationSteps (endpoints : Applications complete) : Actor → List T.Step
  | .client => endpoints.client.steps
  | .server => endpoints.server.steps

theorem endpoint_valid (endpoints : Applications complete) (actor : Actor) : (endpoint endpoints actor).Valid := by
  cases actor
  · exact endpoints.client.valid
  · exact endpoints.server.valid

private theorem stepOutput_exists (actual : T.Step) (output : Protocol.TCP.EstablishedReceive.Input)
    (origin : T.OutputOrigin actual output) :
    ∃ checked, Protocol.TCP.ApplicationTrace.stepOutput actual = .ok checked ∧ checked.val = output := by
  refine ⟨⟨output, origin⟩, ?_, rfl⟩
  cases actual with
  | mk before event result stamp valid computed =>
    cases origin with
    | send count policy same accepted present =>
      dsimp only at same accepted present
      cases same
      cases result with
      | mk state decision packet read ack =>
        dsimp only at accepted present
        subst decision
        subst packet
        simp [Protocol.TCP.ApplicationTrace.stepOutput]
    | retry count policy same accepted present =>
      dsimp only at same accepted present
      cases same
      cases result with
      | mk state decision packet read ack =>
        dsimp only at accepted present
        subst decision
        subst packet
        simp [Protocol.TCP.ApplicationTrace.stepOutput]
    | ack policy same accepted present | dispatchAck policy same accepted present =>
      dsimp only at same accepted present
      cases same
      cases result with
      | mk state decision packet read ack =>
        dsimp only at accepted present
        subst decision
        subst packet
        simp [Protocol.TCP.ApplicationTrace.stepOutput]

private theorem output_supported (actual : T.Step) (output : Protocol.TCP.EstablishedReceive.Input)
    (origin : T.OutputOrigin actual output) : actual.supported = true := by
  cases origin with
  | send count policy event accepted present | retry count policy event accepted present =>
    simp only [Protocol.TCP.ApplicationTrace.Step.supported, accepted]
  | ack policy event accepted present | dispatchAck policy event accepted present =>
    simp only [Protocol.TCP.ApplicationTrace.Step.supported, accepted]

theorem application_emitting (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (output : Protocol.TCP.EstablishedReceive.Input)
    (origin : T.OutputOrigin (Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
      (endpoint_valid endpoints actor) event before.time) output) :
    ∃ effect produced, applyApplication input before actor event = .ok effect ∧ effect.output = some produced ∧
      produced.actor = actor ∧ produced.output = output ∧ effect.supported = true ∧
      effect.application = some (actor, Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) event before.time) := by
  cases actor
  all_goals
    obtain ⟨applied, computed, same⟩ := cursor_apply_enabled _ event before.time earlier
    have actual : T.OutputOrigin applied.step output := by simpa only [same, endpoint] using origin
    obtain ⟨checked, emitted, bytes⟩ := stepOutput_exists applied.step output actual
    have present : applied.step.result.output = some output := by
      cases actual <;> assumption
    simp only [applyApplication, connection, computed, parsed, Except.mapError, bind, Except.bind,
      pure, Except.pure, present, emitted]
    exact ⟨_, _, rfl, rfl, rfl, bytes, output_supported _ _ actual, by simp only [same, endpoint]⟩

/-- Lift a derived endpoint result through the actual stored cursor. -/
theorem application_quiet (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (result : Protocol.TCP.Endpoint.Result) (action : Protocol.TCP.Endpoint.Accepted)
    (evaluated : Protocol.TCP.ApplicationTrace.evaluate (endpoint endpoints actor) event = result)
    (quiet : result.output = none) (accepted : result.decision = .accepted action) :
    ∃ effect, applyApplication input before actor event = .ok effect ∧ effect.supported = true ∧
      effect.output = none ∧ effect.read = result.read ∧
      effect.application = some (actor, Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) event before.time) := by
  cases actor
  all_goals
    obtain ⟨applied, computed, same⟩ := cursor_apply_enabled _ event before.time earlier
    have actual : applied.step.result = result := by
      simpa only [same, Protocol.TCP.ApplicationTrace.Step.make, endpoint] using evaluated
    have present : applied.step.result.output = none := actual ▸ quiet
    have supported : applied.step.supported = true := by
      simp only [Protocol.TCP.ApplicationTrace.Step.supported, actual, accepted]
    simp only [applyApplication, connection, computed, parsed, Except.mapError, bind, Except.bind,
      pure, Except.pure, present]
    exact ⟨_, rfl, supported, rfl, by rw [actual], by simp only [same, endpoint]⟩

theorem finish_step (before : State input) (event : Event) (effect : Effect input)
    (core : processCore input before event = .ok effect)
    (prepared : prepareCustody before event = .ok before.custody) :
    ∃ after, step input before event = .ok after ∧ after.supported = effect.supported ∧
      after.output = effect.output ∧ after.application = effect.application ∧ after.read = effect.read := by
  simp only [step, process, core, prepared, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem send_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (count : Nat)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (ready : Protocol.TCP.Endpoint.SendReady (endpoint endpoints actor) count)
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor)) :
    ∃ effect produced, step input before (.send actor count true) = .ok effect ∧
      effect.supported = true ∧ effect.output = some produced ∧ produced.actor = actor ∧
      produced.output.packet.segment.payload = (endpoint endpoints actor).pending.take count ∧
      effect.application = some (actor, Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) (.send count true) before.time) := by
  obtain ⟨output, sent⟩ := Protocol.TCP.Endpoint.send_success_enabled _ count (endpoint_valid endpoints actor) ready prepared
  have origin : T.OutputOrigin (Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
      (endpoint_valid endpoints actor) (.send count true) before.time) output :=
    .send count true rfl (by simp only [Protocol.TCP.ApplicationTrace.Step.make,
      Protocol.TCP.ApplicationTrace.evaluate, sent]) (by simp only [Protocol.TCP.ApplicationTrace.Step.make,
      Protocol.TCP.ApplicationTrace.evaluate, sent])
  obtain ⟨effect, produced, computed, present, who, wire, supported, application⟩ :=
    application_emitting before complete endpoints connection actor (.send count true) earlier output origin
  obtain ⟨after, checked, supportEq, outputEq, appEq, _⟩ := finish_step before (.send actor count true) effect computed rfl
  have selected : (Protocol.TCP.Endpoint.send (endpoint endpoints actor) count true).decision = .accepted (.send count) := by rw [sent]
  obtain ⟨actual, actualPresent, _, payload, _, _⟩ := Protocol.TCP.Endpoint.send_output _ _ _ selected
  have same : actual = output := Option.some.inj (actualPresent.symm.trans (by rw [sent]))
  refine ⟨after, produced, checked, supportEq.trans supported, outputEq.trans present, who, ?_, appEq.trans application⟩
  rw [wire, ← same]
  exact payload

private theorem ack_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (dueOnly : Bool)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (available : Protocol.TCP.Endpoint.ResponseAvailable (endpoint endpoints actor) dueOnly) :
    ∃ effect produced, step input before (if dueOnly then .dispatchAck actor true else .emitAck actor true) = .ok effect ∧
      effect.supported = true ∧ effect.output = some produced ∧ produced.actor = actor ∧
      produced.output.packet.segment.payload = [] ∧
      produced.output.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext := by
  obtain ⟨output, sent, encoded⟩ := Protocol.TCP.Endpoint.pureAck_success_enabled _ dueOnly
    (endpoint_valid endpoints actor) prepared available
  let event : T.Event := if dueOnly then .dispatchAck true else .emitAck true
  let joint : Event := if dueOnly then .dispatchAck actor true else .emitAck actor true
  cases dueOnly
  all_goals
    have origin : T.OutputOrigin (Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) event before.time) output := by
      simp only [event, Bool.false_eq_true, ite_true, ite_false]
      first
      | exact .ack true rfl (by simpa only [Protocol.TCP.ApplicationTrace.Step.make,
          Protocol.TCP.ApplicationTrace.evaluate, Protocol.TCP.Endpoint.emitAck, Bool.false_eq_true, ite_false] using congrArg Protocol.TCP.Endpoint.Result.decision sent)
          (by simpa only [Protocol.TCP.ApplicationTrace.Step.make, Protocol.TCP.ApplicationTrace.evaluate,
            Protocol.TCP.Endpoint.emitAck, Bool.false_eq_true, ite_false] using congrArg Protocol.TCP.Endpoint.Result.output sent)
      | exact .dispatchAck true rfl (by simpa only [Protocol.TCP.ApplicationTrace.Step.make,
          Protocol.TCP.ApplicationTrace.evaluate, Protocol.TCP.Endpoint.dispatchAck, Bool.true_eq, ite_true] using congrArg Protocol.TCP.Endpoint.Result.decision sent)
          (by simpa only [Protocol.TCP.ApplicationTrace.Step.make, Protocol.TCP.ApplicationTrace.evaluate,
            Protocol.TCP.Endpoint.dispatchAck, Bool.true_eq, ite_true] using congrArg Protocol.TCP.Endpoint.Result.output sent)
    obtain ⟨effect, produced, computed, present, who, wire, supported, _⟩ :=
      application_emitting before complete endpoints connection actor _ earlier output origin
    obtain ⟨after, checked, supportEq, outputEq, _, _⟩ := finish_step before joint effect
      (by simpa only [processCore, joint, event, Bool.false_eq_true, Bool.true_eq, ite_true, ite_false] using computed)
      (by simp only [prepareCustody, joint, Bool.false_eq_true, ite_true, ite_false]; rfl)
    refine ⟨after, produced, checked, supportEq.trans supported, outputEq.trans present, who, ?_, ?_⟩
    · rw [wire]
      exact Protocol.TCP.Endpoint.emit_payload _ _ _ encoded
    · rw [wire]
      exact (Protocol.TCP.Endpoint.emit_transport _ _ _ encoded).2.2.1

theorem emitAck_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (available : Protocol.TCP.Endpoint.ResponseAvailable (endpoint endpoints actor) false) :
    ∃ effect produced, step input before (.emitAck actor true) = .ok effect ∧
      effect.supported = true ∧ effect.output = some produced ∧ produced.actor = actor ∧
      produced.output.packet.segment.payload = [] ∧
      produced.output.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext :=
  ack_enabled before complete endpoints connection actor false earlier prepared available

theorem dispatchAck_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (prepared : Protocol.TCP.Endpoint.AckPrepared (endpoint endpoints actor))
    (available : Protocol.TCP.Endpoint.ResponseAvailable (endpoint endpoints actor) true) :
    ∃ effect produced, step input before (.dispatchAck actor true) = .ok effect ∧
      effect.supported = true ∧ effect.output = some produced ∧ produced.actor = actor ∧
      produced.output.packet.segment.payload = [] ∧
      produced.output.packet.segment.acknowledgment = (endpoint endpoints actor).core.receiveNext :=
  ack_enabled before complete endpoints connection actor true earlier prepared available

theorem write_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (bytes : List UInt8)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (fits : (endpoint endpoints actor).pending.length + bytes.length ≤ (endpoint endpoints actor).pendingLimit) :
    ∃ effect, step input before (.write actor bytes) = .ok effect ∧ effect.supported = true ∧
      effect.output = none ∧ effect.read = [] ∧
      effect.application = some (actor, Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) (.write bytes) before.time) := by
  have written := Protocol.TCP.Endpoint.write_of_fits (endpoint endpoints actor) bytes (endpoint_valid endpoints actor) fits
  obtain ⟨effect, computed, supported, quiet, read, application⟩ :=
    application_quiet before complete endpoints connection actor (.write bytes) earlier
      ⟨Protocol.TCP.Endpoint.writeState (endpoint endpoints actor) bytes, .accepted (.write bytes.length), none, [], none⟩
      (.write bytes.length) written rfl rfl
  obtain ⟨after, checked, supportEq, outputEq, appEq, readEq⟩ := finish_step before (.write actor bytes) effect computed rfl
  exact ⟨after, checked, supportEq.trans supported, outputEq.trans quiet, readEq.trans read, appEq.trans application⟩

theorem read_enabled (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (count : Nat)
    (earlier : ∀ old ∈ applicationSteps endpoints actor, old.stamp < before.time)
    (fits : count ≤ (endpoint endpoints actor).core.received.length) :
    ∃ effect, step input before (.read actor count) = .ok effect ∧ effect.supported = true ∧
      effect.output = none ∧ effect.read = (endpoint endpoints actor).core.received.take count ∧
      effect.application = some (actor, Protocol.TCP.ApplicationTrace.Step.make (endpoint endpoints actor)
        (endpoint_valid endpoints actor) (.read count) before.time) := by
  have consumed := Protocol.TCP.Endpoint.read_of_fits (endpoint endpoints actor) count (endpoint_valid endpoints actor) fits
  obtain ⟨effect, computed, supported, quiet, read, application⟩ :=
    application_quiet before complete endpoints connection actor (.read count) earlier
      ⟨Protocol.TCP.Endpoint.readState (endpoint endpoints actor) count, .accepted (.read count), none,
        (endpoint endpoints actor).core.received.take count, none⟩ (.read count) consumed rfl rfl
  obtain ⟨after, checked, supportEq, outputEq, appEq, readEq⟩ := finish_step before (.read actor count) effect computed rfl
  exact ⟨after, checked, supportEq.trans supported, outputEq.trans quiet, readEq.trans read, appEq.trans application⟩

private theorem cursor_apply_fields (before : Cursor seed) (event : T.Event) (stamp : Nat)
    (applied : Applied before) (computed : before.apply event stamp = .ok applied) :
    applied.step.event = event ∧ applied.step.stamp = stamp := by
  unfold Cursor.apply at computed
  split at computed
  · cases computed
    exact ⟨rfl, rfl⟩
  · cases computed

theorem application_frame (before : State input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (effect : Effect input) (actual : T.Step)
    (computed : applyApplication input before actor event = .ok effect)
    (recorded : effect.application = some (actor, actual)) :
    ∃ after : Applications complete, effect.state.connection = .application complete after ∧
      endpoint after actor = actual.result.state ∧ endpoint after actor.other = endpoint endpoints actor.other ∧
      applicationSteps after actor = applicationSteps endpoints actor ++ [actual] ∧
      applicationSteps after actor.other = applicationSteps endpoints actor.other ∧
      actual.before = endpoint endpoints actor ∧ actual.event = event ∧ actual.stamp = before.time := by
  cases actor with
  | client =>
    cases accepted : endpoints.client.apply event before.time with
    | error reason => simp [applyApplication, connection, accepted, parsed, Except.mapError, bind, Except.bind] at computed
    | ok applied =>
      have fields := cursor_apply_fields _ event before.time applied accepted
      simp only [applyApplication, connection, accepted, parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      repeat' first
        | (solve
            | cases computed
              dsimp only at recorded
              cases recorded
              exact ⟨_, rfl, applied.state, rfl, applied.history, rfl, applied.same, fields.1, fields.2⟩)
        | (cases computed)
        | (split at computed)
        | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)
  | server =>
    cases accepted : endpoints.server.apply event before.time with
    | error reason => simp [applyApplication, connection, accepted, parsed, Except.mapError, bind, Except.bind] at computed
    | ok applied =>
      have fields := cursor_apply_fields _ event before.time applied accepted
      simp only [applyApplication, connection, accepted, parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      repeat' first
        | (solve
            | cases computed
              dsimp only at recorded
              cases recorded
              exact ⟨_, rfl, applied.state, rfl, applied.history, rfl, applied.same, fields.1, fields.2⟩)
        | (cases computed)
        | (split at computed)
        | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

inductive LocalAction (actor : Actor) : Event → T.Event → Prop where
  | write (bytes) : LocalAction actor (.write actor bytes) (.write bytes)
  | send (count policy) : LocalAction actor (.send actor count policy) (.send count policy)
  | read (count) : LocalAction actor (.read actor count) (.read count)
  | emitAck (policy) : LocalAction actor (.emitAck actor policy) (.emitAck policy)
  | dispatchAck (policy) : LocalAction actor (.dispatchAck actor policy) (.dispatchAck policy)
  | enableRecovery : LocalAction actor (.enableRecovery actor) .enableRecovery
  | advanceClock (millis) : LocalAction actor (.advanceClock actor millis) (.advanceClock millis)
  | timeout (policy) : LocalAction actor (.timeout actor policy) (.timeout policy)

theorem Step.application_frame (joint : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : joint.before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (action : LocalAction actor joint.event event) (actual : T.Step)
    (recorded : joint.result.application = some (actor, actual)) :
    ∃ after : Applications complete, joint.result.state.connection = .application complete after ∧
      endpoint after actor = actual.result.state ∧ endpoint after actor.other = endpoint endpoints actor.other ∧
      applicationSteps after actor = applicationSteps endpoints actor ++ [actual] ∧
      applicationSteps after actor.other = applicationSteps endpoints actor.other ∧
      actual.before = endpoint endpoints actor ∧ actual.event = event ∧ actual.stamp = joint.before.time := by
  cases joint with
  | mk before jointEvent jointResult checked =>
    obtain ⟨effect, custody, core, result⟩ := (Step.processed (⟨before, jointEvent, jointResult, checked⟩ : Step input))
    dsimp only at core result
    have applied : applyApplication input before actor event = .ok effect := by
      cases action <;> exact core
    have present : effect.application = some (actor, actual) := by simpa only [result] using recorded
    simpa only [result] using CampusTCPEnabled.application_frame before complete endpoints connection actor event effect actual applied present

def ApplicationsBefore (endpoints : Applications complete) (time : Nat) : Prop :=
  ∀ actor, ∀ old ∈ applicationSteps endpoints actor, old.stamp < time

theorem Step.application_chronology (joint : Step input) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : joint.before.connection = .application complete endpoints)
    (actor : Actor) (event : T.Event) (action : LocalAction actor joint.event event) (actual : T.Step)
    (recorded : joint.result.application = some (actor, actual))
    (earlier : ApplicationsBefore endpoints joint.before.time) :
    ∃ after : Applications complete, joint.result.state.connection = .application complete after ∧
      ApplicationsBefore after joint.result.state.time := by
  obtain ⟨after, connectionEq, _, _, selected, other, _, _, stamp⟩ :=
    Step.application_frame joint complete endpoints connection actor event action actual recorded
  refine ⟨after, connectionEq, ?_⟩
  intro receiver old member
  rw [joint.clock]
  by_cases same : receiver = actor
  · subst receiver
    rw [selected] at member
    rcases List.mem_append.mp member with prior | current
    · exact Nat.lt_trans (earlier actor old prior) (Nat.lt_succ_self _)
    · have same := List.mem_singleton.mp current
      rw [same, stamp]
      exact Nat.lt_succ_self _
  · have opposite : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
    rw [opposite, other] at member
    exact Nat.lt_trans (earlier actor.other old member) (Nat.lt_succ_self _)

end Netlib.Check.CampusTCPEnabled
