import Netlib.Check.CampusTCPFacts

/-!
# Startup records in one actual campus history

The projection reads stored startup records. It does not run the endpoints again.
-/

namespace Netlib.Check.CampusTCPStartupOrigins

open Packet Protocol CampusTCPModel
namespace H
export Check.TCPHandshake (Stage Step Completed Opened Answered Acknowledged Event)
end H

variable {input : Input}

def stage : Connection active passive → H.Stage active passive
  | .startup value _ => value
  | .application complete _ => .complete complete

@[simp] theorem stage_ofStage (value : H.Stage active passive) :
    stage (Connection.ofStage value) = value := by cases value <;> rfl

private def Linked (before : State input) (effect : Effect input) : Prop :=
  match effect.startup with
  | none => stage effect.state.connection = stage before.connection
  | some actual => actual.before = stage before.connection ∧ actual.index = before.time ∧
      stage effect.state.connection = actual.result.state

private theorem startup_linked (before : State input) (event : H.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : Linked before effect := by
  unfold startup at computed
  split at computed
  · cases computed; rfl
  · split at computed
    · cases computed
    · split at computed
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        simp only [Linked, publish, stage_ofStage]
        simp_all [stage]

private theorem application_linked (before : State input) (actor : Actor)
    (event : TCP.ApplicationTrace.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : Linked before effect := by
  unfold applyApplication at computed
  split at computed
  · cases computed; rfl
  · cases actor <;> simp only at computed
    all_goals repeat' first
      | (solve | cases computed)
      | (solve | cases computed; simp_all [Linked, stage, publish])
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)

private theorem application_no_startup (before : State input) (actor : Actor)
    (event : TCP.ApplicationTrace.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : effect.startup = none := by
  unfold applyApplication at computed
  split at computed
  · cases computed; rfl
  · cases actor <;> simp only at computed
    all_goals repeat' first
      | (solve | cases computed)
      | (solve | cases computed; rfl)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)

private theorem enableAck_linked (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : Linked before effect := by
  unfold enableAck at computed
  split at computed
  · exact application_linked _ _ _ _ computed
  · cases actor <;> dsimp only at computed
    all_goals
      split at computed
      · exact application_linked _ _ _ _ computed
      · cases computed

@[simp] private theorem stage_write (before : State input) (gateway) (resident) :
    stage (before.write gateway resident).connection = stage before.connection := by cases gateway <;> rfl

private theorem process_linked (before : State input) (event : CampusTCPModel.Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) : Linked before effect := by
  cases event with
  | «open» remote policy => exact startup_linked _ _ _ computed
  | write actor bytes | send actor bytes policy | read actor bytes | emitAck actor policy =>
    exact application_linked _ _ _ _ computed
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_linked _ _ _ _ computed
  | enableAck actor => exact enableAck_linked _ _ _ computed
  | copyPacket id | dropPacket id => cases computed; rfl
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; rfl)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; simp [Linked, stage_write])
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; rfl)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress | serve index observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed)
      | (solve | cases computed; simp [Linked, stage_write, unsupported])
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; have fresh := startup_linked before _ _ (by assumption); exact fresh)
      | (solve | cases computed; have fresh := application_linked before _ _ _ (by assumption); exact fresh)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.linked (actual : CampusTCPModel.Step input) :
    match actual.result.startup with
    | none => stage actual.result.state.connection = stage actual.before.connection
    | some startupStep => startupStep.before = stage actual.before.connection ∧ startupStep.index = actual.before.time ∧
        stage actual.result.state.connection = startupStep.result.state := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  simpa only [result, Linked] using process_linked actual.before actual.event effect computed

inductive Chain : H.Stage active passive → List (H.Step active passive) → H.Stage active passive → Prop where
  | done (value) : Chain value [] value
  | next (head : H.Step active passive) (tail : Chain head.result.state rest final) :
      Chain head.before (head :: rest) final

theorem Trace.startup_chain (trace : CampusTCPModel.Trace input initial events steps final remaining) :
    Chain (stage initial.connection) (steps.filterMap (·.result.startup)) (stage final.connection) := by
  induction trace with
  | done => exact .done _
  | stop head _ _ =>
    have linked := Step.linked head
    cases found : head.result.startup with
    | none =>
      simp only [found] at linked
      simpa [found, linked] using Chain.done (stage head.before.connection)
    | some startupStep =>
      simp only [found] at linked
      simpa [found, linked.1, linked.2.2] using
        Chain.next startupStep (Chain.done startupStep.result.state)
  | next head _ _ ih =>
    have linked := Step.linked head
    cases found : head.result.startup with
    | none =>
      simp only [found] at linked
      simpa [found, linked] using ih
    | some startupStep =>
      simp only [found] at linked
      rw [linked.2.2] at ih
      simpa [found, linked.1] using Chain.next startupStep ih

theorem Report.startup_chain (report : CampusTCPModel.Report input events) :
    Chain .idle (report.steps.filterMap (·.result.startup)) (stage report.final.connection) :=
  Trace.startup_chain report.trace

private theorem startup_event (before : State input) (event : H.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) (actual : H.Step input.active input.passive)
    (recorded : effect.startup = some actual) : actual.event = event := by
  unfold startup at computed
  split at computed
  · cases computed; cases recorded
  · split at computed
    · cases computed
    · split at computed
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        cases recorded
        rfl

inductive ReceiveEvent : H.Event → Actor → CampusTCPFacts.StartupKind → List UInt8 → Prop where
  | syn (bytes policy) : ReceiveEvent (.listenSyn bytes .rewrite policy) .server .syn bytes
  | synAck (bytes policy) : ReceiveEvent (.synSentSynAck bytes .rewrite policy) .client .synAck bytes
  | ack (bytes) : ReceiveEvent (.synReceivedAck bytes .rewrite) .server .ack bytes

private theorem parsed_input_bytes (value : TCP.EstablishedReceive.Input)
    (computed : parsed (TCP.EstablishedReceive.input bytes) = .ok value) : value.bytes = bytes := by
  cases decoded : TCP.EstablishedReceive.input bytes with
  | error reason => simp [decoded, parsed, Except.mapError] at computed
  | ok packet =>
    simp only [decoded, parsed, Except.mapError, Except.ok.injEq] at computed
    subst value
    unfold TCP.EstablishedReceive.input at decoded
    split at decoded
    · cases decoded
    · cases decoded; rfl

theorem Step.startup_receipt (joint : CampusTCPModel.Step input)
    (actual : H.Step input.active input.passive) (recorded : joint.result.startup = some actual)
    (index : Nat) (bytes : List UInt8) (policy : Bool)
    (event : joint.event = .deliver index bytes policy)
    (received : ReceiveEvent actual.event actor kind bytes) :
    ∃ receipt : Receipt input, joint.result.receipt = some receipt ∧ receipt.received.bytes = bytes ∧
      receipt.actor = actor ∧ CampusTCPFacts.startupKind receipt.served.ticket.value.produced = some kind := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have present : effect.startup = some actual := by simpa only [result] using recorded
  rw [event] at computed
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; cases present)
    | (solve | cases computed; have absent := application_no_startup joint.before _ _ _ (by assumption); rw [absent] at present; cases present)
    | (split at computed)
    | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at computed)
  all_goals
    rename_i inner accepted
    cases computed
    have actualEvent := startup_event joint.before _ inner accepted actual present
    rw [actualEvent] at received
    cases received
    refine ⟨_, by rw [result], parsed_input_bytes _ (by assumption), ?_, ?_⟩ <;>
      simp_all [CampusTCPFacts.startupKind, Produced.actor, Actor.other]

namespace F
export CampusTCPFacts (At DeliveryAt GatewayService StartupKind StartupDelivery StartupHistory)
end F

private theorem earlier_gateway (value : F.DeliveryAt report time actor) :
    ∃ service, service ∈ report.steps ∧ service.result.service = some value.receipt.served ∧
      value.receipt.served.time = service.before.time ∧ service.before.time < value.joint.step.before.time := by
  have selected := (CampusTCPFacts.deliver_origin value.joint.step value.service value.raw value.policy value.delivered
    value.receipt value.recorded).2.2
  obtain ⟨prior, later, same, preceding, _, _⟩ := CampusTCPFacts.step_origin report value.joint.step value.joint.member
  rcases CampusTCPOrigins.Trace.services_origin preceding value.receipt.served (List.mem_of_getElem? selected) with old | created
  · simp only [Input.initial, List.mem_nil_iff] at old
  · obtain ⟨service, member, present, time, earlier⟩ := created
    exact ⟨service, by rw [same]; simp [member], present, time, earlier⟩

theorem DeliveryAt.service_exists (value : F.DeliveryAt report time actor) : Nonempty (F.GatewayService value) := by
  obtain ⟨joint, member, recorded, time, earlier⟩ := earlier_gateway value
  obtain ⟨id, observed, completed, event, computed, ticket, before, _⟩ :=
    CampusTCPOrigins.service_origin joint value.receipt.served recorded
  obtain ⟨_, _, _, _, _, passed⟩ := CampusTCPFacts.serve_origin joint id observed event value.receipt.served recorded
  have received := (CampusTCPFacts.deliver_origin value.joint.step value.service value.raw value.policy value.delivered
    value.receipt value.recorded).1
  exact ⟨⟨⟨joint, member, time.symm⟩, recorded, id, observed, event, completed, computed, ticket, before, passed, by omega⟩⟩

private theorem packet_eq (first second : TCP.EstablishedReceive.Input) (same : first.bytes = second.bytes) :
    first = second := by
  have checked := first.checked
  rw [same, second.checked] at checked
  have packet := (Except.ok.inj checked).symm
  cases first
  cases second
  dsimp only at same packet
  cases same
  cases packet
  rfl

structure ReceiveAt (report : CampusTCPModel.Report input events) (actual : H.Step input.active input.passive) where
  joint : CampusTCPModel.Step input
  member : joint ∈ report.steps
  recorded : joint.result.startup = some actual
  index : Nat
  bytes : List UInt8
  policy : Bool
  delivered : joint.event = .deliver index bytes policy

theorem ReceiveAt.delivery_exists (value : ReceiveAt report actual)
    (received : ReceiveEvent actual.event actor kind value.bytes)
    (packet : TCP.EstablishedReceive.Input) (bytes : packet.bytes = value.bytes) :
    Nonempty (F.StartupDelivery report actual.index actor packet kind) := by
  obtain ⟨receipt, recorded, sameBytes, receiver, sourceKind⟩ :=
    Step.startup_receipt value.joint actual value.recorded value.index value.bytes value.policy value.delivered received
  have linked := Step.linked value.joint
  simp only [value.recorded] at linked
  let delivery : F.DeliveryAt report actual.index actor := {
    joint := ⟨value.joint, value.member, linked.2.1.symm⟩
    service := value.index
    raw := value.bytes
    policy := value.policy
    delivered := value.delivered
    receipt := receipt
    recorded := recorded
    received := packet
    same := packet_eq receipt.received packet (sameBytes.trans bytes.symm)
    receiver := receiver }
  obtain ⟨service⟩ := DeliveryAt.service_exists delivery
  exact ⟨⟨delivery, rfl, service, CampusTCPFacts.gateway_lineage delivery service, sourceKind⟩⟩

structure Ordinary (report : CampusTCPModel.Report input events) where
  opened : H.Step input.active input.passive
  syn : H.Step input.active input.passive
  synAck : H.Step input.active input.passive
  ack : H.Step input.active input.passive
  records : report.steps.filterMap (·.result.startup) = [opened, syn, synAck, ack]
  synAt : ReceiveAt report syn
  synAckAt : ReceiveAt report synAck
  ackAt : ReceiveAt report ack
  synEvent : syn.event = .listenSyn synAt.bytes .rewrite synAt.policy
  synAckEvent : synAck.event = .synSentSynAck synAckAt.bytes .rewrite synAckAt.policy
  ackEvent : ack.event = .synReceivedAck ackAt.bytes .rewrite

private theorem Chain.cons_parts (history : Chain first (head :: rest) final) :
    head.before = first ∧ Chain head.result.state rest final := by cases history; exact ⟨rfl, by assumption⟩

private theorem Chain.empty_parts (history : Chain first [] final) : first = final := by cases history; rfl

theorem Ordinary.history_exists (value : Ordinary report) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints) :
    Nonempty (F.StartupHistory report complete) := by
  have history := Report.startup_chain report
  rw [value.records, connection] at history
  have first := Chain.cons_parts history
  have second := Chain.cons_parts first.2
  have third := Chain.cons_parts second.2
  have fourth := Chain.cons_parts third.2
  have final := Chain.empty_parts fourth.2
  obtain ⟨⟨opened, openedState⟩, ⟨answered, answeredState⟩, ⟨acknowledged, acknowledgedState⟩⟩ :=
    TCPHandshake.four_step_stages value.opened value.syn value.synAck value.ack first.1 second.1 third.1 fourth.1 complete final
  have synComputed := value.syn.computed
  rw [second.1, openedState, value.synEvent] at synComputed
  obtain ⟨sameOpened, synIndex, synBytes⟩ :=
    TCPHandshake.answered_input_origin opened value.syn.index value.synAt.bytes .rewrite value.synAt.policy
      value.syn.result synComputed answered answeredState
  have synAckComputed := value.synAck.computed
  rw [third.1, answeredState, value.synAckEvent] at synAckComputed
  obtain ⟨sameAnswered, synAckIndex, synAckBytes⟩ :=
    TCPHandshake.acknowledged_input_origin answered value.synAck.index value.synAckAt.bytes .rewrite value.synAckAt.policy
      value.synAck.result synAckComputed acknowledged acknowledgedState
  have ackComputed := value.ack.computed
  rw [fourth.1, acknowledgedState, value.ackEvent] at ackComputed
  obtain ⟨times, synSpec, synAckSpec, ackBytes⟩ :=
    TCPHandshake.final_input_origin acknowledged value.ack.index value.ackAt.bytes .rewrite
      value.ack.result ackComputed complete final
  have synTime : complete.input.times.synReceived = value.syn.index := by rw [times]; simpa only [sameAnswered] using synIndex
  have synAckTime : complete.input.times.synAckReceived = value.synAck.index := by rw [times]; exact synAckIndex
  have ackTime : complete.input.times.ackReceived = value.ack.index := by rw [times]
  have synPacket : complete.certificate.syn.input.bytes = value.synAt.bytes := by
    rw [complete.certificate.syn.bytes, synSpec, sameAnswered]
    exact synBytes
  have synAckPacket : complete.certificate.synAck.input.bytes = value.synAckAt.bytes := by
    rw [complete.certificate.synAck.bytes, synAckSpec]
    exact synAckBytes
  have ackPacket : complete.certificate.ack.input.bytes = value.ackAt.bytes :=
    complete.certificate.ack.bytes.trans ackBytes
  obtain ⟨syn⟩ := value.synAt.delivery_exists (by rw [value.synEvent]; exact .syn _ _) complete.certificate.syn.input synPacket
  obtain ⟨synAck⟩ := value.synAckAt.delivery_exists (by rw [value.synAckEvent]; exact .synAck _ _) complete.certificate.synAck.input synAckPacket
  obtain ⟨ack⟩ := value.ackAt.delivery_exists (by rw [value.ackEvent]; exact .ack _) complete.certificate.ack.input ackPacket
  exact ⟨⟨synTime ▸ syn, synAckTime ▸ synAck, ackTime ▸ ack⟩⟩

end Netlib.Check.CampusTCPStartupOrigins
