import Netlib.Check.CampusTCPFacts
import Netlib.Check.CampusTCPRecoveryStartupOrigins

/-!
# Startup records in one actual campus history

Ordinary histories specialize the actual sum of startup modes.
The projection does not run the endpoints again.
-/

namespace Netlib.Check.CampusTCPStartupOrigins

open Packet Protocol CampusTCPModel
namespace H
export Check.TCPHandshake (Stage Step Completed Opened Answered Acknowledged Event)
end H
namespace R
export CampusTCPRecoveryStartupOrigins (Stage Linked stage)
end R

variable {input : Input}

export CampusTCPRecoveryStartupOrigins (stage)

theorem Step.linked (actual : CampusTCPModel.Step input) : R.Linked actual.before actual.event actual.result :=
  CampusTCPRecoveryStartupOrigins.Step.linked actual

abbrev StartupChain := @CampusTCPRecoveryStartupOrigins.Chain

theorem Trace.startup_chain (trace : CampusTCPModel.Trace input initial events steps final remaining) :
    CampusTCPRecoveryStartupOrigins.Chain (stage initial.connection) steps (stage final.connection) :=
  CampusTCPRecoveryStartupOrigins.Trace.startup_chain trace

theorem Report.startup_chain (report : CampusTCPModel.Report input events) :
    CampusTCPRecoveryStartupOrigins.Chain (.ordinary .idle) report.steps (stage report.final.connection) :=
  CampusTCPRecoveryStartupOrigins.Report.startup_chain report

inductive Chain : H.Stage active passive → List (H.Step active passive) → H.Stage active passive → Prop where
  | done (value) : Chain value [] value
  | next (head : H.Step active passive) (tail : Chain head.result.state rest final) :
      Chain head.before (head :: rest) final

private theorem evaluated_idle (before : H.Stage active passive) (index : Nat) (event : H.Event)
    (result : TCPHandshake.Effect active passive)
    (computed : TCPHandshake.evaluate active passive before index event = .ok result)
    (idle : result.state = .idle) : before = .idle := by
  cases before <;> cases event <;> simp only [TCPHandshake.evaluate] at computed
  all_goals repeat' first
    | (solve | rfl)
    | (solve | cases computed)
    | (solve | cases computed; cases idle)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem idle_event (actual : H.Step active passive) (idle : actual.result.state = .idle)
    (supported : actual.supported = true) : ∃ remote policy, actual.event = .activeOpen remote policy := by
  have before := evaluated_idle _ _ _ _ actual.computed idle
  have computed := actual.computed
  rw [before] at computed
  cases event : actual.event with
  | activeOpen remote policy => exact ⟨remote, policy, rfl⟩
  | listenSyn bytes path policy | synSentSynAck bytes path policy | synReceivedAck bytes path =>
    rw [event] at computed
    simp only [TCPHandshake.evaluate] at computed
    have decision : actual.result.decision = .phase :=
      congrArg TCPHandshake.Effect.decision (Except.ok.inj computed).symm
    simp only [TCPHandshake.Step.supported, decision, Bool.false_eq_true] at supported

private def Closed : R.Stage active passive → Prop
  | .recovering _ => True
  | .ordinary (.complete _) => True
  | _ => False

private theorem linked_closed (linked : R.Linked before event effect) (closed : Closed (stage before.connection)) :
    effect.startup = none ∧ Closed (stage effect.state.connection) := by
  cases linked with
  | quiet ordinary recovery same => exact ⟨ordinary, by rw [same]; exact closed⟩
  | ordinary actual recorded recovery prior after stamp pending supported =>
    rw [prior] at closed
    cases phase : actual.before <;> simp only [phase, Closed] at closed
    all_goals first
      | exact False.elim closed
      | (rw [phase] at pending; cases pending)
  | recovery actual recorded ordinary prior after stamp => exact ⟨ordinary, by rw [after]; trivial⟩
  | drain archive ordinary recovery event prior after retained stamp => exact ⟨ordinary, by rw [after]; trivial⟩

private theorem trace_closed (trace : CampusTCPModel.Trace input initial events steps final remaining) :
    Closed (stage initial.connection) → steps.filterMap (·.result.startup) = [] ∧ Closed (stage final.connection) := by
  induction trace with
  | done state => intro closed; exact ⟨rfl, closed⟩
  | stop head blocked tail =>
    intro closed
    obtain ⟨absent, after⟩ := linked_closed (Step.linked head) closed
    exact ⟨by simp [absent], after⟩
  | next head supported rest ih =>
    intro closed
    obtain ⟨absent, after⟩ := linked_closed (Step.linked head) closed
    obtain ⟨records, final⟩ := ih after
    exact ⟨by simp [absent, records], final⟩

private def Opens (actual : H.Step active passive) : Prop :=
  ∃ remote policy, actual.event = .activeOpen remote policy

private theorem ordinary_or_opens (trace : CampusTCPModel.Trace input initial events steps final remaining) :
    ∀ first, stage initial.connection = .ordinary first →
      (∃ last, stage final.connection = .ordinary last ∧ Chain first (steps.filterMap (·.result.startup)) last) ∨
        (first = .idle ∧ ∀ actual ∈ steps.filterMap (·.result.startup), Opens actual) := by
  induction trace with
  | done state => intro first start; exact Or.inl ⟨first, start, .done first⟩
  | stop head blocked tail =>
    intro first start
    cases linked : Step.linked head with
    | quiet ordinary recovery same => exact Or.inl ⟨first, same.trans start, by simp [ordinary]; exact .done first⟩
    | ordinary actual recorded recovery prior after stamp pending supported =>
      have same : actual.before = first := by cases prior.symm.trans start; rfl
      exact Or.inl ⟨actual.result.state, after, by simp [recorded, ← same]; exact .next actual (.done _)⟩
    | recovery actual recorded ordinary prior after stamp =>
      rcases prior with impossible | ⟨idle, seeded⟩
      · rw [start] at impossible; cases impossible
      · exact Or.inr ⟨(by cases start.symm.trans idle; rfl), by simp [ordinary]⟩
    | drain archive ordinary recovery event prior after retained stamp =>
      rw [prior] at start; cases start
  | next head supported rest ih =>
    intro first start
    cases linked : Step.linked head with
    | quiet ordinary recovery same =>
      simpa [ordinary] using ih first (same.trans start)
    | ordinary actual recorded recovery prior after stamp pending accepted =>
      have same : actual.before = first := by cases prior.symm.trans start; rfl
      rcases ih actual.result.state after with ⟨last, final, history⟩ | ⟨idle, opens⟩
      · exact Or.inl ⟨last, final, by simp only [List.filterMap_cons, recorded]; rw [← same]; exact .next actual history⟩
      · have before := evaluated_idle _ _ _ _ actual.computed idle
        have opened : Opens actual := idle_event actual idle (accepted ▸ supported)
        refine Or.inr ⟨same.symm.trans before, ?_⟩
        intro selected member
        simp only [List.filterMap_cons, recorded, List.mem_cons] at member
        rcases member with rfl | member
        · exact opened
        · exact opens selected member
    | recovery actual recorded ordinary prior after stamp =>
      rcases prior with impossible | ⟨idle, seeded⟩
      · rw [start] at impossible; cases impossible
      · have closed : Closed (stage head.result.state.connection) := by rw [after]; trivial
        have absent := (trace_closed rest closed).1
        exact Or.inr ⟨by cases start.symm.trans idle; rfl, by simp [ordinary, absent]⟩
    | drain archive ordinary recovery event prior after retained stamp =>
      rw [prior] at start; cases start

theorem Step.ordinary_linked (actual : CampusTCPModel.Step input) (head : H.Step input.active input.passive)
    (recorded : actual.result.startup = some head) :
    stage actual.before.connection = .ordinary head.before ∧ head.index = actual.before.time ∧
      stage actual.result.state.connection = .ordinary head.result.state := by
  cases Step.linked actual with
  | quiet absent recovery same => rw [absent] at recorded; cases recorded
  | ordinary selected present recovery prior after stamp pending supported =>
    have same := Option.some.inj (present.symm.trans recorded)
    subst selected
    exact ⟨prior, stamp, after⟩
  | recovery selected present absent prior after stamp => rw [absent] at recorded; cases recorded
  | drain archive absent recovery event prior after retained stamp => rw [absent] at recorded; cases recorded

private theorem application_no_startup (before : State input) (actor : Actor)
    (event : TCP.ApplicationTrace.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : effect.startup = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)

private theorem recovery_no_startup (before : State input) (event : C.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : effect.startup = none := by
  cases connected : before.connection with
  | startup value pending | application value pending =>
    simp only [runRecovery, connected, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    rfl
  | recovering current =>
    simp only [runRecovery, connected] at computed
    split at computed
    · cases computed
    · split at computed
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst effect
        rfl

private theorem startup_event (before : State input) (event : H.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) (actual : H.Step input.active input.passive)
    (recorded : effect.startup = some actual) : actual.event = event := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; cases recorded; rfl)
    | (solve | cases computed; simp [unsupported] at recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [pure, Except.pure] at computed)

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
    | (solve | cases computed; have absent := recovery_no_startup joint.before _ _ (by assumption); rw [absent] at present; cases present)
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
  have linked := Step.ordinary_linked value.joint actual value.recorded
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
  have history : Chain .idle (report.steps.filterMap (·.result.startup)) (.complete complete) := by
    rcases ordinary_or_opens report.trace .idle rfl with ⟨last, final, history⟩ | ⟨idle, opens⟩
    · have completed : stage report.final.connection = .ordinary (.complete complete) := by rw [connection]; rfl
      have same : last = .complete complete := by cases final.symm.trans completed; rfl
      exact same ▸ history
    · obtain ⟨remote, policy, event⟩ := opens value.syn (by rw [value.records]; simp)
      rw [value.synEvent] at event
      cases event
  rw [value.records] at history
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

theorem Trace.recovering_startup_opens (trace : CampusTCPModel.Trace input initial events steps final remaining)
    (start : stage initial.connection = .ordinary .idle) (connection : final.connection = .recovering current) :
    ∀ actual ∈ steps.filterMap (·.result.startup), ∃ remote policy, actual.event = .activeOpen remote policy := by
  rcases ordinary_or_opens trace .idle start with ⟨last, ended, _⟩ | ⟨_, opens⟩
  · rw [connection] at ended
    cases ended
  · exact opens

theorem Report.recovering_startup_opens (report : CampusTCPModel.Report input events)
    (connection : report.final.connection = .recovering current) :
    ∀ actual ∈ report.steps.filterMap (·.result.startup), ∃ remote policy, actual.event = .activeOpen remote policy :=
  Trace.recovering_startup_opens report.trace rfl connection

end Netlib.Check.CampusTCPStartupOrigins
