import Netlib.Check.CampusTCPRecoveryRoundReceiver
import Netlib.Check.CampusTCPTimedOldData
import Netlib.Check.CampusTCPRoundPhaseBase
import Netlib.Check.CampusTCPRoundAck

/-!
# Actual data receipts and ACK output in a recovery round

Current endpoint facts derive the next receive guards.
Each result appends its actual operation and retains the packet custody evidence.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundDelivery

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

namespace R
export CampusTCPRecoveryRoundReceiver (Facts)
end R
namespace D
export CampusTCPRoundDelivery (Delivery DataDelivered)
end D
namespace O
export CampusTCPTimedOldData (OldDataReady OldDataDelivered)
end O

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}

structure DataFields (initial : Initial report complete request) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) : Prop where
  actor : served.ticket.value.produced.actor = .client
  target : emission.target = initial.entry.flow.output .original
  sequence : served.ticket.value.source.packet.segment.sequence = input.active.iss.add 1
  acknowledgment : served.ticket.value.source.packet.segment.acknowledgment = input.passive.iss.add 1
  payload : served.ticket.value.source.packet.segment.payload = request.bytes
  profile : Admission.DataProfile served.ticket.value.source.packet.segment

theorem DataFields.packet (fields : DataFields initial served emission) :
    emission.asInput.packet.header = complete.certificate.passiveSeed.core.inbound ∧
      EstablishedReceive.control emission.asInput.packet.segment = none ∧
      Flags.ack emission.asInput.packet.segment.flags = true ∧
      emission.asInput.packet.segment.sequence = input.active.iss.add 1 ∧
      emission.asInput.packet.segment.acknowledgment = input.passive.iss.add 1 ∧
      emission.asInput.packet.segment.payload = request.bytes := by
  have controls := CampusTCPRoundEmission.profile_controls
    (CampusTCPRoundEmission.emission_profile emission fields.profile)
  refine ⟨?_, controls.1, controls.2, emission.control.1.trans fields.sequence,
    emission.control.2.1.trans fields.acknowledgment, emission.payload.trans fields.payload⟩
  change emission.decoded.header = complete.certificate.passiveSeed.core.inbound
  rw [emission.header, fields.target, initial.aligned.serverOutput]

private theorem application_frames (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.work = before.work ∧ effect.service = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem startup_work (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.state.work = before.work := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_work (before : State input) (event : Check.TCPHandshakeRecovery.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : effect.state.work = before.work := by
  unfold runRecovery at computed
  split at computed
  · cases computed; rfl
  · cases computed; rfl
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; rfl

private theorem delivery_work (delivery : D.Delivery report complete endpoints index served emission emitted) :
    delivery.step.result.state.work = report.final.work := by
  obtain ⟨effect, custody, computed, final⟩ := delivery.step.processed
  rw [delivery.event] at computed
  simp only [processCore] at computed
  have result : effect.state.work = delivery.step.before.work := by
    repeat' first
      | (solve | cases computed; dsimp only; exact (application_frames _ _ _ _ (by assumption)).1)
      | (solve | cases computed; dsimp only; exact startup_work _ _ _ (by assumption))
      | (solve | cases computed; dsimp only; exact recovery_work _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  simpa only [final, delivery.beforeEq] using result

private theorem delivery_custody (delivery : D.Delivery report complete endpoints index served emission emitted) :
    ∃ id, ∃ resolved : Theory.PacketCustody.Resolved delivery.step.before.custody id .delivered,
      delivery.step.before.custody.pendingID (Transit.linkAt index) = some id ∧
      Theory.PacketCustody.resolve delivery.step.before.custody id .delivered = .ok resolved ∧
      resolved.item.value.payload = .link index served emission emitted ∧
      delivery.step.result.state.custody = resolved.state ∧
      ∀ item ∈ delivery.step.result.state.custody.pending, item.id ≠ id := by
  obtain ⟨id, resolved, selected, resolution, payload, absent⟩ := delivery.consumed
  obtain ⟨effect, custody, _, prepared, final⟩ := delivery.step.transaction
  have output : effect.output = none := by simpa only [final] using delivery.noOutput
  have service : effect.service = none := by simpa only [final] using delivery.noService
  have custodyEq : custody = resolved.state := by
    simp only [prepareCustody, delivery.event, selected, resolution, Except.mapError, bind, Except.bind,
      payload, Transit.bytes, ite_true, pure, Except.pure, Except.ok.injEq] at prepared
    exact prepared.symm
  exact ⟨id, resolved, selected, resolution, payload, by
    simp only [final, finishCustody, output, service, custodyEq], absent⟩

def deliveryMove (current : Cut input complete)
    (delivery : D.Delivery current.report complete current.endpoints index served emission emitted) :
    Move current delivery.step :=
  let after : Cut input complete := ⟨_, delivery.append current.supported current.finished,
    delivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  ⟨after, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩

structure Received (initial : Initial report complete request) (current : Cut input complete) (released : Bool)
    (facts : R.Facts initial (endpoint current.endpoints .server) released)
    (index : Nat) (served : Served input) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) where
  fields : DataFields initial served emission
  delivery : D.Delivery current.report complete current.endpoints index served emission emitted
  move : Move current delivery.step
  selected : endpoint move.after.endpoints .server = delivery.after
  receiver : R.Facts initial (endpoint move.after.endpoints .server) true
  peer : endpoint move.after.endpoints .client = endpoint current.endpoints .client
  releasedBytes : Endpoint.receivedBytes (endpoint current.endpoints .server) emission.asInput =
    if released then [] else request.bytes
  localRelease : delivery.localStep.releasedPayload = if released then [] else request.bytes
  available : Endpoint.ResponseAvailable (endpoint move.after.endpoints .server) false
  pending : receiver.reaction.work.pending ≠ []
  fresh : released = false → ∃ value : D.DataDelivered current.report complete current.endpoints index served emission emitted,
    value.toDelivery = delivery
  old : released = true → ∃ value : O.OldDataDelivered current.report complete current.endpoints index served emission emitted facts.reaction,
    value.toDelivery = delivery
  work : delivery.step.result.state.work = current.report.final.work
  custody : ∃ id, ∃ resolved : Theory.PacketCustody.Resolved delivery.step.before.custody id .delivered,
    delivery.step.before.custody.pendingID (Transit.linkAt index) = some id ∧
    Theory.PacketCustody.resolve delivery.step.before.custody id .delivered = .ok resolved ∧
    resolved.item.value.payload = .link index served emission emitted ∧
    delivery.step.result.state.custody = resolved.state ∧
    ∀ item ∈ delivery.step.result.state.custody.pending, item.id ≠ id

private theorem receiver_pending (facts : R.Facts initial state true)
    (available : Endpoint.ResponseAvailable state false) : facts.reaction.work.pending ≠ [] := by
  have pending : facts.reaction.work.pending ≠ [] ∧ (false = true →
      ∃ due, facts.reaction.due = some due ∧ due ≤ state.now) := by
    simpa only [Endpoint.ResponseAvailable, facts.ackRuntime] using available
  exact pending.1

theorem deliver_data (current : Cut input complete)
    (facts : R.Facts initial (endpoint current.endpoints .server) released)
    (index : Nat) (served : Served input) (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (fields : DataFields initial served emission) :
    Nonempty (Received initial current released facts index served emission emitted) := by
  obtain ⟨tuple, controls, ack, sequence, acknowledgment, payload⟩ := fields.packet
  cases released with
  | false =>
    have ready : CampusTCPDeliveryEnabled.InOrderReady
        (endpoint current.endpoints served.ticket.value.produced.actor.other) emission.asInput facts.recovery facts.reaction := by
      simpa only [fields.actor, Actor.other] using facts.in_order_ready emission.asInput tuple controls ack sequence acknowledgment payload
    obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_data current.report complete current.endpoints
      current.connection index served found emission emitted application pending facts.recovery facts.reaction ready
    obtain ⟨after, computed, _, _, ⟨nextFacts⟩, _⟩ :=
      facts.receive_data emission.asInput tuple controls ack sequence acknowledgment payload
    have afterEq : delivery.after = after := by
      have computedLocal := congrArg Endpoint.Result.state delivery.localStep.computed
      rw [delivery.localBefore, delivery.localEvent] at computedLocal
      simp only [ApplicationTrace.evaluate, fields.actor, Actor.other] at computedLocal
      rw [computed] at computedLocal
      exact delivery.resultState.symm.trans computedLocal
    let move := deliveryMove current delivery.toDelivery
    have selected : endpoint move.after.endpoints .server = delivery.after := by
      simpa only [move, deliveryMove, fields.actor, Actor.other] using delivery.selected
    have receiver : R.Facts initial (endpoint move.after.endpoints .server) true := by
      rw [selected, afterEq]
      exact nextFacts
    have available : Endpoint.ResponseAvailable (endpoint move.after.endpoints .server) false := by
      rw [selected]
      exact delivery.available
    refine ⟨{
      fields, delivery := delivery.toDelivery, move, selected, receiver, peer := ?_, releasedBytes := ?_, localRelease := ?_
      available, pending := receiver_pending receiver available, fresh := fun _ => ⟨delivery, rfl⟩
      old := by intro impossible; cases impossible
      work := delivery_work delivery.toDelivery, custody := delivery_custody delivery.toDelivery }⟩
    · simpa only [move, deliveryMove, fields.actor, Actor.other] using delivery.peer
    · simpa only [fields.actor, Actor.other, payload, Bool.false_eq_true, ite_false] using delivery.released
    · simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload,
        delivery.localEvent, delivery.localBefore, delivery.resultState, delivery.received,
        fields.actor, Actor.other, facts.received, Bool.false_eq_true, ite_false,
        List.length_nil, List.drop_zero, List.nil_append, payload]
  | true =>
    obtain ⟨nonempty, ends, epoch⟩ := facts.old_geometry emission.asInput sequence payload
    have packetTuple : emission.asInput.packet.header = (endpoint current.endpoints .server).core.inbound := by
      simpa only [facts.core] using tuple
    have ready : O.OldDataReady (endpoint current.endpoints served.ticket.value.produced.actor.other)
        emission.asInput facts.reaction := by
      simpa only [fields.actor, Actor.other] using
        (⟨facts.coherent, facts.prepared, facts.storage, facts.ackRuntime, packetTuple, controls,
          nonempty, ends, epoch⟩ : O.OldDataReady (endpoint current.endpoints .server) emission.asInput facts.reaction)
    obtain ⟨delivery⟩ := CampusTCPTimedOldData.Report.deliver_old_data current.report complete current.endpoints
      current.connection index served found emission emitted application pending facts.reaction ready
    let move := deliveryMove current delivery.toDelivery
    have selected : endpoint move.after.endpoints .server = delivery.after := by
      simpa only [move, deliveryMove, fields.actor, Actor.other] using delivery.selected
    have receiver : R.Facts initial (endpoint move.after.endpoints .server) true := by
      rw [selected, delivery.afterEq]
      simpa only [fields.actor, Actor.other] using facts.sequence
    have available : Endpoint.ResponseAvailable (endpoint move.after.endpoints .server) false := by
      rw [selected]
      exact delivery.available_early
    refine ⟨{
      fields, delivery := delivery.toDelivery, move, selected, receiver, peer := ?_, releasedBytes := ?_
      localRelease := delivery.localReleased, available, pending := receiver_pending receiver available
      fresh := by intro impossible; cases impossible
      old := fun _ => ⟨delivery, rfl⟩
      work := delivery_work delivery.toDelivery, custody := delivery_custody delivery.toDelivery }⟩
    · simpa only [move, deliveryMove, fields.actor, Actor.other] using delivery.peer
    · simpa only [fields.actor, Actor.other, ite_true] using delivery.released

private theorem emitAck_frames (actual : Step input) (event : actual.event = .emitAck .server true) :
    actual.result.state.work = actual.before.work ∧ actual.result.service = none := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  rw [event] at computed
  have applied : applyApplication input actual.before .server (.emitAck true) = .ok effect := computed
  simpa only [final] using application_frames actual.before .server (.emitAck true) effect applied

private theorem emitAck_custody (facts : CampusTCPRoundAck.AckFacts before complete endpoints .server actual) :
    actual.result.state.custody = Theory.PacketCustody.mint before.custody (.ingress before.outputs.length facts.produced) := by
  obtain ⟨effect, custody, _, prepared, final⟩ := actual.transaction
  have service : effect.service = none := by
    simpa only [final] using (emitAck_frames actual facts.event).2
  have output : effect.output = some facts.produced := by simpa only [final] using facts.output
  have custodyEq : custody = actual.before.custody := by
    simp only [prepareCustody, facts.event, pure, Except.pure, Except.ok.injEq] at prepared
    exact prepared.symm
  simp only [final, finishCustody, output, service, custodyEq, facts.beforeEq]

def ackMove (current : Cut input complete) (actual : Step input)
    (facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints .server actual) : Move current actual :=
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished
    actual facts.beforeEq facts.supported
  let after : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _,
    rfl, facts.after, facts.connection⟩
  ⟨after, facts.beforeEq, facts.supported, facts.passed, rfl, rfl⟩

structure Acked (initial : Initial report complete request) (current : Cut input complete) where
  actual : Step input
  facts : CampusTCPRoundAck.AckFacts current.report.final complete current.endpoints .server actual
  move : Move current actual
  selected : endpoint move.after.endpoints .server = Endpoint.outputState (endpoint current.endpoints .server)
  receiver : R.Facts initial (endpoint move.after.endpoints .server) true
  peer : endpoint move.after.endpoints .client = endpoint current.endpoints .client
  fields : CampusTCPRoundPhaseBase.AckFields (complete := complete) (request := request) facts.produced
  work : actual.result.state.work = current.report.final.work
  custody : actual.result.state.custody = Theory.PacketCustody.mint current.report.final.custody
    (.ingress current.report.final.outputs.length facts.produced)

theorem emit_ack (current : Cut input complete)
    (receiver : R.Facts initial (endpoint current.endpoints .server) true)
    (pending : receiver.reaction.work.pending ≠ []) : Nonempty (Acked initial current) := by
  have available := Endpoint.responseAvailable_of_pending _ _ receiver.ackRuntime pending
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPRoundAck.Report.emitAck_enabled current.report complete current.endpoints
    current.connection .server receiver.prepared available
  let move := ackMove current actual facts
  have selected : endpoint move.after.endpoints .server = Endpoint.outputState (endpoint current.endpoints .server) := by
    simpa only [move, ackMove] using facts.selected
  refine ⟨{
    actual, facts, move, selected, receiver := ?_, peer := ?_, fields := ?_
    work := by simpa only [facts.beforeEq] using (emitAck_frames actual facts.event).1
    custody := emitAck_custody facts }⟩
  · rw [selected]
    exact receiver.output
  · simpa only [move, ackMove, Actor.other] using facts.peer
  · have fields := facts.source_fields
    refine ⟨?_, fields.2.1.trans receiver.sendNext, ?_, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2⟩
    · simpa only [receiver.core] using fields.1
    · simpa only [receiver.receiveNext, ite_true] using fields.2.2.1

end Netlib.Check.CampusTCPRecoveryRoundDelivery
