import Netlib.Check.CampusTCPGapProgressDemand
import Netlib.Check.CampusTCPGapProgressDataState
import Netlib.Check.CampusTCPGapProgressServiceState

/-!
# Forward phases at actual held-gap cuts

Each move follows from current stored work and endpoint facts.
The next context retains actual packet identities and the first gap release.
-/

namespace Netlib.Check.CampusTCPGapProgressPhaseForward

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)
open CampusTCPGapProgressWire (Geometry DataFields DataLinkFields AckFields)

namespace E
export CampusTCPGapProgressEvidence
  (DropLog dropID FirstReceipt Active DataOutput DataIngress DataTicket DataLink NeedAck AckOutput AckIngress)
end E
namespace M
export CampusTCPGapProgressMonitor (Monitor observe nextAction advance observeAssignment observeService observeReceipt observeOutput)
end M
namespace F
export CampusTCPGapProgressMonitorFacts (observe_action)
end F
namespace N
export CampusTCPGapProgressNetwork (AssignmentMove ServiceMove)
end N

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current after : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {monitor : M.Monitor} {allowance retries : Nat} {released : Bool}

private theorem silent_drops (log : E.DropLog cut current ids) (move : Move current actual)
    (quiet : E.dropID actual = none) : E.DropLog cut move.after ids := by
  simpa only [quiet, Option.toList_none, List.append_nil] using log.append move

private def retainFirst (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) : Option (E.FirstReceipt initial after) :=
  first.map fun receipt => receipt.reframe (by
    obtain ⟨extra, history⟩ := retained
    rw [← history, List.getElem?_append_left (List.getElem?_eq_some_iff.mp receipt.stored).1]
    exact receipt.stored)

private theorem retainFirst_index (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) :
    (retainFirst first retained).map (·.index) = first.map (·.index) := by cases first <;> rfl

private theorem retainFirst_operation (first : Option (E.FirstReceipt initial current))
    (retained : current.report.final.receipts <+: after.report.final.receipts) :
    (retainFirst first retained).map (·.operation) = first.map (·.operation) := by cases first <;> rfl

private theorem no_first (record : E.Active initial allowance current monitor retries false phase) : record.first = none := by
  have present := record.live.history.streams.present
  rw [record.firstOperation] at present
  cases selected : record.first with
  | none => rfl
  | some receipt => simp only [selected, Option.map_some, Option.isSome_some, Bool.true_eq_false] at present

private theorem active_first (record : E.Active initial allowance current monitor retries true phase) :
    ∃ first, record.first = some first := by
  have present := record.live.history.streams.present
  rw [record.firstOperation] at present
  cases selected : record.first with
  | none => simp only [selected, Option.map_none, Option.isSome_none, Bool.false_eq_true] at present
  | some receipt => exact ⟨receipt, rfl⟩

theorem assign_data_at (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.DataIngress initial allowance current monitor retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .assign record.output.index (native.ingress sender) ∧
      Nonempty (E.DataTicket initial native allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries released) := by
  obtain ⟨actual, ⟨assigned⟩⟩ := CampusTCPGapProgressNetwork.assign_at initial native current record.live.anchor
    record.output.index record.output.produced record.output.stored record.pending
  let cfg := config initial native quantum allowance
  have event : actual.event = .assign record.output.index (native.ingress sender) := by
    simpa only [record.output.actor] using assigned.facts.event
  have selected : M.nextAction cfg actual.before monitor = some (.assign record.output.index (native.ingress sender)) := by
    rw [assigned.facts.beforeEq]
    exact record.next_action native quantum
  have observed : M.observe cfg monitor actual = { monitor with
      phase := .dataTicket, refs := { monitor.refs with dataTicket := some assigned.ticket.id } } := by
    rw [F.observe_action cfg monitor actual record.waiting assigned.facts.supported assigned.facts.passed
      (.assign record.output.index (native.ingress sender)) selected event, M.advance, record.phaseEq]
    simp only [M.observeAssignment, CampusTCPRoundMonitorFacts.AssignmentFacts.find_new assigned.facts]
    rfl
  let live := assigned.live record.live
  have receipts : assigned.move.after.report.final.receipts = current.report.final.receipts := by
    rw [assigned.move.final, assigned.facts.frame]
  have retained : current.report.final.receipts <+: assigned.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  let output : E.DataOutput initial assigned.move.after :=
    ⟨record.output.index, record.output.produced, by rw [assigned.move.final, assigned.facts.frame]; exact record.output.stored,
      record.output.actor, record.output.application, record.output.fields⟩
  have drops := silent_drops record.drops assigned.move (by simp only [E.dropID, assigned.facts.event])
  refine ⟨actual, assigned.move, event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    output, ticket := assigned.ticket, pending := assigned.pending, outputIndex := rfl, produced := rfl
    standby := assigned.ticket_gateway, ingress := ?_, outputRef := ?_, ticketRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef
  · rw [retainFirst_operation]
    exact record.firstOperation
  · change native.ingress record.output.produced.actor = native.ingress sender
    rw [record.output.actor]
  · rw [observed]; exact record.outputRef
  · rw [observed]


theorem serve_data_at (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.DataTicket initial native allowance current monitor retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .serve record.ticket.id none ∧
      Nonempty (E.DataLink initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries released) := by
  let cfg := config initial native quantum allowance
  have fields : DataFields initial record.ticket.value.produced := by
    rw [record.produced]
    exact record.output.fields
  have actor : record.ticket.value.produced.actor = sender := by
    rw [record.produced]
    exact record.output.actor
  have zone : record.live.gateway.session.entry.flow.zone sender.direction = input.zone := by
    rw [record.live.gateway.shape.entry, initial.gateway.identity.entry, initial.basis.aligned.entryEq]
    cases sender
    · exact initial.basis.aligned.originalZone
    · exact initial.basis.aligned.replyZone
  let ready := record.live.gateway.repeated_ready (native.paths sender)
    (CampusTCPGapProgressNetwork.service_environment record.live.anchor) record.ticket.value.source input.zone
    (fields.current_header record.live.gateway) zone (fields.admission_ready record.live.gateway) fields.ttl
  have readyAt : CampusTCPService.ExistingRepeatedReady (input.contextFor record.ticket.value.gateway)
      (beforeService input current.report.final record.ticket.value.gateway) record.ticket.value.source input.zone
      record.ticket.value.ingress ⟨record.live.gateway.session.entry.flow, sender.direction⟩ record.live.gateway.session
      record.ticket.value.produced.actor.nextHop := by
    simpa only [record.standby, record.ingress, actor] using ready
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPGapProgressNetwork.serve_repeated_at
    initial native current record.live.anchor record.ticket record.pending record.standby
    ⟨record.live.gateway.session.entry.flow, sender.direction⟩ record.live.gateway.session readyAt
  have servedFields : DataFields initial served.ticket.value.produced := by
    rw [value.facts.ticket]
    exact fields
  obtain ⟨live⟩ := record.live.lower_service value rfl (servedFields.current_sequence record.live.gateway) servedFields.payload
  obtain ⟨packetID, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  have selected : M.nextAction cfg actual.before monitor = some (.serve record.ticket.id) := by
    rw [value.facts.beforeEq]
    exact record.next_action quantum
  have observed : M.observe cfg monitor actual = { monitor with phase := .dataLink, refs := { monitor.refs with
      dataService := some current.report.final.services.length, dataLinkPacket := some packetID } } := by
    rw [F.observe_action cfg monitor actual record.waiting value.facts.supported value.facts.passed
      (.serve record.ticket.id) selected value.facts.event, M.advance, record.phaseEq]
    simp only [M.observeService, value.facts.recorded, emitted, pending]
    rw [value.facts.beforeEq]
    rfl
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [value.move.final, value.facts.receipts]
    exact List.prefix_refl _
  have operations : live.history.operations = record.live.history.operations := by
    have same := live.history.steps
    rw [value.endpoints] at same
    have both := same.symm.trans record.live.history.steps
    simpa only [List.drop_left] using congrArg
      (fun steps => steps.drop (applicationSteps cut.endpoints sender.other).length) both
  have firstEq : live.history.streams.first = record.live.history.streams.first := by
    have same := live.history.streams.releases.symm.trans
      ((congrArg (fun steps => steps.filter CampusTCPRecoveryRoundHistory.nonemptyRelease) operations).trans
        record.live.history.streams.releases)
    cases first : live.history.streams.first <;> cases second : record.live.history.streams.first <;> simp_all
  have drops := silent_drops record.drops value.move (by simp only [E.dropID, value.facts.event])
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    index := current.report.final.services.length, served, stored := ?_, emission, emitted
    actor := ?_, application := ?_, fields := ⟨servedFields, ?_⟩
    packetID, custody := ?_, serviceRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef
  · rw [retainFirst_operation, firstEq]
    exact record.firstOperation
  · rw [value.move.final]
    exact value.facts.serviceIndex
  · rw [value.facts.ticket]
    exact actor
  · rw [value.facts.ticket, record.produced]
    exact record.output.application
  · calc
      emission.target = record.live.gateway.session.entry.flow.output sender.direction := value.facts.target
      _ = initial.gateway.seed.entry.flow.output sender.direction := by rw [record.live.gateway.shape.entry]
      _ = (endpoint cut.endpoints sender.other).core.inbound := CampusTCPGapProgressWire.output_tuple initial sender
  · rw [value.move.final, ← value.facts.beforeEq]
    exact pending
  · rw [observed]
  · rw [observed]

theorem deliver_data_at (wire : Geometry initial) (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.DataLink initial allowance current monitor retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .deliver record.index record.emission.bytes true ∧
      Nonempty (E.NeedAck initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  have controls := CampusTCPRoundEmission.profile_controls
    (CampusTCPRoundEmission.emission_profile record.emission record.fields.source.profile)
  have tuple : record.emission.asInput.packet.header = (CampusTCPGapProgressReceiver.source initial).core.inbound := by
    change record.emission.decoded.header = _
    exact record.emission.header.trans record.fields.target
  have sequence : record.emission.asInput.packet.segment.sequence = initial.lowerSource.attempt.output.packet.segment.sequence :=
    record.emission.control.1.trans (record.fields.source.sequence.trans wire.lowerSequence.symm)
  have ackOld : Seq.distance record.emission.asInput.packet.segment.acknowledgment
      (CampusTCPGapProgressReceiver.source initial).core.sendUna ≤ EstablishedReceive.maxSendWindow := by
    rw [show record.emission.asInput.packet.segment.acknowledgment =
      record.served.ticket.value.source.packet.segment.acknowledgment from record.emission.control.2.1]
    exact record.fields.source.ack_old wire
  have payload : record.emission.asInput.packet.segment.payload = lower :=
    record.emission.payload.trans record.fields.source.payload
  obtain ⟨received⟩ := CampusTCPGapProgressDataState.receive_at record.live record.index record.served record.stored
    record.emission record.emitted record.application record.pending record.actor tuple controls.1 controls.2 sequence ackOld payload
  let cfg := config initial native quantum allowance
  have selected : M.nextAction cfg received.delivery.step.before monitor =
      some (.deliver record.index record.emission.bytes true) := by
    rw [received.delivery.beforeEq]
    exact record.next_action native quantum
  have observed : M.observe cfg monitor received.delivery.step = { monitor with
      phase := .needAck
      refs := { monitor.refs with
        dataReceipt := some received.delivery.step.before.receipts.length, dataReceiveStamp := some received.delivery.localStep.stamp }
      firstDataReceipt := match monitor.firstDataReceipt with
        | some previous => some previous
        | none => some received.delivery.step.before.receipts.length } := by
    rw [F.observe_action cfg monitor received.delivery.step record.waiting received.delivery.supported received.delivery.passed
      (.deliver record.index record.emission.bytes true) selected received.delivery.event, M.advance, record.phaseEq]
    simp only [M.observeReceipt, received.delivery.receiptAt, received.delivery.recorded,
      received.delivery.receipt.receiver, received.delivery.receiptService, record.actor]
    cases sender <;> rfl
  have receipts : received.move.after.report.final.receipts = current.report.final.receipts ++ [received.delivery.receipt] := by
    rw [received.move.final]
    exact received.delivery.receiptsHistory
  have retained : current.report.final.receipts <+: received.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_append _ _
  have firstEvidence : ∃ first : Option (E.FirstReceipt initial received.move.after),
      (M.observe cfg monitor received.delivery.step).firstDataReceipt = first.map (·.index) ∧
      received.next.history.streams.first = first.map (·.operation) := by
    cases released with
    | false =>
      have oldFirst := no_first record.toActive
      have oldRef : monitor.firstDataReceipt = none := by rw [record.firstRef, oldFirst]; rfl
      let first : E.FirstReceipt initial received.move.after := {
        index := received.delivery.step.before.receipts.length
        receipt := received.delivery.receipt
        stored := by
          rw [receipts, received.delivery.beforeEq, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self, List.getElem?_cons_zero]
        operation := received.delivery.localStep
        application := received.delivery.receiptStep
        actor := by rw [received.delivery.receiptService]; exact record.actor
        released := received.localRelease }
      refine ⟨some first, ?_, ?_⟩
      · rw [observed, oldRef]
        rfl
      · rw [received.first]
        rfl
    | true =>
      obtain ⟨old, previous⟩ := active_first record.toActive
      have oldRef : monitor.firstDataReceipt = some old.index := by
        simpa only [previous, Option.map_some] using record.firstRef
      refine ⟨retainFirst record.first retained, ?_, ?_⟩
      · rw [observed, oldRef, retainFirst_index]
        simp only [previous, Option.map_some]
      · rw [received.first, retainFirst_operation]
        exact record.firstOperation
  obtain ⟨first, firstRef, firstOperation⟩ := firstEvidence
  have drops := silent_drops record.drops received.move (by simp only [E.dropID, received.delivery.event])
  refine ⟨received.delivery.step, received.move, received.delivery.event, ⟨{
    live := received.next, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first, firstRef, firstOperation, pending := received.pending }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops

private theorem application_receipts (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.receipts = before.receipts := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_receipts {live : CampusTCPGapProgressState.Live initial current retries true}
    (acked : CampusTCPGapProgressDataState.Acked live actual) :
    acked.move.after.report.final.receipts = current.report.final.receipts := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  have applied : applyApplication input actual.before sender.other (.emitAck true) = .ok effect := by
    simpa only [acked.facts.event, processCore] using computed
  simpa only [acked.move.final, final, acked.facts.beforeEq] using application_receipts _ _ _ _ applied

theorem emit_ack_at (wire : Geometry initial) (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.NeedAck initial allowance current monitor retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .emitAck sender.other true ∧
      Nonempty (E.AckIngress initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  obtain ⟨actual, ⟨acked⟩⟩ := CampusTCPGapProgressDataState.ack_at record.live record.pending
  let cfg := config initial native quantum allowance
  have actor : acked.facts.produced.actor = sender.other := by rw [acked.facts.production]; rfl
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.output_pending actual acked.facts.produced acked.facts.output
  have selected : M.nextAction cfg actual.before monitor = some (.emitAck sender.other true) := by
    rw [acked.facts.beforeEq]
    exact record.next_action native quantum
  have observed : M.observe cfg monitor actual = { monitor with
      phase := .ackIngress, refs := { monitor.refs with
        ackOutput := some actual.before.outputs.length, ackIngressPacket := some packetID } } := by
    rw [F.observe_action cfg monitor actual record.waiting acked.facts.supported acked.facts.passed
      (.emitAck sender.other true) selected acked.facts.event, M.advance, record.phaseEq]
    simp only [M.observeOutput, acked.facts.output, actor, custody]
    cases sender <;> rfl
  have fields : AckFields initial acked.facts.produced := by
    rw [acked.facts.production]
    apply CampusTCPGapProgressWire.ack_fields wire acked.facts.localStep acked.facts.packet acked.facts.origin
    · rw [acked.facts.localBefore]
      exact record.live.receiverFacts
    · rw [acked.facts.localBefore]
      exact acked.facts.encoded
  have receipts := ack_receipts acked
  have retained : current.report.final.receipts <+: acked.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  let output : E.AckOutput initial acked.move.after :=
    ⟨actual.before.outputs.length, acked.facts.produced, by
      rw [acked.move.final, acked.facts.beforeEq]
      exact acked.facts.source, actor, by rw [acked.facts.production]; trivial, fields⟩
  have drops := silent_drops record.drops acked.move (by simp only [E.dropID, acked.facts.event])
  refine ⟨actual, acked.move, acked.facts.event, ⟨{
    live := acked.next, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    output, packetID, custody := ?_, outputRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef
  · rw [acked.first, retainFirst_operation]
    exact record.firstOperation
  · rw [acked.move.final]
    exact custody
  · rw [observed]
  · rw [observed]

end Netlib.Check.CampusTCPGapProgressPhaseForward
