import Netlib.Check.CampusTCPGapProgressDemand
import Netlib.Check.CampusTCPGapProgressDataState
import Netlib.Check.CampusTCPGapProgressServiceState

/-!
# Forward phases at actual held-gap cuts

Each move follows from current stored work and endpoint facts.
The next context retains actual packet identities and the first gap release.
-/

namespace Netlib.Check.CampusTCPGapProgressPhaseReverse

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)
open CampusTCPGapProgressWire (Geometry DataFields DataLinkFields AckFields)

namespace E
export CampusTCPGapProgressEvidence
  (DropLog dropID FirstReceipt AckOutput AckIngress AckTicket AckLink NeedRead Done)
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

theorem assign_ack_at (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.AckIngress initial allowance current monitor retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .assign record.output.index (native.ingress sender.other) ∧
      Nonempty (E.AckTicket initial native allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  obtain ⟨actual, ⟨assigned⟩⟩ := CampusTCPGapProgressNetwork.assign_at initial native current record.live.anchor
    record.output.index record.output.produced record.output.stored record.pending
  let cfg := config initial native quantum allowance
  have event : actual.event = .assign record.output.index (native.ingress sender.other) := by
    simpa only [record.output.actor] using assigned.facts.event
  have selected : M.nextAction cfg actual.before monitor = some (.assign record.output.index (native.ingress sender.other)) := by
    rw [assigned.facts.beforeEq]
    exact record.next_action native quantum
  have observed : M.observe cfg monitor actual = { monitor with
      phase := .ackTicket, refs := { monitor.refs with ackTicket := some assigned.ticket.id } } := by
    rw [F.observe_action cfg monitor actual record.waiting assigned.facts.supported assigned.facts.passed
      (.assign record.output.index (native.ingress sender.other)) selected event, M.advance, record.phaseEq]
    simp only [M.observeAssignment, CampusTCPRoundMonitorFacts.AssignmentFacts.find_new assigned.facts]
    rfl
  let live := assigned.live record.live
  have receipts : assigned.move.after.report.final.receipts = current.report.final.receipts := by
    rw [assigned.move.final, assigned.facts.frame]
  have retained : current.report.final.receipts <+: assigned.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  let output : E.AckOutput initial assigned.move.after :=
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
  · change native.ingress record.output.produced.actor = native.ingress sender.other
    rw [record.output.actor]
  · rw [observed]; exact record.outputRef
  · rw [observed]

private theorem option_eq {α : Type} {first second : Option α} (same : first.toList = second.toList) : first = second := by
  cases first <;> cases second <;> simp_all

private theorem history_first (next : CampusTCPGapProgressHistory.History cut after sender.other (lower ++ upper) true)
    (prior : CampusTCPGapProgressHistory.History cut current sender.other (lower ++ upper) true)
    (operations : applicationSteps after.endpoints sender.other = applicationSteps current.endpoints sender.other) :
    next.streams.first = prior.streams.first := by
  have same : next.operations = prior.operations := List.append_cancel_left
    (next.steps.symm.trans (operations.trans prior.steps))
  apply option_eq
  rw [← next.streams.releases, same, prior.streams.releases]

private theorem current_zone (initial : GapInitial cut sender lower upper)
    (gateway : CampusTCPGapProgressGateway.Current initial.gateway current) (actor : Actor) :
    gateway.session.entry.flow.zone actor.direction = input.zone := by
  rw [gateway.shape.entry, CampusTCPGapProgressWire.entry_eq initial]
  cases actor
  · exact initial.basis.aligned.originalZone
  · exact initial.basis.aligned.replyZone

theorem serve_ack_at (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.AckTicket initial native allowance current monitor retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .serve record.ticket.id none ∧
      Nonempty (E.AckLink initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  let cfg := config initial native quantum allowance
  have actor : record.ticket.value.produced.actor = sender.other := by rw [record.produced]; exact record.output.actor
  have fields : AckFields initial record.ticket.value.produced := by rw [record.produced]; exact record.output.fields
  have ready : CampusTCPService.ExistingDataReady (input.contextFor record.ticket.value.gateway)
      (beforeService input current.report.final record.ticket.value.gateway) record.ticket.value.source input.zone
      record.ticket.value.ingress ⟨record.live.gateway.session.entry.flow, sender.other.direction⟩
        record.live.gateway.session record.ticket.value.produced.actor.nextHop := by
    rw [record.standby, record.ingress, actor]
    exact record.live.gateway.existing_ready (native.paths sender.other)
      (CampusTCPGapProgressNetwork.service_environment record.live.anchor) record.ticket.value.source input.zone
      (fields.current_header record.live.gateway) (current_zone initial record.live.gateway sender.other)
      (Or.inr (fields.admission_ready record.live.gateway)) fields.ttl
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := CampusTCPGapProgressNetwork.serve_at initial native current
    record.live.anchor record.ticket record.pending record.standby
    ⟨record.live.gateway.session.entry.flow, sender.other.direction⟩ record.live.gateway.session ready
  have servedFields : AckFields initial served.ticket.value.produced := by rw [value.facts.ticket]; exact fields
  obtain ⟨live⟩ := record.live.ack_service value servedFields.payload (by
    rw [value.facts.ticket]
    exact fields.current_ack record.live.gateway)
  have selected : M.nextAction cfg actual.before monitor = some (.serve record.ticket.id) := by
    rw [value.facts.beforeEq]
    exact record.next_action quantum
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  have observed : M.observe cfg monitor actual = { monitor with phase := .ackLink, refs := {
      monitor.refs with ackService := some actual.before.services.length, ackLinkPacket := some packet } } := by
    rw [F.observe_action cfg monitor actual record.waiting value.facts.supported value.facts.passed
      (.serve record.ticket.id) selected value.facts.event, M.advance, record.phaseEq]
    simp only [M.observeService, value.facts.recorded, emitted, pending]
    rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    rw [value.move.final]
    exact value.facts.receipts
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  have firstOperation : live.history.streams.first = (retainFirst record.first retained).map (·.operation) := by
    rw [retainFirst_operation, ← record.firstOperation]
    exact history_first live.history record.live.history
      (congrArg (fun endpoints => applicationSteps endpoints sender.other) value.endpoints)
  have drops := silent_drops record.drops value.move (by simp only [E.dropID, value.facts.event])
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation
    index := actual.before.services.length, served, stored := ?_, emission, emitted, actor := ?_, application := ?_
    fields := servedFields, target := ?_, packetID := packet, custody := ?_, serviceRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef
  · rw [value.move.final, value.facts.beforeEq]
    exact value.facts.serviceIndex
  · rw [value.facts.ticket]
    exact actor
  · rw [value.facts.ticket, record.produced]
    exact record.output.application
  · rw [value.facts.target]
    change record.live.gateway.session.entry.flow.output sender.other.direction = _
    rw [record.live.gateway.shape.entry, CampusTCPGapProgressWire.output_tuple initial sender.other]
    cases sender <;> rfl
  · rw [value.move.final]
    exact pending
  · rw [observed]
  · rw [observed]

theorem deliver_ack_at (wire : Geometry initial) (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.AckLink initial allowance current monitor retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .deliver record.index record.emission.bytes true ∧
      Nonempty (E.NeedRead initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  let cfg := config initial native quantum allowance
  have twice : sender.other.other = sender := by cases sender <;> rfl
  have controls := CampusTCPRoundEmission.profile_controls
    (CampusTCPRoundEmission.emission_profile record.emission record.fields.profile)
  have tuple : record.emission.asInput.packet.header = (endpoint cut.endpoints sender).core.inbound := by
    change record.emission.decoded.header = _
    exact record.emission.header.trans record.target
  have sequence : record.emission.asInput.packet.segment.sequence = (endpoint cut.endpoints sender).core.receiveNext := by
    apply record.emission.control.1.trans
    change record.served.ticket.value.produced.source.packet.segment.sequence = _
    rw [record.fields.sequence, ← wire.peerComplete, ← wire.senderCursor]
  have acknowledgment : record.emission.asInput.packet.segment.acknowledgment = (endpoint cut.endpoints sender).core.sendNext := by
    apply record.emission.control.2.1.trans
    change record.served.ticket.value.produced.source.packet.segment.acknowledgment = _
    rw [record.fields.acknowledgment, wire.observed, ← wire.lowerSequence]
    exact (CampusTCPGapProgressSetup.initial_sender initial).sendNext.symm
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPGapProgressRetire.deliver_ack_at record.live record.index record.served
    record.stored record.emission record.emitted record.actor record.application record.pending tuple controls.1 controls.2
    sequence acknowledgment (record.emission.payload.trans record.fields.payload)
  let retired := CampusTCPGapProgressRetire.Retired.ofAck record.live value
  have event : actual.event = .deliver record.index record.emission.bytes true := value.actualEq.symm ▸ value.delivery.event
  have selected : M.nextAction cfg actual.before monitor = some (.deliver record.index record.emission.bytes true) := by
    rw [value.move.beforeEq]
    exact record.next_action native quantum
  have receiver : value.delivery.receipt.actor = sender := by
    have receiver := value.delivery.receipt.receiver
    rw [value.delivery.receiptService, record.actor, twice] at receiver
    exact receiver
  have recorded : actual.result.application = some (sender, value.delivery.localStep) := by
    simpa only [value.actualEq, record.actor, twice] using value.delivery.recorded
  have receiptAt : actual.result.receipt = some value.delivery.receipt := by
    simpa only [value.actualEq] using value.delivery.receiptAt
  have observed : M.observe cfg monitor actual = { monitor with phase := .needRead, refs := {
      monitor.refs with ackReceipt := some actual.before.receipts.length, ackReceiveStamp := some value.delivery.localStep.stamp } } := by
    rw [F.observe_action cfg monitor actual record.waiting value.move.supported value.move.passed
      (.deliver record.index record.emission.bytes true) selected event, M.advance, record.phaseEq]
    simp only [M.observeReceipt, receiptAt, recorded, Bool.false_eq_true, ite_false,
      show cfg.sender = sender from rfl, receiver, Bool.and_self]
    cases sender <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts ++ [value.delivery.receipt] := by
    rw [value.move.final]
    simpa only [value.actualEq] using value.delivery.receiptsHistory
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_append _ _
  have firstOperation : retired.history.streams.first = (retainFirst record.first retained).map (·.operation) := by
    rw [retainFirst_operation, ← record.firstOperation]
    rfl
  have drops := silent_drops record.drops value.move (by simp only [E.dropID, event])
  refine ⟨actual, value.move, event, ⟨{
    retired, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef

private theorem application_receipts (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.receipts = before.receipts := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem read_at (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (record : E.NeedRead initial allowance current monitor retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .read sender.other (lower ++ upper).length ∧
      Nonempty (E.Done initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries) := by
  let cfg := config initial native quantum allowance
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPGapProgressRetire.read_at record.retired
  let completed := CampusTCPGapProgressRetire.Completed.ofRead record.retired value
  have selected : M.nextAction cfg actual.before monitor = some (.read sender.other (lower ++ upper).length) := by
    rw [value.move.beforeEq]
    exact record.next_action native quantum
  have observed : M.observe cfg monitor actual = { monitor with phase := .done, refs := {
      monitor.refs with readStamp := some value.operation.stamp, readBytes := lower ++ upper } } := by
    rw [F.observe_action cfg monitor actual record.waiting value.move.supported value.move.passed
      (.read sender.other (lower ++ upper).length) selected value.event, M.advance, record.phaseEq]
    simp only [value.recorded, value.returned, show cfg.sender = sender from rfl,
      show cfg.bytes = lower ++ upper from rfl, beq_self_eq_true]
    cases sender <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    obtain ⟨effect, custody, computed, same⟩ := actual.processed
    rw [value.event] at computed
    have applied : applyApplication input actual.before sender.other (.read (lower ++ upper).length) = .ok effect := computed
    rw [value.move.final, same]
    exact (application_receipts actual.before sender.other (.read (lower ++ upper).length) effect applied).trans
      (congrArg State.receipts value.move.beforeEq)
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  have firstOperation : completed.history.streams.first = (retainFirst record.first retained).map (·.operation) := by
    rw [retainFirst_operation, ← record.firstOperation]
    rfl
  have drops := silent_drops record.drops value.move (by simp only [E.dropID, value.event])
  refine ⟨actual, value.move, value.event, ⟨{
    completed, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, bound := record.bound, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef

end Netlib.Check.CampusTCPGapProgressPhaseReverse
