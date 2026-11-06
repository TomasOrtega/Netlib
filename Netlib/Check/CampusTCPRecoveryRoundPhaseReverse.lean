import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPRecoveryRoundDataState
import Netlib.Check.CampusTCPRecoveryRoundServiceState
import Netlib.Check.CampusTCPRecoveryRoundMonitorFacts
import Netlib.Check.CampusTCPRoundEmission

namespace Netlib.Check.CampusTCPRecoveryRoundPhaseReverse

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move AckFields)
open CampusTCPRecoveryRoundEvidence

namespace M
export CampusTCPRecoveryRoundMonitor (Monitor observe)
end M
namespace R
export CampusTCPRoundMonitor (nextAction ingressAction ticketAction advance)
end R
namespace F
export CampusTCPRoundMonitorFacts (observe_action observeService_eq service_pending observeReceipt_eq advanceRead_eq)
end F
namespace N
export CampusTCPRecoveryRoundNetwork (assign_at serve_at)
end N
namespace D
export CampusTCPRecoveryRoundDataState (assignmentMonitor)
end D

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
variable {current after : Cut input complete} {monitor : M.Monitor} {sentAt retries : Nat}

private theorem option_eq {α : Type} {first second : Option α} (same : first.toList = second.toList) : first = second := by
  cases first <;> cases second <;> simp_all

private theorem history_first (next : CampusTCPRecoveryRoundHistory.History initial after released)
    (prior : CampusTCPRecoveryRoundHistory.History initial current released)
    (operations : applicationSteps after.endpoints .server = applicationSteps current.endpoints .server) :
    next.first = prior.first := by
  apply option_eq
  rw [← next.releases, operations, prior.releases]

private def mapFirst (first : Option (FirstReceipt initial current))
    (keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt → after.report.final.receipts[index]? = some receipt) :
    Option (FirstReceipt initial after) := first.map (fun receipt => receipt.reframe (keep _ _ receipt.stored))

private theorem mapFirst_index (first : Option (FirstReceipt initial current))
    (keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt → after.report.final.receipts[index]? = some receipt) :
    (mapFirst first keep).map (·.index) = first.map (·.index) := by cases first <;> rfl

private theorem mapFirst_operation (first : Option (FirstReceipt initial current))
    (keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt → after.report.final.receipts[index]? = some receipt) :
    (mapFirst first keep).map (·.operation) = first.map (·.operation) := by cases first <;> rfl

private theorem ticket_action (state : State input) (ticket : Work.Item (Ticket input.active input.passive))
    (member : ticket ∈ state.work.pending) : R.ticketAction state (some ticket.id) = some (.serve ticket.id) := by
  unfold CampusTCPRoundMonitor.ticketAction
  simp only [bind, Option.bind]
  cases found : state.work.pending.find? (fun item => item.id == ticket.id) with
  | none =>
    have absent := List.find?_eq_none.mp found ticket member
    exact False.elim (absent (beq_self_eq_true _))
  | some item => rfl

theorem assign_ack_at (native : NativeEnv initial) (quantum : Nat) (record : AckIngress initial current monitor sentAt retries) :
    ∃ actual : Step input, ∃ move : Move current actual,
      actual.event = .assign record.output.index native.ackIngress ∧
      Nonempty (AckTicket initial native move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) sentAt retries) := by
  let config := CampusTCPRecoveryRoundPhaseBase.config initial native quantum
  have next : R.nextAction config.toConfig current.report.final monitor.round = some (.assign record.output.index native.ackIngress) := by
    simp only [R.nextAction, record.phaseEq, R.ingressAction, record.outputRef, record.packetRef,
      record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
    rfl
  obtain ⟨actual, ⟨value⟩⟩ := N.assign_at initial native current record.live.anchor record.output.index native.ackIngress
    record.output.produced record.output.stored record.pending
  obtain ⟨observed, _, _⟩ := CampusTCPRecoveryRoundDataState.AssignmentMove.observe value config monitor .server
    record.waiting record.phaseEq next
  let live := record.live.assign value
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    rw [value.move.final, value.facts.frame]
  have keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt →
      value.move.after.report.final.receipts[index]? = some receipt := by intro index receipt stored; rw [receipts]; exact stored
  let first := mapFirst record.first keep
  have firstOperation : live.history.first = first.map (·.operation) := by
    rw [mapFirst_operation, ← record.firstOperation]
    exact history_first live.history record.live.history (congrArg (fun endpoints => applicationSteps endpoints .server) value.endpoints)
  have drops : DropLog initial value.move.after monitor.drops := by
    have log := record.drops.append value.move
    simpa only [dropID, value.facts.event, Option.toList_none, List.append_nil] using log
  let output : AckOutput initial value.move.after := {
    index := record.output.index, produced := record.output.produced
    stored := by rw [value.move.final, value.facts.frame]; exact record.output.stored
    actor := record.output.actor, application := record.output.application, fields := record.output.fields }
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_, first
    firstRef := ?_, firstOperation, output, ticket := value.ticket, pending := value.pending
    outputIndex := rfl, produced := rfl, primary := ?_, ingress := rfl, outputRef := ?_, ticketRef := ?_ }⟩⟩
  · rw [observed]; rfl
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, mapFirst_index]; exact record.firstRef
  · change current.report.final.owner record.output.produced.actor = .primary
    exact native.owner_at current.report.final record.live.anchor.environment record.output.produced.actor
  · rw [observed]; exact record.outputRef
  · rw [observed]; rfl

theorem serve_ack_at (native : NativeEnv initial) (quantum : Nat) (record : AckTicket initial native current monitor sentAt retries) :
    ∃ actual : Step input, ∃ move : Move current actual, actual.event = .serve record.ticket.id none ∧
      Nonempty (AckLink initial move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) sentAt retries) := by
  let config := CampusTCPRecoveryRoundPhaseBase.config initial native quantum
  have next : R.nextAction config.toConfig current.report.final monitor.round = some (.serve record.ticket.id) := by
    simp only [R.nextAction, record.phaseEq, record.ticketRef]
    exact ticket_action current.report.final record.ticket record.pending
  obtain ⟨seen⟩ := record.live.observed rfl
  have actor : record.ticket.value.produced.actor = .server := by rw [record.produced]; exact record.output.actor
  have fields : AckFields (complete := complete) (request := request) record.ticket.value.produced := by
    rw [record.produced]; exact record.output.fields
  have ready : CampusTCPService.ExistingDataReady (input.contextFor record.ticket.value.gateway)
      (beforeService input current.report.final record.ticket.value.gateway) record.ticket.value.source input.zone
      record.ticket.value.ingress ⟨initial.entry.flow, .reply⟩ seen.session record.ticket.value.produced.actor.nextHop := by
    rw [record.primary, record.ingress, actor]
    exact seen.ack_service_ready native (beforeService input current.report.final .primary)
      (initial.service_environment current.report.final record.live.anchor.environment) record.ticket.value.source
      fields.header record.live.gateway.valid record.live.gateway.records fields.profile fields.payload
      fields.sequence fields.acknowledgment fields.ttl
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final record.ticket.value.gateway := by
    rw [record.primary]
    exact native.service_phase_at current.report.final record.live.anchor.environment
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := N.serve_at initial current record.live.anchor record.ticket record.pending
    phase ⟨initial.entry.flow, .reply⟩ seen.session ready
  have servedFields : AckFields (complete := complete) (request := request) served.ticket.value.produced := by
    rw [value.facts.ticket]; exact fields
  obtain ⟨live⟩ := record.live.ack_service value record.primary servedFields
  have selected : R.nextAction config.toConfig actual.before monitor.round = some (.serve record.ticket.id) := by
    rw [value.facts.beforeEq]; exact next
  obtain ⟨packet, pending⟩ := F.service_pending actual served value.facts.recorded emission emitted
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round actual =
      { phase := .ackLink, refs := { monitor.round.refs with
        ackService := some actual.before.services.length, ackLinkPacket := some packet } } := by
    rw [F.observe_action config.toConfig monitor.round actual (.serve record.ticket.id)
      value.facts.supported value.facts.passed selected value.facts.event, R.advance, record.phaseEq]
    exact F.observeService_eq monitor.round actual .server .ackLink served value.facts.recorded emission emitted pending
  have observed : M.observe config monitor actual = { monitor with round := { phase := .ackLink, refs := {
      monitor.round.refs with ackService := some actual.before.services.length, ackLinkPacket := some packet } } } := by
    rw [CampusTCPRecoveryRoundMonitorFacts.observe_ordinary config monitor actual record.waiting value.facts.supported
      value.facts.passed (.serve record.ticket.id) value.facts.event]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, record.phaseEq]
    cases monitor.firstDataReceipt <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    rw [value.move.final]; exact value.facts.receipts
  have keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt →
      value.move.after.report.final.receipts[index]? = some receipt := by intro index receipt stored; rw [receipts]; exact stored
  let first := mapFirst record.first keep
  have firstOperation : live.history.first = first.map (·.operation) := by
    rw [mapFirst_operation, ← record.firstOperation]
    exact history_first live.history record.live.history (congrArg (fun endpoints => applicationSteps endpoints .server) value.endpoints)
  have drops : DropLog initial value.move.after monitor.drops := by
    have log := record.drops.append value.move
    simpa only [dropID, value.facts.event, Option.toList_none, List.append_nil] using log
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_, first,
    firstRef := ?_, firstOperation, index := actual.before.services.length, served,
    stored := ?_, emission, emitted, actor := ?_, application := ?_, fields := servedFields,
    target := value.facts.target, packetID := packet, custody := ?_, serviceRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, mapFirst_index]; exact record.firstRef
  · rw [value.move.final, value.facts.beforeEq]; exact value.facts.serviceIndex
  · rw [value.facts.ticket]; exact actor
  · rw [value.facts.ticket, record.produced]; exact record.output.application
  · rw [value.move.final]; exact pending
  · rw [observed]
  · rw [observed]

theorem deliver_ack_at (native : NativeEnv initial) (quantum : Nat) (record : AckLink initial current monitor sentAt retries) :
    ∃ actual : Step input, ∃ move : Move current actual,
      actual.event = .deliver record.index record.emission.bytes true ∧
      Nonempty (NeedRead initial move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) retries) := by
  let config := CampusTCPRecoveryRoundPhaseBase.config initial native quantum
  have next : R.nextAction config.toConfig current.report.final monitor.round =
      some (.deliver record.index record.emission.bytes true) := by
    simp only [R.nextAction, record.phaseEq, CampusTCPRoundMonitor.linkAction, record.serviceRef, record.packetRef,
      record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  have profile := CampusTCPRoundEmission.emission_profile record.emission record.fields.profile
  have controls := CampusTCPRoundEmission.profile_controls profile
  have tuple : record.emission.asInput.packet.header = complete.certificate.activeSeed.core.inbound := by
    change record.emission.decoded.header = _
    rw [record.emission.header, record.target, initial.aligned.clientOutput]
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPRecoveryRoundRetire.deliver_ack_at initial current record.live.anchor sentAt retries
    record.live.sender record.live.receiver record.index record.served record.stored record.emission record.emitted
    record.actor record.application record.pending tuple controls.1 controls.2
    (record.emission.control.1.trans record.fields.sequence)
    (record.emission.control.2.1.trans record.fields.acknowledgment) (record.emission.payload.trans record.fields.payload)
  let retired := record.live.retire value record.actor
  have event : actual.event = .deliver record.index record.emission.bytes true := value.actualEq.symm ▸ value.delivery.event
  have selected : R.nextAction config.toConfig actual.before monitor.round =
      some (.deliver record.index record.emission.bytes true) := by rw [value.move.beforeEq]; exact next
  have receiver : value.delivery.receipt.actor = .client := by
    have receiver := value.delivery.receipt.receiver
    rw [value.delivery.receiptService, record.actor] at receiver
    exact receiver
  have recorded : actual.result.application = some (.client, value.delivery.localStep) := by
    simpa only [value.actualEq, record.actor, Actor.other] using value.delivery.recorded
  have receiptAt : actual.result.receipt = some value.delivery.receipt := by
    simpa only [value.actualEq] using value.delivery.receiptAt
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round actual =
      { phase := .needRead, refs := { monitor.round.refs with
        ackReceipt := some actual.before.receipts.length, ackReceiveStamp := some value.delivery.localStep.stamp } } := by
    rw [F.observe_action config.toConfig monitor.round actual (.deliver record.index record.emission.bytes true)
      value.move.supported value.move.passed selected event, R.advance, record.phaseEq]
    exact F.observeReceipt_eq monitor.round actual .client .needRead value.delivery.receipt receiptAt receiver
      value.delivery.localStep recorded
  have observed : M.observe config monitor actual = { monitor with round := { phase := .needRead, refs := {
      monitor.round.refs with ackReceipt := some actual.before.receipts.length, ackReceiveStamp := some value.delivery.localStep.stamp } } } := by
    rw [CampusTCPRecoveryRoundMonitorFacts.observe_ordinary config monitor actual record.waiting value.move.supported
      value.move.passed (.deliver record.index record.emission.bytes true) event]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, record.phaseEq]
    cases monitor.firstDataReceipt <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts ++ [value.delivery.receipt] := by
    rw [value.move.final]
    simpa only [value.actualEq] using value.delivery.receiptsHistory
  have keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt →
      value.move.after.report.final.receipts[index]? = some receipt := by
    intro index receipt stored
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp stored
    rw [receipts, List.getElem?_append_left bound]
    exact stored
  let first := mapFirst record.first keep
  have firstOperation : retired.history.first = first.map (·.operation) := by
    rw [mapFirst_operation, ← record.firstOperation]
    apply history_first retired.history record.live.history
    simpa only [record.actor, Actor.other, reduceCtorEq, ite_false, List.append_nil] using
      CampusTCPRoundPhaseHistory.Move.delivery_history value.move value.delivery.toDelivery value.actualEq .server
  have drops : DropLog initial value.move.after monitor.drops := by
    have log := record.drops.append value.move
    simpa only [dropID, event, Option.toList_none, List.append_nil] using log
  refine ⟨actual, value.move, event, ⟨{
    retired, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_, first,
    firstRef := ?_, firstOperation }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, mapFirst_index]; exact record.firstRef

private theorem application_receipts (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.receipts = before.receipts := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

theorem read_at (native : NativeEnv initial) (quantum : Nat) (record : NeedRead initial current monitor retries) :
    ∃ actual : Step input, ∃ move : Move current actual, actual.event = .read .server request.bytes.length ∧
      Nonempty (Done initial move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) retries) := by
  let config := CampusTCPRecoveryRoundPhaseBase.config initial native quantum
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPRecoveryRoundRetire.read_at initial current record.retired.anchor retries
    record.retired.retirement record.retired.receiver
  let completed := record.retired.read value
  have next : R.nextAction config.toConfig actual.before monitor.round = some (.read .server request.bytes.length) := by
    simp only [R.nextAction, record.phaseEq]
    rfl
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round actual =
      { phase := .done, refs := { monitor.round.refs with readStamp := some value.operation.stamp, readBytes := request.bytes } } := by
    rw [F.observe_action config.toConfig monitor.round actual (.read .server request.bytes.length)
      value.move.supported value.move.passed next value.event]
    exact F.advanceRead_eq config.toConfig monitor.round record.phaseEq actual value.operation value.recorded value.returned
  have observed : M.observe config monitor actual = { monitor with round := { phase := .done, refs := {
      monitor.round.refs with readStamp := some value.operation.stamp, readBytes := request.bytes } } } := by
    rw [CampusTCPRecoveryRoundMonitorFacts.observe_ordinary config monitor actual record.waiting value.move.supported
      value.move.passed (.read .server request.bytes.length) value.event]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, record.phaseEq]
    cases monitor.firstDataReceipt <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    obtain ⟨effect, custody, computed, same⟩ := actual.processed
    rw [value.event] at computed
    have applied : applyApplication input actual.before .server (.read request.bytes.length) = .ok effect := computed
    rw [value.move.final, same]
    exact (application_receipts actual.before .server (.read request.bytes.length) effect applied).trans
      (congrArg State.receipts value.move.beforeEq)
  have keep : ∀ (index : Nat) (receipt : Receipt input), current.report.final.receipts[index]? = some receipt →
      value.move.after.report.final.receipts[index]? = some receipt := by intro index receipt stored; rw [receipts]; exact stored
  let first := mapFirst record.first keep
  have firstOperation : completed.history.first = first.map (·.operation) := by
    rw [mapFirst_operation, ← record.firstOperation]
    apply option_eq
    rw [← completed.history.releases]
    have operations := CampusTCPRoundPhaseHistory.Move.local_history value.move .server (.read request.bytes.length)
      (by rw [value.event]; exact .read _) value.operation value.recorded .server
    simp only [ite_true] at operations
    rw [operations, List.filter_append, record.retired.history.releases]
    have quiet : value.operation.releasedPayload = [] := by
      simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, value.localEvent]
    simp only [List.filter_cons, List.filter_nil, CampusTCPRecoveryRoundHistory.nonemptyRelease, quiet,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil]
  have drops : DropLog initial value.move.after monitor.drops := by
    have log := record.drops.append value.move
    simpa only [dropID, value.event, Option.toList_none, List.append_nil] using log
  refine ⟨actual, value.move, value.event, ⟨{
    completed, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_, first,
    firstRef := ?_, firstOperation }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, mapFirst_index]; exact record.firstRef

end

end Netlib.Check.CampusTCPRecoveryRoundPhaseReverse
