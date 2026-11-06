import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPRecoveryRoundDataState
import Netlib.Check.CampusTCPRecoveryRoundServiceState

/-!
# Forward phases at actual recovery-round cuts

Each constructor derives its next action from the current stored facts.
The returned move retains actual drops, packet references, and the first data receipt.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundPhaseForward

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move OriginalFields)
open CampusTCPRecoveryRoundPhaseBase (config)
open CampusTCPRecoveryRoundState (Live)

namespace E
export CampusTCPRecoveryRoundEvidence
  (DropLog dropID FirstReceipt Active NeedSend DataOutput DataIngress DataTicket DataLink NeedAck AckOutput AckIngress)
end E
namespace M
export CampusTCPRecoveryRoundMonitor (Monitor observe)
end M
namespace R
export CampusTCPRoundMonitor (nextAction observeService linkAction)
end R
namespace F
export CampusTCPRoundMonitorFacts (observe_action observeService_eq service_pending)
end F
namespace N
export CampusTCPRecoveryRoundNetwork (AssignmentMove ServiceMove)
end N
namespace D
export CampusTCPRecoveryRoundDataState (assignmentMonitor receiptMonitor ackMonitor)
end D

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current after : Cut input complete} {monitor : M.Monitor}
variable {sentAt retries : Nat} {released : Bool}

private theorem silent_drops (log : E.DropLog initial current ids) (move : Move current actual)
    (quiet : E.dropID actual = none) : E.DropLog initial move.after ids := by
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

private theorem history_first (left : CampusTCPRecoveryRoundHistory.History initial after released)
    (right : CampusTCPRecoveryRoundHistory.History initial current released)
    (same : (applicationSteps after.endpoints .server).filter CampusTCPRecoveryRoundHistory.nonemptyRelease =
      (applicationSteps current.endpoints .server).filter CampusTCPRecoveryRoundHistory.nonemptyRelease) :
    left.first = right.first := by
  rw [left.releases, right.releases] at same
  cases a : left.first <;> cases b : right.first <;> simp_all

private theorem no_first (history : CampusTCPRecoveryRoundHistory.History initial current false) : history.first = none := by
  have present := history.present
  cases first : history.first with
  | none => rfl
  | some operation => simp only [first, Option.isSome_some, Bool.true_eq_false] at present

private theorem history_first_some (history : CampusTCPRecoveryRoundHistory.History initial after true)
    (releases : (applicationSteps after.endpoints .server).filter CampusTCPRecoveryRoundHistory.nonemptyRelease = [operation]) :
    history.first = some operation := by
  rw [history.releases] at releases
  cases first : history.first <;> simp_all

private theorem active_first (record : E.Active initial current monitor sentAt retries true phase) :
    ∃ first, record.first = some first := by
  cases selected : record.first with
  | none =>
    have same := record.firstOperation
    rw [selected, Option.map_none] at same
    have present := record.live.history.present
    rw [same] at present
    cases present
  | some receipt => exact ⟨receipt, rfl⟩

theorem send_at (native : NativeEnv initial) (quantum : Nat) (record : E.NeedSend initial current monitor) :
    ∃ actual, ∃ move : Move current actual, actual.event = .send .client request.bytes.length true ∧
      Nonempty (E.DataIngress initial move.after (M.observe (config initial native quantum) monitor actual)
        (endpoint current.endpoints .client).now 0 false) := by
  obtain ⟨actual, ⟨sent⟩⟩ := CampusTCPRecoveryRoundSend.send_at initial native current record.placement quantum
  let live := Live.ofSend sent record.placement
  have observed : M.observe (config initial native quantum) monitor actual =
      { round := { phase := .dataIngress, refs := {
        dataOutput := some actual.before.outputs.length, dataIngressPacket := some sent.packetID } } } := by
    rw [record.monitorEq]
    exact sent.observed
  have drops := silent_drops ((Netlib.Check.CampusTCPRecoveryRoundEvidence.DropLog.ofInitial initial).clock record.placement) sent.move
    (by simp only [E.dropID, sent.event])
  have actor : sent.application.produced.actor = .client := by rw [sent.application.production]; rfl
  refine ⟨actual, sent.move, sent.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_
    first := none, firstRef := ?_, firstOperation := ?_
    output := ⟨actual.before.outputs.length, sent.application.produced, sent.source, actor, ?_, sent.fields⟩
    packetID := sent.packetID, custody := sent.custody, outputRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed] <;> rfl
  · rw [observed] <;> rfl
  · rw [observed] <;> rfl
  · rw [observed] <;> rfl
  · rw [observed]
    exact drops
  · rw [observed] <;> rfl
  · exact no_first live.history
  · rw [sent.application.production]
    trivial
  · rw [observed] <;> rfl
  · rw [observed] <;> rfl

theorem assign_data_at (native : NativeEnv initial) (quantum : Nat)
    (record : E.DataIngress initial current monitor sentAt retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .assign record.output.index native.dataIngress ∧
      Nonempty (E.DataTicket initial native move.after (M.observe (config initial native quantum) monitor actual) sentAt retries released) := by
  obtain ⟨actual, ⟨assigned⟩⟩ := CampusTCPRecoveryRoundNetwork.assign_at initial native current record.live.anchor
    record.output.index native.dataIngress record.output.produced record.output.stored record.pending
  have next : R.nextAction (config initial native quantum).toConfig current.report.final monitor.round =
      some (.assign record.output.index native.dataIngress) := by
    simp only [R.nextAction, record.phaseEq, record.outputRef, record.packetRef, CampusTCPRoundMonitor.ingressAction,
      record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
    rfl
  obtain ⟨observed, _, _⟩ := CampusTCPRecoveryRoundDataState.AssignmentMove.observe assigned
    (config initial native quantum) monitor .client record.waiting record.phaseEq next
  let live := record.live.assign assigned
  have receipts : assigned.move.after.report.final.receipts = current.report.final.receipts := by
    rw [assigned.move.final, assigned.facts.frame]
  have retained : current.report.final.receipts <+: assigned.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  have firstSame : live.history.first = record.live.history.first := history_first live.history record.live.history (by rw [assigned.endpoints])
  let output : E.DataOutput initial assigned.move.after :=
    ⟨record.output.index, record.output.produced, by rw [assigned.move.final, assigned.facts.frame]; exact record.output.stored,
      record.output.actor, record.output.application, record.output.fields⟩
  have drops := silent_drops record.drops assigned.move (by simp only [E.dropID, assigned.facts.event])
  refine ⟨actual, assigned.move, assigned.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    output, ticket := assigned.ticket, pending := assigned.pending, outputIndex := rfl, produced := rfl
    primary := ?_, ingress := rfl, outputRef := ?_, ticketRef := ?_ }⟩⟩
  · rw [observed] <;> rfl
  · rw [observed]
    exact record.waiting
  · rw [observed]
    exact record.retryCount
  · rw [observed]
    exact record.dropCount
  · rw [observed]
    exact drops
  · rw [observed, retainFirst_index]
    exact record.firstRef
  · rw [firstSame, retainFirst_operation]
    exact record.firstOperation
  · change current.report.final.owner record.output.produced.actor = .primary
    exact native.owner_at current.report.final record.live.anchor.environment record.output.produced.actor
  · rw [observed]
    exact record.outputRef
  · rw [observed] <;> rfl

private theorem service_ticket_action (state : State input) (ticket : Work.Item (Ticket input.active input.passive))
    (member : ticket ∈ state.work.pending) : CampusTCPRoundMonitor.ticketAction state (some ticket.id) = some (.serve ticket.id) := by
  unfold CampusTCPRoundMonitor.ticketAction
  simp only [bind, Option.bind]
  cases found : state.work.pending.find? (fun item => item.id == ticket.id) with
  | none => exact False.elim ((List.find?_eq_none.mp found ticket member) (beq_self_eq_true _))
  | some item => rfl

theorem serve_data_at (native : NativeEnv initial) (quantum : Nat)
    (record : E.DataTicket initial native current monitor sentAt retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .serve record.ticket.id none ∧
      Nonempty (E.DataLink initial move.after (M.observe (config initial native quantum) monitor actual) sentAt retries released) := by
  let cfg := config initial native quantum
  let range := record.live.gateway.admission
  have next : R.nextAction cfg.toConfig current.report.final monitor.round = some (.serve record.ticket.id) := by
    simp only [R.nextAction, record.phaseEq, record.ticketRef]
    exact service_ticket_action current.report.final record.ticket record.pending
  have actor : record.ticket.value.produced.actor = .client := by rw [record.produced]; exact record.output.actor
  have fields : OriginalFields (complete := complete) (request := request) record.ticket.value.produced := by
    rw [record.produced]; exact record.output.fields
  let ready := CampusTCPRecoveryRoundAdmission.RangeState.original_service_ready native
    (beforeService input current.report.final .primary) range
    (initial.service_environment current.report.final record.live.anchor.environment) record.ticket.value.source
    fields.header record.live.gateway.valid record.live.gateway.records fields.profile fields.sequence
    fields.acknowledgment fields.payload fields.ttl
  have phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final record.ticket.value.gateway := by
    rw [record.primary]
    exact native.service_phase_at current.report.final record.live.anchor.environment
  have available : ∃ actual : Step input, ∃ served : Served input,
      ∃ emission : WireForwarding.Emission served.ticket.value.source.packet,
      ∃ emitted : served.evidence.output = some emission,
        Nonempty (N.ServiceMove initial current record.ticket ⟨initial.entry.flow, .original⟩ range.session actual served emission emitted) := by
    cases ready with
    | inl fresh =>
      apply CampusTCPRecoveryRoundNetwork.serve_at initial current record.live.anchor record.ticket record.pending phase
        ⟨initial.entry.flow, .original⟩ range.session
      rw [record.primary, record.ingress, actor]
      exact fresh
    | inr repeated =>
      apply CampusTCPRecoveryRoundNetwork.serve_repeated_at initial current record.live.anchor record.ticket record.pending phase
        ⟨initial.entry.flow, .original⟩ range.session
      rw [record.primary, record.ingress, actor]
      exact repeated
  obtain ⟨actual, served, emission, emitted, ⟨value⟩⟩ := available
  have servedFields : OriginalFields (complete := complete) (request := request) served.ticket.value.produced := by
    rw [value.facts.ticket]; exact fields
  obtain ⟨live, seen⟩ := record.live.original_service value record.primary servedFields
  have selected : R.nextAction cfg.toConfig actual.before monitor.round = some (.serve record.ticket.id) := by
    rw [value.facts.beforeEq]; exact next
  obtain ⟨packet, pending⟩ := F.service_pending actual served value.facts.recorded emission emitted
  have round : CampusTCPRoundMonitor.observe cfg.toConfig monitor.round actual =
      { phase := .dataLink, refs := { monitor.round.refs with
        dataService := some actual.before.services.length, dataLinkPacket := some packet } } := by
    rw [F.observe_action cfg.toConfig monitor.round actual (.serve record.ticket.id)
      value.facts.supported value.facts.passed selected value.facts.event, CampusTCPRoundMonitor.advance, record.phaseEq]
    exact F.observeService_eq monitor.round actual .client .dataLink served value.facts.recorded emission emitted pending
  have observed : M.observe cfg monitor actual = { monitor with round := { phase := .dataLink, refs := {
      monitor.round.refs with dataService := some actual.before.services.length, dataLinkPacket := some packet } } } := by
    unfold CampusTCPRecoveryRoundMonitor.observe
    rw [value.facts.supported, value.facts.passed]
    simp only [Bool.and_self, ite_true, value.facts.event, record.waiting, Bool.false_eq_true, ite_false]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, record.phaseEq, record.waiting]
    cases monitor.firstDataReceipt <;> rfl
  have receipts : value.move.after.report.final.receipts = current.report.final.receipts := by
    rw [value.move.final]; exact value.facts.receipts
  have retained : current.report.final.receipts <+: value.move.after.report.final.receipts := by
    rw [receipts]; exact List.prefix_refl _
  have firstSame : live.history.first = record.live.history.first :=
    history_first live.history record.live.history (by rw [value.endpoints])
  have drops := silent_drops record.drops value.move (by simp only [E.dropID, value.facts.event])
  refine ⟨actual, value.move, value.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    index := actual.before.services.length, served, stored := ?_, emission, emitted, application := ?_
    fields := ⟨?_, value.facts.target, servedFields.sequence, servedFields.acknowledgment, servedFields.payload, servedFields.profile⟩
    observed := seen, packetID := packet, custody := ?_, serviceRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed]
  · rw [observed]; exact record.waiting
  · rw [observed]; exact record.retryCount
  · rw [observed]; exact record.dropCount
  · rw [observed]; exact drops
  · rw [observed, retainFirst_index]; exact record.firstRef
  · rw [firstSame, retainFirst_operation]; exact record.firstOperation
  · rw [value.move.final, value.facts.beforeEq]; exact value.facts.serviceIndex
  · rw [value.facts.ticket, record.produced]; exact record.output.application
  · rw [value.facts.ticket]; exact actor
  · rw [value.move.final]; exact pending
  · rw [observed]
  · rw [observed]

theorem deliver_data_at (native : NativeEnv initial) (quantum : Nat)
    (record : E.DataLink initial current monitor sentAt retries released) :
    ∃ actual, ∃ move : Move current actual, actual.event = .deliver record.index record.emission.bytes true ∧
      Nonempty (E.NeedAck initial move.after (M.observe (config initial native quantum) monitor actual) sentAt retries) := by
  obtain ⟨received⟩ := CampusTCPRecoveryRoundDelivery.deliver_data current record.live.receiver record.index record.served
    record.stored record.emission record.emitted record.application record.pending record.fields
  let live := record.live.received received record.observed
  have next : R.nextAction (config initial native quantum).toConfig current.report.final monitor.round =
      some (.deliver record.index record.emission.bytes true) := by
    simp only [R.nextAction, record.phaseEq, record.serviceRef, record.packetRef, R.linkAction,
      record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  have observed := CampusTCPRecoveryRoundDataState.Received.observe received (config initial native quantum)
    monitor record.waiting record.phaseEq next
  have receipts : received.move.after.report.final.receipts = current.report.final.receipts ++ [received.delivery.receipt] := by
    rw [received.move.final]
    exact received.delivery.receiptsHistory
  have retained : current.report.final.receipts <+: received.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_append _ _
  have operations := CampusTCPRoundPhaseHistory.Move.delivery_history received.move received.delivery rfl .server
  simp only [received.fields.actor, Actor.other, ite_true] at operations
  have firstEvidence : ∃ first : Option (E.FirstReceipt initial received.move.after),
      (M.observe (config initial native quantum) monitor received.delivery.step).firstDataReceipt = first.map (·.index) ∧
      live.history.first = first.map (·.operation) := by
    cases released with
    | false =>
      have oldFirst : record.first = none := by
        have same := record.firstOperation
        rw [no_first record.live.history] at same
        cases selected : record.first with
        | none => rfl
        | some first => simp only [selected, Option.map_some, reduceCtorEq] at same
      have oldRef : monitor.firstDataReceipt = none := by rw [record.firstRef, oldFirst]; rfl
      have payload : received.delivery.localStep.releasedPayload = request.bytes := by
        simpa only [Bool.false_eq_true, ite_false] using received.localRelease
      let first : E.FirstReceipt initial received.move.after := {
        index := received.delivery.step.before.receipts.length
        receipt := received.delivery.receipt
        stored := by
          rw [receipts, received.delivery.beforeEq, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self, List.getElem?_cons_zero]
        operation := received.delivery.localStep
        application := received.delivery.receiptStep
        actor := by rw [received.delivery.receiptService]; exact received.fields.actor
        released := payload }
      have releases : (applicationSteps received.move.after.endpoints .server).filter
          CampusTCPRecoveryRoundHistory.nonemptyRelease = [received.delivery.localStep] := by
        rw [operations, List.filter_append, record.live.history.releases, no_first record.live.history]
        simp only [Option.toList_none, List.filter_cons, List.filter_nil,
          CampusTCPRecoveryRoundHistory.nonemptyRelease, payload,
          List.isEmpty_eq_false_iff.mpr request.nonempty, Bool.not_false, ite_true, List.nil_append]
      refine ⟨some first, ?_, ?_⟩
      · simp only [observed, D.receiptMonitor, oldRef, first, Option.map_some]
      · exact history_first_some live.history releases
    | true =>
      obtain ⟨old, selected⟩ := active_first record.toActive
      have oldRef : monitor.firstDataReceipt = some old.index := by
        simpa only [selected, Option.map_some] using record.firstRef
      have firstSame : live.history.first = record.live.history.first := history_first live.history record.live.history (by
        rw [operations, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, CampusTCPRecoveryRoundHistory.nonemptyRelease,
          received.localRelease, ite_true, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false,
          List.append_nil])
      refine ⟨retainFirst record.first retained, ?_, ?_⟩
      · rw [observed, retainFirst_index]
        simp only [D.receiptMonitor, oldRef, selected, Option.map_some]
      · rw [firstSame, retainFirst_operation]
        exact record.firstOperation
  obtain ⟨first, firstRef, firstOperation⟩ := firstEvidence
  have drops := silent_drops record.drops received.move (by simp only [E.dropID, received.delivery.event])
  refine ⟨received.delivery.step, received.move, received.delivery.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_
    first, firstRef, firstOperation, pending := received.pending }⟩⟩
  · rw [observed] <;> rfl
  · rw [observed]
    exact record.waiting
  · rw [observed]
    exact record.retryCount
  · rw [observed]
    exact record.dropCount
  · rw [observed]
    exact drops

private theorem application_receipts (before : State input) (actor : Actor) (event : T.Event)
    (effect : Effect input) (computed : applyApplication input before actor event = .ok effect) :
    effect.state.receipts = before.receipts := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_receipts (acked : CampusTCPRecoveryRoundDelivery.Acked initial current) :
    acked.move.after.report.final.receipts = current.report.final.receipts := by
  obtain ⟨effect, custody, computed, final⟩ := acked.actual.processed
  rw [acked.facts.event] at computed
  have applied : applyApplication input acked.actual.before .server (.emitAck true) = .ok effect := computed
  simpa only [acked.move.final, final, acked.facts.beforeEq] using application_receipts _ _ _ _ applied

theorem emit_ack_at (native : NativeEnv initial) (quantum : Nat)
    (record : E.NeedAck initial current monitor sentAt retries) :
    ∃ actual, ∃ move : Move current actual, actual.event = .emitAck .server true ∧
      Nonempty (E.AckIngress initial move.after (M.observe (config initial native quantum) monitor actual) sentAt retries) := by
  obtain ⟨acked⟩ := CampusTCPRecoveryRoundDelivery.emit_ack current record.live.receiver record.pending
  let live := record.live.ack acked
  obtain ⟨packetID, custody, observed, _⟩ := CampusTCPRecoveryRoundDataState.Acked.observe acked
    (config initial native quantum) monitor record.waiting record.phaseEq
  have receipts := ack_receipts acked
  have retained : current.report.final.receipts <+: acked.move.after.report.final.receipts := by
    rw [receipts]
    exact List.prefix_refl _
  have operations := CampusTCPRoundPhaseHistory.Move.local_history acked.move .server (.emitAck true)
    (by rw [acked.facts.event]; exact .emitAck _) acked.facts.localStep acked.facts.application .server
  simp only [ite_true] at operations
  have quiet : acked.facts.localStep.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, acked.facts.localEvent]
  have firstSame : live.history.first = record.live.history.first := history_first live.history record.live.history (by
    rw [operations, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, CampusTCPRecoveryRoundHistory.nonemptyRelease,
      quiet, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil])
  have actor : acked.facts.produced.actor = .server := by rw [acked.facts.production]; rfl
  let output : E.AckOutput initial acked.move.after :=
    ⟨acked.actual.before.outputs.length, acked.facts.produced, by
      rw [acked.move.final, acked.facts.beforeEq]
      exact acked.facts.source, actor, by rw [acked.facts.production]; trivial, acked.fields⟩
  have drops := silent_drops record.drops acked.move (by simp only [E.dropID, acked.facts.event])
  refine ⟨acked.actual, acked.move, acked.facts.event, ⟨{
    live, phaseEq := ?_, waiting := ?_, retryCount := ?_, dropCount := ?_, drops := ?_
    first := retainFirst record.first retained, firstRef := ?_, firstOperation := ?_
    output, packetID, custody := ?_, outputRef := ?_, packetRef := ?_ }⟩⟩
  · rw [observed] <;> rfl
  · rw [observed]
    exact record.waiting
  · rw [observed]
    exact record.retryCount
  · rw [observed]
    exact record.dropCount
  · rw [observed]
    exact drops
  · rw [observed, retainFirst_index]
    exact record.firstRef
  · rw [firstSame, retainFirst_operation]
    exact record.firstOperation
  · rw [acked.move.final]
    exact custody
  · rw [observed] <;> rfl
  · rw [observed] <;> rfl

end

end Netlib.Check.CampusTCPRecoveryRoundPhaseForward
