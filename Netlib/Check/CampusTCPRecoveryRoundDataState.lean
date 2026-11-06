import Netlib.Check.CampusTCPRecoveryRoundState
import Netlib.Check.CampusTCPRecoveryRoundDelivery
import Netlib.Check.CampusTCPRoundMonitorFacts

/-!
# Current recovery state after data receipts and ACK output

Actual receipt and output records extend the same history.
Their peer frames retain the current sender flight.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundDataState

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)

namespace D
export CampusTCPRecoveryRoundDelivery (Received Acked)
end D

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}

theorem Received.gateway (received : D.Received initial current released facts index served emission emitted)
    (gateway : Gateway) : beforeService input received.move.after.report.final gateway =
      beforeService input current.report.final gateway := by
  rw [received.move.final]
  simpa only [received.delivery.beforeEq] using CampusTCPRoundLocal.step_service_nonservice received.delivery.step
    (by rw [received.delivery.event]; trivial) gateway

theorem Acked.gateway (acked : D.Acked initial current) (gateway : Gateway) :
    beforeService input acked.move.after.report.final gateway = beforeService input current.report.final gateway := by
  rw [acked.move.final]
  simpa only [acked.facts.beforeEq] using
    CampusTCPRoundLocal.step_service_nonservice acked.actual (by rw [acked.facts.event]; trivial) gateway

end Netlib.Check.CampusTCPRecoveryRoundDataState

namespace Netlib.Check.CampusTCPRecoveryRoundState

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)

namespace D
export CampusTCPRecoveryRoundDelivery (Received Acked)
end D

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}
variable {sentAt retries : Nat} {released : Bool}

def Live.received (live : Live initial current sentAt retries released)
    (received : D.Received initial current released live.receiver index served emission emitted)
    (observed : CampusTCPRecoveryRoundAdmission.Observed initial.session request.bytes
      (beforeService input current.report.final .primary).admission) :
    Live initial received.move.after sentAt retries true where
  anchor := by
    refine ⟨?_, live.anchor.retained.trans received.move.retained, ?_⟩
    · intro actor
      cases actor
      · rw [received.peer]
        exact ⟨live.sender.coherent, live.sender.prepared, by rw [live.sender.runtime]; rfl⟩
      · exact ⟨received.receiver.coherent, received.receiver.prepared, by rw [received.receiver.runtime]; rfl⟩
    · rw [received.move.final]
      exact live.anchor.environment.trans received.delivery.environment
  sender := by rw [received.peer]; exact live.sender
  receiver := received.receiver
  gateway := live.gateway.frame (CampusTCPRecoveryRoundDataState.Received.gateway received .primary).symm
  history := by
    cases released with
    | false =>
      let first := Classical.choose (received.fresh rfl)
      have same : first.toDelivery = received.delivery := Classical.choose_spec (received.fresh rfl)
      exact live.history.first_data received.move first (congrArg CampusTCPRoundDelivery.Delivery.step same)
        received.fields.actor received.fields.packet.2.2.2.2.2
    | true =>
      exact live.history.old_data received.move received.delivery rfl received.fields.actor
        (by simpa only [ite_true] using received.localRelease)
  observed _ := ⟨observed.frame (congrArg CampusTCPService.Before.admission
    (CampusTCPRecoveryRoundDataState.Received.gateway received .primary).symm)⟩

def Live.ack (live : Live initial current sentAt retries true) (acked : D.Acked initial current) :
    Live initial acked.move.after sentAt retries true where
  anchor := by
    refine ⟨?_, live.anchor.retained.trans acked.move.retained, ?_⟩
    · intro actor
      cases actor
      · rw [acked.peer]
        exact ⟨live.sender.coherent, live.sender.prepared, by rw [live.sender.runtime]; rfl⟩
      · exact ⟨acked.receiver.coherent, acked.receiver.prepared, by rw [acked.receiver.runtime]; rfl⟩
    · rw [acked.move.final]
      exact live.anchor.environment.trans acked.facts.environment
  sender := by rw [acked.peer]; exact live.sender
  receiver := acked.receiver
  gateway := live.gateway.frame (CampusTCPRecoveryRoundDataState.Acked.gateway acked .primary).symm
  history := live.history.server_ack acked.move acked.facts.localStep
    (by rw [acked.facts.event]; exact .emitAck _) acked.facts.application acked.facts.localEvent
  observed _ := by
    obtain ⟨seen⟩ := live.observed rfl
    exact ⟨seen.frame (congrArg CampusTCPService.Before.admission
      (CampusTCPRecoveryRoundDataState.Acked.gateway acked .primary).symm)⟩

end

end Netlib.Check.CampusTCPRecoveryRoundState

namespace Netlib.Check.CampusTCPRecoveryRoundDataState

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)

namespace M
export CampusTCPRecoveryRoundMonitor (Config Monitor observe observeOrdinary)
end M
namespace R
export CampusTCPRoundMonitor (nextAction advance observeReceipt observeOutput ingressAction)
end R
namespace F
export CampusTCPRoundMonitorFacts (observe_action observeReceipt_eq observeOutput_eq output_pending)
end F

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete}

def receiptMonitor (monitor : M.Monitor) (actual : Step input) (operation : T.Step) : M.Monitor :=
  { monitor with
    round := { phase := .needAck, refs := { monitor.round.refs with
      dataReceipt := some actual.before.receipts.length, dataReceiveStamp := some operation.stamp } }
    firstDataReceipt := match monitor.firstDataReceipt with
      | some index => some index
      | none => some actual.before.receipts.length }

theorem Received.observe (received : D.Received initial current released facts index served emission emitted)
    (config : M.Config) (monitor : M.Monitor) (waiting : monitor.waiting = false)
    (phase : monitor.round.phase = .dataLink)
    (next : R.nextAction config.toConfig current.report.final monitor.round = some (.deliver index emission.bytes true)) :
    M.observe config monitor received.delivery.step =
      receiptMonitor monitor received.delivery.step received.delivery.localStep := by
  have selected : R.nextAction config.toConfig received.delivery.step.before monitor.round =
      some (.deliver index emission.bytes true) := by simpa only [received.delivery.beforeEq] using next
  have observed := F.observe_action config.toConfig monitor.round received.delivery.step
    (.deliver index emission.bytes true) received.delivery.supported received.delivery.passed selected received.delivery.event
  have receiver : received.delivery.receipt.actor = .server := by
    have receiver := received.delivery.receipt.receiver
    rw [received.delivery.receiptService, received.fields.actor] at receiver
    exact receiver
  have application : received.delivery.step.result.application = some (.server, received.delivery.localStep) := by
    simpa only [received.fields.actor, Actor.other] using received.delivery.recorded
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round received.delivery.step =
      { phase := .needAck, refs := { monitor.round.refs with
        dataReceipt := some received.delivery.step.before.receipts.length,
        dataReceiveStamp := some received.delivery.localStep.stamp } } := by
    rw [observed, R.advance, phase]
    exact F.observeReceipt_eq monitor.round received.delivery.step .server .needAck received.delivery.receipt
      received.delivery.receiptAt receiver received.delivery.localStep application
  unfold CampusTCPRecoveryRoundMonitor.observe
  rw [received.delivery.supported, received.delivery.passed]
  simp only [Bool.and_self, ite_true, received.delivery.event, waiting, Bool.false_eq_true, ite_false]
  unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
  rw [round, phase]
  unfold receiptMonitor
  cases monitor.firstDataReceipt <;> rfl

def ackMonitor (monitor : M.Monitor) (actual : Step input) (packet : Nat) : M.Monitor :=
  { monitor with round := { phase := .ackIngress, refs := { monitor.round.refs with
    ackOutput := some actual.before.outputs.length, ackIngressPacket := some packet } } }

theorem Acked.observe (acked : D.Acked initial current) (config : M.Config) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (phase : monitor.round.phase = .needAck) :
    ∃ packet, acked.actual.result.state.custody.pendingID (Transit.ingressAt acked.actual.before.outputs.length) = some packet ∧
      M.observe config monitor acked.actual = ackMonitor monitor acked.actual packet ∧
      R.nextAction config.toConfig acked.actual.result.state (ackMonitor monitor acked.actual packet).round =
        some (.assign acked.actual.before.outputs.length config.serverIngress) := by
  obtain ⟨packet, pending⟩ := F.output_pending acked.actual acked.facts.produced acked.facts.output
  have selected : R.nextAction config.toConfig acked.actual.before monitor.round = some (.emitAck .server true) := by
    simp only [R.nextAction, phase]
  have observed := F.observe_action config.toConfig monitor.round acked.actual (.emitAck .server true)
    acked.facts.supported acked.facts.passed selected acked.facts.event
  have actor : acked.facts.produced.actor = .server := by rw [acked.facts.production]; rfl
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round acked.actual =
      { phase := .ackIngress, refs := { monitor.round.refs with
        ackOutput := some acked.actual.before.outputs.length, ackIngressPacket := some packet } } := by
    rw [observed, R.advance, phase]
    exact F.observeOutput_eq monitor.round acked.actual .server .ackIngress acked.facts.produced acked.facts.output actor pending
  refine ⟨packet, pending, ?_, ?_⟩
  · unfold CampusTCPRecoveryRoundMonitor.observe
    rw [acked.facts.supported, acked.facts.passed]
    simp only [Bool.and_self, ite_true, acked.facts.event, waiting, Bool.false_eq_true, ite_false]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, phase]
    unfold ackMonitor
    cases monitor.firstDataReceipt <;> rfl
  · have source : acked.actual.result.state.outputs[acked.actual.before.outputs.length]? = some acked.facts.produced := by
      simpa only [acked.facts.beforeEq] using acked.facts.source
    simp only [ackMonitor, R.nextAction, R.ingressAction, source, pending, bind, Option.bind,
      beq_self_eq_true, ite_true, pure]

def ingressPhase : Actor → CampusTCPRoundMonitor.Phase
  | .client => .dataIngress
  | .server => .ackIngress

def ticketPhase : Actor → CampusTCPRoundMonitor.Phase
  | .client => .dataTicket
  | .server => .ackTicket

def assignmentMonitor (monitor : M.Monitor) (actor : Actor) (ticket : Nat) : M.Monitor :=
  { monitor with round := { phase := ticketPhase actor, refs := match actor with
    | .client => { monitor.round.refs with dataTicket := some ticket }
    | .server => { monitor.round.refs with ackTicket := some ticket } } }

theorem AssignmentMove.observe
    (value : CampusTCPRecoveryRoundNetwork.AssignmentMove initial current index ingress produced actual)
    (config : M.Config) (monitor : M.Monitor) (actor : Actor) (waiting : monitor.waiting = false)
    (phase : monitor.round.phase = ingressPhase actor)
    (next : R.nextAction config.toConfig current.report.final monitor.round = some (.assign index ingress)) :
    M.observe config monitor actual = assignmentMonitor monitor actor value.ticket.id ∧
      actual.result.state.work.pending.find? (fun item => item.id == value.ticket.id) = some value.ticket ∧
      R.nextAction config.toConfig actual.result.state (assignmentMonitor monitor actor value.ticket.id).round =
        some (.serve value.ticket.id) := by
  have selected : R.nextAction config.toConfig actual.before monitor.round = some (.assign index ingress) := by
    simpa only [value.facts.beforeEq] using next
  have observed := F.observe_action config.toConfig monitor.round actual (.assign index ingress)
    value.facts.supported value.facts.passed selected value.facts.event
  have found : actual.result.state.work.pending.find? (fun item => item.id == actual.before.work.nextID) = some value.ticket := by
    simpa only [CampusTCPRecoveryRoundNetwork.AssignmentMove.ticket] using
      CampusTCPRoundMonitorFacts.AssignmentFacts.find_new value.facts
  have ticketID : value.ticket.id = actual.before.work.nextID := by
    simp only [CampusTCPRecoveryRoundNetwork.AssignmentMove.ticket, CampusTCPRoundAssignment.ticket_id,
      value.facts.beforeEq]
  have pending : actual.result.state.work.pending.find? (fun item => item.id == value.ticket.id) = some value.ticket := by
    simpa only [ticketID] using found
  have round : CampusTCPRoundMonitor.observe config.toConfig monitor.round actual =
      (assignmentMonitor monitor actor value.ticket.id).round := by
    cases actor with
    | client =>
      change monitor.round.phase = .dataIngress at phase
      rw [observed, R.advance, phase]
      exact CampusTCPRoundMonitorFacts.observeAssignment_eq monitor.round actual .client .dataTicket value.ticket found
    | server =>
      change monitor.round.phase = .ackIngress at phase
      rw [observed, R.advance, phase]
      exact CampusTCPRoundMonitorFacts.observeAssignment_eq monitor.round actual .server .ackTicket value.ticket found
  refine ⟨?_, pending, ?_⟩
  · unfold CampusTCPRecoveryRoundMonitor.observe
    rw [value.facts.supported, value.facts.passed]
    simp only [Bool.and_self, ite_true, value.facts.event, waiting, Bool.false_eq_true, ite_false]
    unfold CampusTCPRecoveryRoundMonitor.observeOrdinary
    rw [round, phase]
    cases actor <;> unfold assignmentMonitor ingressPhase <;> cases monitor.firstDataReceipt <;> rfl
  · cases actor <;>
      simp only [assignmentMonitor, ticketPhase, R.nextAction, CampusTCPRoundMonitor.ticketAction,
        pending, bind, Option.bind, pure]

end Netlib.Check.CampusTCPRecoveryRoundDataState
