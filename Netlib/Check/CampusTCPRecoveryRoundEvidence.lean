import Netlib.Check.CampusTCPRecoveryRoundState
import Netlib.Check.CampusTCPRecoveryRoundDelivery

/-!
# Actual phase evidence for the recovery monitor

Each live reference selects stored work at the current checked cut.
The drop log and first data receipt retain only past operations.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundPhaseBase (At Anchor)
open CampusTCPRecoveryRoundState (Live Retired Completed)
open CampusTCPRoundPhaseBase (OriginalFields AckFields)
open CampusTCPRecoveryRoundMonitor (Monitor)

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}

def dropID (actual : Step input) : Option Nat :=
  match actual.event with | .dropPacket id => some id | _ => none

def DropLog (initial : Initial report complete request) (current : Cut input complete) (ids : List Nat) : Prop :=
  ∃ suffix, current.report.steps = initial.start.next.report.steps ++ suffix ∧ suffix.filterMap dropID = ids

theorem DropLog.ofInitial (initial : Initial report complete request) :
    DropLog initial (Cut.ofPrepared initial.start) [] := ⟨[], (List.append_nil _).symm, rfl⟩

theorem DropLog.append (log : DropLog initial current ids) (move : CampusTCPRoundPhaseBase.Move current actual) :
    DropLog initial move.after (ids ++ (dropID actual).toList) := by
  obtain ⟨suffix, history, drops⟩ := log
  refine ⟨suffix ++ [actual], ?_, ?_⟩
  · rw [move.history, history, List.append_assoc]
  · simp only [List.filterMap_append, drops, List.filterMap_cons, List.filterMap_nil]
    cases dropID actual <;> rfl

theorem DropLog.clock (log : DropLog initial before ids) (placement : At before current) :
    DropLog initial current ids := by
  obtain ⟨suffix, history, drops⟩ := log
  obtain ⟨extra, appended, clocks⟩ := placement.clocks
  have silent : extra.filterMap dropID = [] := by
    clear history drops appended placement
    induction extra with
    | nil => rfl
    | cons actual rest ih =>
      obtain ⟨actor, now, event⟩ := clocks actual (by simp)
      have tail := ih (fun step member => clocks step (List.mem_cons_of_mem _ member))
      simpa only [List.filterMap_cons, dropID, event] using tail
  exact ⟨suffix ++ extra, by rw [appended, history, List.append_assoc], by
    rw [List.filterMap_append, drops, silent, List.append_nil]⟩

structure FirstReceipt (initial : Initial report complete request) (current : Cut input complete) where
  index : Nat
  receipt : Receipt input
  stored : current.report.final.receipts[index]? = some receipt
  operation : T.Step
  application : receipt.application = some operation
  actor : receipt.served.ticket.value.produced.actor = .client
  released : operation.releasedPayload = request.bytes

def FirstReceipt.reframe (receipt : FirstReceipt initial before)
    (stored : current.report.final.receipts[receipt.index]? = some receipt.receipt) : FirstReceipt initial current :=
  ⟨receipt.index, receipt.receipt, stored, receipt.operation, receipt.application, receipt.actor, receipt.released⟩

def FirstReceipt.clock (receipt : FirstReceipt initial before) (placement : At before current) :
    FirstReceipt initial current := receipt.reframe (by rw [placement.frame.receipts]; exact receipt.stored)

structure Active (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) (released : Bool) (phase : CampusTCPRoundMonitor.Phase) where
  live : Live initial current sentAt retries released
  phaseEq : monitor.round.phase = phase
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  drops : DropLog initial current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : live.history.first = first.map (·.operation)

structure NeedSend (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor) where
  placement : At (Cut.ofPrepared initial.start) current
  anchor : Anchor initial current
  monitorEq : monitor = Monitor.initial

structure DataOutput (initial : Initial report complete request) (current : Cut input complete) where
  index : Nat
  produced : Produced input.active input.passive
  stored : current.report.final.outputs[index]? = some produced
  actor : produced.actor = .client
  application : CampusTCPDeliveryEnabled.ApplicationSource produced
  fields : OriginalFields (complete := complete) (request := request) produced

structure AckOutput (initial : Initial report complete request) (current : Cut input complete) where
  index : Nat
  produced : Produced input.active input.passive
  stored : current.report.final.outputs[index]? = some produced
  actor : produced.actor = .server
  application : CampusTCPDeliveryEnabled.ApplicationSource produced
  fields : AckFields (complete := complete) (request := request) produced

structure DataIngress (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) (released : Bool) extends Active initial current monitor sentAt retries released .dataIngress where
  output : DataOutput initial current
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.ingressAt output.index) = some packetID
  outputRef : monitor.round.refs.dataOutput = some output.index
  packetRef : monitor.round.refs.dataIngressPacket = some packetID

structure DataTicket (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (monitor : Monitor) (sentAt retries : Nat) (released : Bool)
    extends Active initial current monitor sentAt retries released .dataTicket where
  output : DataOutput initial current
  ticket : Work.Item (Ticket input.active input.passive)
  pending : ticket ∈ current.report.final.work.pending
  outputIndex : ticket.value.outputIndex = output.index
  produced : ticket.value.produced = output.produced
  primary : ticket.value.gateway = .primary
  ingress : ticket.value.ingress = native.dataIngress
  outputRef : monitor.round.refs.dataOutput = some output.index
  ticketRef : monitor.round.refs.dataTicket = some ticket.id

structure DataLink (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) (released : Bool) extends Active initial current monitor sentAt retries released .dataLink where
  index : Nat
  served : Served input
  stored : current.report.final.services[index]? = some served
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced
  fields : CampusTCPRecoveryRoundDelivery.DataFields initial served emission
  observed : CampusTCPRecoveryRoundAdmission.Observed initial.session request.bytes
    (beforeService input current.report.final .primary).admission
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.linkAt index) = some packetID
  serviceRef : monitor.round.refs.dataService = some index
  packetRef : monitor.round.refs.dataLinkPacket = some packetID

structure NeedAck (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) extends Active initial current monitor sentAt retries true .needAck where
  pending : live.receiver.reaction.work.pending ≠ []

structure AckIngress (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) extends Active initial current monitor sentAt retries true .ackIngress where
  output : AckOutput initial current
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.ingressAt output.index) = some packetID
  outputRef : monitor.round.refs.ackOutput = some output.index
  packetRef : monitor.round.refs.ackIngressPacket = some packetID

structure AckTicket (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (monitor : Monitor) (sentAt retries : Nat)
    extends Active initial current monitor sentAt retries true .ackTicket where
  output : AckOutput initial current
  ticket : Work.Item (Ticket input.active input.passive)
  pending : ticket ∈ current.report.final.work.pending
  outputIndex : ticket.value.outputIndex = output.index
  produced : ticket.value.produced = output.produced
  primary : ticket.value.gateway = .primary
  ingress : ticket.value.ingress = native.ackIngress
  outputRef : monitor.round.refs.ackOutput = some output.index
  ticketRef : monitor.round.refs.ackTicket = some ticket.id

structure AckLink (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) extends Active initial current monitor sentAt retries true .ackLink where
  index : Nat
  served : Served input
  stored : current.report.final.services[index]? = some served
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  actor : served.ticket.value.produced.actor = .server
  application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced
  fields : AckFields (complete := complete) (request := request) served.ticket.value.produced
  target : emission.target = initial.entry.flow.output .reply
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.linkAt index) = some packetID
  serviceRef : monitor.round.refs.ackService = some index
  packetRef : monitor.round.refs.ackLinkPacket = some packetID

structure Waiting (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (sentAt retries : Nat) (released : Bool) where
  live : Live initial current sentAt retries released
  waiting : monitor.waiting = true
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries + 1
  bound : retries + 1 ≤ 2
  drops : DropLog initial current monitor.drops
  dropStep : Step input
  member : dropStep ∈ current.report.steps
  dropPacket : Nat
  lastDrop : monitor.drops.getLast? = some dropPacket
  facts : CampusTCPRecoveryRoundDrop.Facts dropStep.before dropPacket dropStep
  absent : ∀ item ∈ current.report.final.custody.pending, item.id ≠ dropPacket
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : live.history.first = first.map (·.operation)

structure NeedRead (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (retries : Nat) where
  retired : Retired initial current retries
  phaseEq : monitor.round.phase = .needRead
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  drops : DropLog initial current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : retired.history.first = first.map (·.operation)

structure Done (initial : Initial report complete request) (current : Cut input complete) (monitor : Monitor)
    (retries : Nat) where
  completed : Completed initial current retries
  phaseEq : monitor.round.phase = .done
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  drops : DropLog initial current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : completed.history.first = first.map (·.operation)

inductive Evidence (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (current : Cut input complete) (monitor : Monitor) : Type where
  | needSend (record : NeedSend initial current monitor)
  | dataIngress {sentAt retries released} (record : DataIngress initial current monitor sentAt retries released)
  | dataTicket {sentAt retries released} (record : DataTicket initial native current monitor sentAt retries released)
  | dataLink {sentAt retries released} (record : DataLink initial current monitor sentAt retries released)
  | needAck {sentAt retries} (record : NeedAck initial current monitor sentAt retries)
  | ackIngress {sentAt retries} (record : AckIngress initial current monitor sentAt retries)
  | ackTicket {sentAt retries} (record : AckTicket initial native current monitor sentAt retries)
  | ackLink {sentAt retries} (record : AckLink initial current monitor sentAt retries)
  | waiting {sentAt retries released} (record : Waiting initial current monitor sentAt retries released)
  | needRead {retries} (record : NeedRead initial current monitor retries)
  | done {retries} (record : Done initial current monitor retries)

def initial_evidence (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat) :
    Evidence initial native quantum (Cut.ofPrepared initial.start) Monitor.initial :=
  .needSend ⟨At.refl _, Anchor.ofInitial initial, rfl⟩

theorem NeedSend.clock (record : NeedSend initial before monitor) (placement : At before current)
    (anchor : Anchor initial current) : NeedSend initial current monitor :=
  ⟨record.placement.trans placement, anchor, record.monitorEq⟩

theorem Waiting.credit (record : Waiting initial current monitor sentAt retries released) : retries < 2 := by
  have bound := record.bound
  omega

theorem DataIngress.pending (record : DataIngress initial current monitor sentAt retries released) :
    IngressPending current.report.final record.output.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem AckIngress.pending (record : AckIngress initial current monitor sentAt retries) :
    IngressPending current.report.final record.output.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem DataLink.pending (record : DataLink initial current monitor sentAt retries released) :
    CampusTCPDeliveryEnabled.LinkPending current.report.final record.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem AckLink.pending (record : AckLink initial current monitor sentAt retries) :
    CampusTCPDeliveryEnabled.LinkPending current.report.final record.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem Evidence.anchor (evidence : Evidence initial native quantum current monitor) : Anchor initial current := by
  cases evidence with
  | needSend record => exact record.anchor
  | dataIngress record => exact record.live.anchor
  | dataTicket record => exact record.live.anchor
  | dataLink record => exact record.live.anchor
  | needAck record => exact record.live.anchor
  | ackIngress record => exact record.live.anchor
  | ackTicket record => exact record.live.anchor
  | ackLink record => exact record.live.anchor
  | waiting record => exact record.live.anchor
  | needRead record => exact record.retired.anchor
  | done record => exact record.completed.anchor

theorem Evidence.drop_log (evidence : Evidence initial native quantum current monitor) :
    DropLog initial current monitor.drops := by
  cases evidence with
  | needSend record =>
    rw [record.monitorEq]
    exact (DropLog.ofInitial initial).clock record.placement
  | dataIngress record => exact record.drops
  | dataTicket record => exact record.drops
  | dataLink record => exact record.drops
  | needAck record => exact record.drops
  | ackIngress record => exact record.drops
  | ackTicket record => exact record.drops
  | ackLink record => exact record.drops
  | waiting record => exact record.drops
  | needRead record => exact record.drops
  | done record => exact record.drops

theorem Evidence.drop_bound (evidence : Evidence initial native quantum current monitor) : monitor.drops.length ≤ 2 := by
  cases evidence with
  | needSend record => simp only [record.monitorEq, Monitor.initial, List.length_nil, Nat.zero_le]
  | dataIngress record => rw [record.dropCount]; exact record.live.sender.bound
  | dataTicket record => rw [record.dropCount]; exact record.live.sender.bound
  | dataLink record => rw [record.dropCount]; exact record.live.sender.bound
  | needAck record => rw [record.dropCount]; exact record.live.sender.bound
  | ackIngress record => rw [record.dropCount]; exact record.live.sender.bound
  | ackTicket record => rw [record.dropCount]; exact record.live.sender.bound
  | ackLink record => rw [record.dropCount]; exact record.live.sender.bound
  | waiting record => rw [record.dropCount]; exact record.bound
  | needRead record => rw [record.dropCount]; exact record.retired.bound
  | done record => rw [record.dropCount]; exact record.completed.bound

theorem Evidence.retry_bound (evidence : Evidence initial native quantum current monitor) : monitor.retries ≤ 2 := by
  cases evidence with
  | needSend record => simp only [record.monitorEq, Monitor.initial, Nat.zero_le]
  | dataIngress record => rw [record.retryCount]; exact record.live.sender.bound
  | dataTicket record => rw [record.retryCount]; exact record.live.sender.bound
  | dataLink record => rw [record.retryCount]; exact record.live.sender.bound
  | needAck record => rw [record.retryCount]; exact record.live.sender.bound
  | ackIngress record => rw [record.retryCount]; exact record.live.sender.bound
  | ackTicket record => rw [record.retryCount]; exact record.live.sender.bound
  | ackLink record => rw [record.retryCount]; exact record.live.sender.bound
  | waiting record => rw [record.retryCount]; exact record.live.sender.bound
  | needRead record => rw [record.retryCount]; exact record.retired.bound
  | done record => rw [record.retryCount]; exact record.completed.bound

private theorem first_receipt_of_option {monitor : Monitor} (first : Option (FirstReceipt initial current))
    (reference : monitor.firstDataReceipt = first.map (·.index)) (selected : monitor.firstDataReceipt = some index) :
    ∃ receipt : FirstReceipt initial current, receipt.index = index := by
  have found := reference.symm.trans selected
  cases first with
  | none => cases found
  | some receipt => exact ⟨receipt, Option.some.inj found⟩

theorem Evidence.first_receipt (evidence : Evidence initial native quantum current monitor)
    (selected : monitor.firstDataReceipt = some index) :
    ∃ receipt : FirstReceipt initial current, receipt.index = index := by
  cases evidence with
  | needSend record => simp only [record.monitorEq, Monitor.initial, reduceCtorEq] at selected
  | dataIngress record => exact first_receipt_of_option record.first record.firstRef selected
  | dataTicket record => exact first_receipt_of_option record.first record.firstRef selected
  | dataLink record => exact first_receipt_of_option record.first record.firstRef selected
  | needAck record => exact first_receipt_of_option record.first record.firstRef selected
  | ackIngress record => exact first_receipt_of_option record.first record.firstRef selected
  | ackTicket record => exact first_receipt_of_option record.first record.firstRef selected
  | ackLink record => exact first_receipt_of_option record.first record.firstRef selected
  | waiting record => exact first_receipt_of_option record.first record.firstRef selected
  | needRead record => exact first_receipt_of_option record.first record.firstRef selected
  | done record => exact first_receipt_of_option record.first record.firstRef selected


end Netlib.Check.CampusTCPRecoveryRoundEvidence
