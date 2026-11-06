import Netlib.Check.CampusTCPGapProgressRetire
import Netlib.Check.CampusTCPGapProgressWire
import Netlib.Check.CampusTCPRecoveryRoundDrop

/-!
# Actual phase evidence for held-gap progress

Each reference selects stored work at the current cut.
The drop log starts at the selected cut and retains all later drops.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPRecoveryRoundPhaseBase (At)
open CampusTCPGapProgressPhaseBase (Anchor)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressState (Live)
open CampusTCPGapProgressRetire (Retired Completed)
open CampusTCPGapProgressWire (DataFields AckFields DataLinkFields)
open CampusTCPGapProgressMonitor (Monitor)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut before current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper}
  {native : NativeEnv cut initial.gateway.seed.entry} {allowance : Nat}

def dropID (actual : Step input) : Option Nat :=
  match actual.event with | .dropPacket id => some id | _ => none

def DropLog (initial current : Cut input complete) (ids : List Nat) : Prop :=
  ∃ suffix, current.report.steps = initial.report.steps ++ suffix ∧ suffix.filterMap dropID = ids

theorem DropLog.ofInitial (cut : Cut input complete) : DropLog cut cut [] :=
  ⟨[], (List.append_nil _).symm, rfl⟩

theorem DropLog.append (log : DropLog cut current ids) (move : Move current actual) :
    DropLog cut move.after (ids ++ (dropID actual).toList) := by
  obtain ⟨suffix, history, drops⟩ := log
  refine ⟨suffix ++ [actual], ?_, ?_⟩
  · rw [move.history, history, List.append_assoc]
  · simp only [List.filterMap_append, drops, List.filterMap_cons, List.filterMap_nil]
    cases dropID actual <;> rfl

theorem DropLog.clock (log : DropLog cut before ids) (placement : At before current) :
    DropLog cut current ids := by
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

structure FirstReceipt (initial : GapInitial cut sender lower upper) (current : Cut input complete) where
  index : Nat
  receipt : Receipt input
  stored : current.report.final.receipts[index]? = some receipt
  operation : T.Step
  application : receipt.application = some operation
  actor : receipt.served.ticket.value.produced.actor = sender
  released : operation.releasedPayload = lower ++ upper

def FirstReceipt.reframe (receipt : FirstReceipt initial before)
    (stored : current.report.final.receipts[receipt.index]? = some receipt.receipt) : FirstReceipt initial current :=
  ⟨receipt.index, receipt.receipt, stored, receipt.operation, receipt.application, receipt.actor, receipt.released⟩

def FirstReceipt.clock (receipt : FirstReceipt initial before) (placement : At before current) :
    FirstReceipt initial current := receipt.reframe (by rw [placement.frame.receipts]; exact receipt.stored)

structure Active (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) (released : Bool)
    (phase : CampusTCPRoundMonitor.Phase) where
  live : Live initial current retries released
  phaseEq : monitor.phase = phase
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  bound : retries ≤ allowance
  drops : DropLog cut current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : live.history.streams.first = first.map (·.operation)

structure DataOutput (initial : GapInitial cut sender lower upper) (current : Cut input complete) where
  index : Nat
  produced : Produced input.active input.passive
  stored : current.report.final.outputs[index]? = some produced
  actor : produced.actor = sender
  application : CampusTCPDeliveryEnabled.ApplicationSource produced
  fields : DataFields initial produced

structure AckOutput (initial : GapInitial cut sender lower upper) (current : Cut input complete) where
  index : Nat
  produced : Produced input.active input.passive
  stored : current.report.final.outputs[index]? = some produced
  actor : produced.actor = sender.other
  application : CampusTCPDeliveryEnabled.ApplicationSource produced
  fields : AckFields initial produced

structure DataIngress (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) (released : Bool)
    extends Active initial allowance current monitor retries released .dataIngress where
  output : DataOutput initial current
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.ingressAt output.index) = some packetID
  outputRef : monitor.refs.dataOutput = some output.index
  packetRef : monitor.refs.dataIngressPacket = some packetID

structure DataTicket (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (allowance : Nat) (current : Cut input complete) (monitor : Monitor) (retries : Nat) (released : Bool)
    extends Active initial allowance current monitor retries released .dataTicket where
  output : DataOutput initial current
  ticket : Work.Item (Ticket input.active input.passive)
  pending : ticket ∈ current.report.final.work.pending
  outputIndex : ticket.value.outputIndex = output.index
  produced : ticket.value.produced = output.produced
  standby : ticket.value.gateway = .standby
  ingress : ticket.value.ingress = native.ingress sender
  outputRef : monitor.refs.dataOutput = some output.index
  ticketRef : monitor.refs.dataTicket = some ticket.id

structure DataLink (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) (released : Bool)
    extends Active initial allowance current monitor retries released .dataLink where
  index : Nat
  served : Served input
  stored : current.report.final.services[index]? = some served
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  actor : served.ticket.value.produced.actor = sender
  application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced
  fields : DataLinkFields initial served emission
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.linkAt index) = some packetID
  serviceRef : monitor.refs.dataService = some index
  packetRef : monitor.refs.dataLinkPacket = some packetID

structure NeedAck (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat)
    extends Active initial allowance current monitor retries true .needAck where
  pending : live.receiverFacts.reaction.work.pending ≠ []

structure AckIngress (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat)
    extends Active initial allowance current monitor retries true .ackIngress where
  output : AckOutput initial current
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.ingressAt output.index) = some packetID
  outputRef : monitor.refs.ackOutput = some output.index
  packetRef : monitor.refs.ackIngressPacket = some packetID

structure AckTicket (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (allowance : Nat) (current : Cut input complete) (monitor : Monitor) (retries : Nat)
    extends Active initial allowance current monitor retries true .ackTicket where
  output : AckOutput initial current
  ticket : Work.Item (Ticket input.active input.passive)
  pending : ticket ∈ current.report.final.work.pending
  outputIndex : ticket.value.outputIndex = output.index
  produced : ticket.value.produced = output.produced
  standby : ticket.value.gateway = .standby
  ingress : ticket.value.ingress = native.ingress sender.other
  outputRef : monitor.refs.ackOutput = some output.index
  ticketRef : monitor.refs.ackTicket = some ticket.id

structure AckLink (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat)
    extends Active initial allowance current monitor retries true .ackLink where
  index : Nat
  served : Served input
  stored : current.report.final.services[index]? = some served
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  actor : served.ticket.value.produced.actor = sender.other
  application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced
  fields : AckFields initial served.ticket.value.produced
  target : emission.target = (endpoint cut.endpoints sender).core.inbound
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.linkAt index) = some packetID
  serviceRef : monitor.refs.ackService = some index
  packetRef : monitor.refs.ackLinkPacket = some packetID

structure Waiting (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) (released : Bool) where
  live : Live initial current retries released
  waiting : monitor.waiting = true
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries + 1
  bound : retries + 1 ≤ allowance
  drops : DropLog cut current monitor.drops
  dropStep : Step input
  member : dropStep ∈ current.report.steps
  dropPacket : Nat
  lastDrop : monitor.drops.getLast? = some dropPacket
  facts : CampusTCPRecoveryRoundDrop.Facts dropStep.before dropPacket dropStep
  absent : ∀ item ∈ current.report.final.custody.pending, item.id ≠ dropPacket
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : live.history.streams.first = first.map (·.operation)

structure NeedRead (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) where
  retired : Retired initial current retries
  phaseEq : monitor.phase = .needRead
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  bound : retries ≤ allowance
  drops : DropLog cut current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : retired.history.streams.first = first.map (·.operation)

structure Done (initial : GapInitial cut sender lower upper) (allowance : Nat)
    (current : Cut input complete) (monitor : Monitor) (retries : Nat) where
  completed : Completed initial current retries
  phaseEq : monitor.phase = .done
  waiting : monitor.waiting = false
  retryCount : monitor.retries = retries
  dropCount : monitor.drops.length = retries
  bound : retries ≤ allowance
  drops : DropLog cut current monitor.drops
  first : Option (FirstReceipt initial current)
  firstRef : monitor.firstDataReceipt = first.map (·.index)
  firstOperation : completed.history.streams.first = first.map (·.operation)

inductive Evidence (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (allowance : Nat) (current : Cut input complete) (monitor : Monitor) : Type where
  | dataIngress {retries released} (record : DataIngress initial allowance current monitor retries released)
  | dataTicket {retries released} (record : DataTicket initial native allowance current monitor retries released)
  | dataLink {retries released} (record : DataLink initial allowance current monitor retries released)
  | needAck {retries} (record : NeedAck initial allowance current monitor retries)
  | ackIngress {retries} (record : AckIngress initial allowance current monitor retries)
  | ackTicket {retries} (record : AckTicket initial native allowance current monitor retries)
  | ackLink {retries} (record : AckLink initial allowance current monitor retries)
  | waiting {retries released} (record : Waiting initial allowance current monitor retries released)
  | needRead {retries} (record : NeedRead initial allowance current monitor retries)
  | done {retries} (record : Done initial allowance current monitor retries)

def initial_evidence (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (allowance : Nat)
    (receiver : CampusTCPGapProgressReceiver.Geometry initial) (wire : CampusTCPGapProgressWire.Geometry initial) :
    Evidence initial native allowance cut (CampusTCPGapProgressSetup.initialMonitor initial) :=
  .dataLink {
    toActive := {
      live := Live.ofInitial initial receiver
      phaseEq := rfl, waiting := rfl, retryCount := rfl, dropCount := rfl, bound := Nat.zero_le _
      drops := DropLog.ofInitial cut
      first := none, firstRef := rfl, firstOperation := rfl }
    index := initial.selected.serviceIndex
    served := initial.selected.served
    stored := initial.selected.stored
    emission := initial.selected.emission
    emitted := initial.selected.emitted
    actor := by rw [initial.selected.source, initial.lowerSource.application]; rfl
    application := CampusTCPGapProgressSetup.initial_application_source initial
    fields := CampusTCPGapProgressWire.initial_link_fields wire
    packetID := initial.selected.packetID
    custody := initial.selected.pending
    serviceRef := rfl, packetRef := rfl }

theorem Waiting.credit (record : Waiting initial allowance current monitor retries released)
    (budget : allowance ≤ 2) : retries < 2 := by
  have bound := record.bound
  omega

theorem DataIngress.pending (record : DataIngress initial allowance current monitor retries released) :
    IngressPending current.report.final record.output.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem AckIngress.pending (record : AckIngress initial allowance current monitor retries) :
    IngressPending current.report.final record.output.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem DataLink.pending (record : DataLink initial allowance current monitor retries released) :
    CampusTCPDeliveryEnabled.LinkPending current.report.final record.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem AckLink.pending (record : AckLink initial allowance current monitor retries) :
    CampusTCPDeliveryEnabled.LinkPending current.report.final record.index := by
  obtain ⟨packet, member, _, linked⟩ := current.report.final.custody.pendingID_source _ _ record.custody
  exact ⟨packet, member, linked⟩

theorem Evidence.anchor (evidence : Evidence initial native allowance current monitor) : Anchor cut current := by
  cases evidence with
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

theorem Evidence.drop_log (evidence : Evidence initial native allowance current monitor) :
    DropLog cut current monitor.drops := by
  cases evidence with
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

theorem Evidence.drop_bound (evidence : Evidence initial native allowance current monitor) :
    monitor.drops.length ≤ allowance := by
  cases evidence with
  | dataIngress record => rw [record.dropCount]; exact record.bound
  | dataTicket record => rw [record.dropCount]; exact record.bound
  | dataLink record => rw [record.dropCount]; exact record.bound
  | needAck record => rw [record.dropCount]; exact record.bound
  | ackIngress record => rw [record.dropCount]; exact record.bound
  | ackTicket record => rw [record.dropCount]; exact record.bound
  | ackLink record => rw [record.dropCount]; exact record.bound
  | waiting record => rw [record.dropCount]; exact record.bound
  | needRead record => rw [record.dropCount]; exact record.bound
  | done record => rw [record.dropCount]; exact record.bound

theorem Evidence.retry_bound (evidence : Evidence initial native allowance current monitor) :
    monitor.retries ≤ allowance := by
  cases evidence with
  | dataIngress record => rw [record.retryCount]; exact record.bound
  | dataTicket record => rw [record.retryCount]; exact record.bound
  | dataLink record => rw [record.retryCount]; exact record.bound
  | needAck record => rw [record.retryCount]; exact record.bound
  | ackIngress record => rw [record.retryCount]; exact record.bound
  | ackTicket record => rw [record.retryCount]; exact record.bound
  | ackLink record => rw [record.retryCount]; exact record.bound
  | waiting record => rw [record.retryCount]; have bound := record.bound; omega
  | needRead record => rw [record.retryCount]; exact record.bound
  | done record => rw [record.retryCount]; exact record.bound

theorem Evidence.drop_limit (evidence : Evidence initial native allowance current monitor)
    (budget : allowance ≤ 2) : monitor.drops.length ≤ 2 := Nat.le_trans evidence.drop_bound budget

theorem Evidence.retry_limit (evidence : Evidence initial native allowance current monitor)
    (budget : allowance ≤ 2) : monitor.retries ≤ 2 := Nat.le_trans evidence.retry_bound budget

private theorem first_receipt_of_option {monitor : Monitor} (first : Option (FirstReceipt initial current))
    (reference : monitor.firstDataReceipt = first.map (·.index)) (selected : monitor.firstDataReceipt = some index) :
    ∃ receipt : FirstReceipt initial current, receipt.index = index := by
  have found := reference.symm.trans selected
  cases first with
  | none => cases found
  | some receipt => exact ⟨receipt, Option.some.inj found⟩

theorem Evidence.first_receipt (evidence : Evidence initial native allowance current monitor)
    (selected : monitor.firstDataReceipt = some index) :
    ∃ receipt : FirstReceipt initial current, receipt.index = index := by
  cases evidence with
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

end Netlib.Check.CampusTCPGapProgressEvidence
