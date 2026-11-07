import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferServiceFrames
import Netlib.Check.CampusTCPTwoTransferServicePaths

/-!
# Enabled primary data drain for the same located task

The actual current ticket supplies admission, service, and the next link.
Gateway service retains endpoint recovery and the complete loss-cause book.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedDrain

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferPaths (DataTicket)
open CampusTCPTwoTransferWork (DataWork)
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoTransferDrainObserve (linkLane afterDrain)

namespace A
export CampusTCPTwoTransferAdmission (DataServed serve_data_at)
end A
namespace P
export CampusTCPTwoTransferServicePaths (Serviced)
end P
namespace F
export CampusTCPTwoTransferServiceFrames (live_after data_frames)
end F
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe drainTicket)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem ticket_actor (path : DataTicket initial checks current part lane) :
    path.ticket.value.produced.actor = sender := by
  rw [path.toTicketPath.produced]
  exact path.output.actor

private theorem ticket_fields (path : DataTicket initial checks current part lane) :
    CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) path.ticket.value.produced := by
  rw [path.toTicketPath.produced]
  exact path.output.fields

private def serviceCore (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received) (path : DataTicket initial checks current part lane)
    (selected : path.assignedGateway = .primary)
    (value : A.DataServed core.live.gatewayState path.ticket part actual)
    (dropIDs : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops)
    (retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries)
    (wholeDropIDs : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops)
    (wholeTimeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts)
    (queue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward) :
    Core initial checks routing quantum allowance reverseLower reverseUpper
      value.value.move.after (W.observe cfg monitor actual) .primary sent received := by
  have located : path.ticket.value.gateway = .primary := path.ticket_gateway.trans selected
  let raw := F.live_after core.live value.value value.next value.reserved
  let live : LiveAt initial value.value.move.after .primary sent (W.observe cfg monitor actual).exchange.forward.retries received := {
    anchor := raw.anchor
    senderFlight := by rw [retries]; exact raw.senderFlight
    receiverFacts := raw.receiverFacts
    gatewayState := value.next
    gatewayWindow := value.reserved
    history := raw.history }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.value.endpoints
    exact Option.some.inj (live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))
  let sources := CampusTCPTwoTransferSources.Frame.service value.value
  have frames := F.data_frames core.live.gatewayState value located (ticket_fields path) core.peerWindow
  exact {
    live
    senderWindow := by rw [value.value.endpoints]; exact core.senderWindow
    originals := sources.originals core.originals
    originalTimes := core.originalTimes
    writer := sources.writer core.writer
    losses := core.losses.append value.value.move
      (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.value.facts.event])
      (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.value.facts.event])
      dropIDs retries wholeDropIDs wholeTimeouts
    lossBound := by rw [dropIDs]; exact core.lossBound
    primaryQueue := queue
    retired := core.retired
    gatewayAck := by rw [frames.1]; exact core.gatewayAck
    peerSettled := frames.2.1
    peerWindow := frames.2.2
    covered := fun role arrived => value.preserved role (core.covered role arrived)
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := by rw [recovery]; exact core.emptyDuplicate
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, retries]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, retries]; exact core.rtoPending }

def forwardAfter (monitor : M.Monitor) (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) : M.Monitor :=
  match part with
  | .lower => { monitor with lower := lane, lastOriginal := some .lower }
  | .upper => { monitor with upper := lane, lastOriginal := some .upper }

structure Drained (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received) (path : DataTicket initial checks current part lane) (actual : Step input) where
  value : A.DataServed core.live.gatewayState path.ticket part actual
  paths : P.Serviced core.live.gatewayState path value
  next : Core initial checks routing quantum allowance reverseLower reverseUpper
    value.value.move.after (W.observe cfg monitor actual) .primary sent received
  gateway : next.live.gatewayState = value.next
  work : DataWork initial checks value.value.move.after next.live.gatewayState part
    (linkLane lane current.report.final.services.length paths.linked.packetID)
  observed : W.observe cfg monitor actual = afterDrain monitor
    (forwardAfter monitor.exchange.forward part (linkLane lane current.report.final.services.length paths.linked.packetID))
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book
  ack : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack

theorem Drained.sender_recovery {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received} {path : DataTicket initial checks current part lane}
    (value : Drained core path actual) : value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.value.value.endpoints
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))

theorem Drained.receiver_reaction {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received} {path : DataTicket initial checks current part lane}
    (value : Drained core path actual) : value.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) value.value.value.endpoints
  exact Option.some.inj (value.next.live.receiverFacts.ackRuntime.symm.trans (same.trans core.live.receiverFacts.ackRuntime))

private theorem finish (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received) (path : DataTicket initial checks current part lane)
    (selected : path.assignedGateway = .primary)
    (value : A.DataServed core.live.gatewayState path.ticket part actual)
    (paths : P.Serviced core.live.gatewayState path value)
    (drain : W.drainTicket current.report.final monitor = some path.ticket.id)
    (observed : W.observe cfg monitor actual = afterDrain monitor
      (forwardAfter monitor.exchange.forward part (linkLane lane current.report.final.services.length paths.linked.packetID)))
    (queue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward) :
    Nonempty (Drained core path actual) := by
  have drops : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops := by
    rw [observed]
    cases part <;> rfl
  have retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by
    rw [observed]
    cases part <;> rfl
  have wholeDrops : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops := by rw [observed]; rfl
  have timeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts := by rw [observed]; rfl
  let next := serviceCore core path selected value drops retries wholeDrops timeouts queue
  exact ⟨{
    value, paths, next, gateway := rfl, work := paths.work, observed
    healthy := by rw [observed]; exact CampusTCPTwoTransferDrainObserve.afterDrain_healthy drain _
    book := rfl
    ack := by rw [observed]; cases part <;> rfl }⟩

theorem drain_lower_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (path : DataTicket initial checks current .lower monitor.exchange.forward.lower)
    (selected : path.assignedGateway = .primary)
    (source : SelectedOutput initial current path.output.produced)
    (drain : W.drainTicket current.report.final monitor = some path.ticket.id)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final .primary)
    (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    ∃ actual, Nonempty (Drained core path actual) := by
  have located : path.ticket.value.gateway = .primary := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_data_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact phase) located
    (by rw [path.ingress, selected]) (ticket_actor path) (ticket_fields path)
  obtain ⟨paths⟩ := CampusTCPTwoTransferServicePaths.data_work_at core.live.gatewayState path value source
  have observed := CampusTCPTwoTransferServicePaths.lower_drain_observe (config := cfg) paths.linked drain located healthy
  have queue := core.primaryQueue.serve_lower value.value ⟨path.phase, path.ticketRef⟩
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    apply queue.reframe <;> rfl
  exact ⟨actual, finish core path selected value paths drain observed afterQueue⟩

theorem drain_upper_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (path : DataTicket initial checks current .upper monitor.exchange.forward.upper)
    (selected : path.assignedGateway = .primary)
    (source : SelectedOutput initial current path.output.produced)
    (drain : W.drainTicket current.report.final monitor = some path.ticket.id)
    (phase : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final .primary)
    (other : ¬(monitor.exchange.forward.lower.phase = .dataTicket ∧
      monitor.exchange.forward.lower.refs.dataTicket = some path.ticket.id))
    (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    ∃ actual, Nonempty (Drained core path actual) := by
  have located : path.ticket.value.gateway = .primary := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_data_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact phase) located
    (by rw [path.ingress, selected]) (ticket_actor path) (ticket_fields path)
  obtain ⟨paths⟩ := CampusTCPTwoTransferServicePaths.data_work_at core.live.gatewayState path value source
  have observed := CampusTCPTwoTransferServicePaths.upper_drain_observe (config := cfg) paths.linked drain located other healthy
  have queue := core.primaryQueue.serve_upper value.value ⟨path.phase, path.ticketRef⟩
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    apply queue.reframe <;> rfl
  exact ⟨actual, finish core path selected value paths drain observed afterQueue⟩

end Netlib.Check.CampusTCPTwoTransferLocatedDrain
