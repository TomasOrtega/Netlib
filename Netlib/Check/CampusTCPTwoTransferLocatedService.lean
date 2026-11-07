import Netlib.Check.CampusTCPTwoTransferServiceObserve
import Netlib.Check.CampusTCPTwoTransferServiceFrames
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoTransferControlState
import Netlib.Check.CampusTCPTwoProgressPathsDistinct

/-!
# Ordinary service from the current located task

Current tickets and gateway geometry derive each actual service.
The same service supplies the next view, link, and retained source history.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedService

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt Reserved Settled PeerReserved)
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferPaths (DataTicket AckTicket AckLink)
open CampusTCPTwoTransferWork (DataWork)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoTransferServiceObserve (afterService ackLinkLane)
open CampusTCPTwoTransferDrainObserve (linkLane)

namespace A
export CampusTCPTwoTransferAdmission (DataServed AckServed serve_data_at serve_ack_at rangeAt)
end A
namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace P
export CampusTCPTwoTransferServicePaths (Serviced)
end P
namespace F
export CampusTCPTwoTransferServiceFrames (live_after data_frames ack_frames)
end F
namespace O
export CampusTCPTwoTransferServiceObserve (lower_observe upper_observe retry_observe ack_observe)
end O
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe Allowed controlDemand)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem data_actor (path : DataTicket initial checks current part lane) :
    path.ticket.value.produced.actor = sender := by rw [path.toTicketPath.produced]; exact path.output.actor

private theorem data_fields (path : DataTicket initial checks current part lane) :
    CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) path.ticket.value.produced := by
  rw [path.toTicketPath.produced]
  exact path.output.fields

private theorem ack_actor (path : AckTicket initial checks current count lane) :
    path.ticket.value.produced.actor = sender.other := by rw [path.toTicketPath.produced]; exact path.output.actor

private theorem ack_fields (path : AckTicket initial checks current count lane) :
    CampusTCPTwoProgressWire.AckFields initial count path.ticket.value.produced := by
  rw [path.toTicketPath.produced]
  exact path.output.fields

theorem service_phase (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) :
    CampusTCPGatewayEnabled.ServicePhaseReady current.report.final location := by
  generalize equation : monitor.mode = mode at phase ordinary
  cases phase with
  | armed fields => exact ⟨fun _ => ⟨fields.unsealed, fields.unfenced⟩, fun impossible => by cases impossible⟩
  | finished fields =>
    constructor
    · intro impossible; cases impossible
    · intro _; exact ⟨fields.unpaused, fields.installed⟩
  | capture | install | clientRoute | serverRoute | fence | resume =>
    rcases ordinary with impossible | impossible <;> cases impossible

private theorem control_none (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (allowed : W.Allowed cfg current.report.final monitor (.serve ticket none)) : W.controlDemand monitor = none := by
  have valid : monitor.mode ≠ .invalid := by rcases ordinary with mode | mode <;> rw [mode] <;> decide
  have drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none := by
    apply CampusTCPTwoTransferControlObserve.noDrain_of_non_capture
    rcases ordinary with mode | mode <;> rw [mode] <;> decide
  cases selected : W.controlDemand monitor with
  | none => rfl
  | some kind =>
    have impossible := allowed
    simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, valid, decide_false, Bool.false_eq_true,
      ite_false, drainless, selected] at impossible
    cases kind <;> simp only [CampusTCPTwoTransferMonitor.Control.serves, Bool.false_eq_true] at impossible

private def serviceCore (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received)
    (value : N.Service current item hit session actual served emission emitted)
    (nextView : ViewAt initial value.move.after location) (space : Reserved nextView)
    (gatewayAck : (nextView.gateway.session.lane sender.direction).acknowledged ≤
      initial.geometry.«prefix» + (received.bytes lower upper).length)
    (settled : Settled nextView) (peerSpace : PeerReserved nextView)
    (covered : ∀ role, CampusTCPTwoProgressPhaseBase.Arrived received role → (A.rangeAt nextView role).isSome = true)
    (dropIDs : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops)
    (retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries)
    (wholeDropIDs : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops)
    (wholeTimeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts)
    (queue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final (W.observe cfg monitor actual).exchange.forward) :
    Core initial checks routing quantum allowance reverseLower reverseUpper
      value.move.after (W.observe cfg monitor actual) location sent received := by
  let raw := F.live_after core.live value nextView space
  let live : LiveAt initial value.move.after location sent (W.observe cfg monitor actual).exchange.forward.retries received := {
    anchor := raw.anchor
    senderFlight := by rw [retries]; exact raw.senderFlight
    receiverFacts := raw.receiverFacts
    gatewayState := nextView
    gatewayWindow := space
    history := raw.history }
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
    exact Option.some.inj (live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))
  let sources := CampusTCPTwoTransferSources.Frame.service value
  exact {
    live
    senderWindow := by rw [value.endpoints]; exact core.senderWindow
    originals := sources.originals core.originals
    originalTimes := core.originalTimes
    writer := sources.writer core.writer
    losses := core.losses.append value.move
      (by simp only [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.facts.event])
      dropIDs retries wholeDropIDs wholeTimeouts
    lossBound := by rw [dropIDs]; exact core.lossBound
    primaryQueue := queue
    retired := core.retired
    gatewayAck, peerSettled := settled, peerWindow := peerSpace, covered
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := by rw [recovery]; exact core.emptyDuplicate
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, retries]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, retries]; exact core.rtoPending }

private theorem queue_service (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received)
    (value : N.Service current item hit session actual served emission emitted) :
    CampusTCPTwoTransferQueue.Closed value.move.after.report.final monitor.exchange.forward := by
  obtain ⟨completed, _, _, work⟩ := value.facts.completed
  intro pending member primary
  have afterMember : pending ∈ completed.state.pending := by simpa only [value.move.final, work] using member
  have beforeMember : pending ∈ current.report.final.work.pending := by
    rw [← value.move.beforeEq]
    exact completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ afterMember)
  exact core.primaryQueue pending beforeMember primary

inductive DataTarget where
  | lower | upper | retry
  deriving DecidableEq

def DataTarget.update (target : DataTarget) (monitor : M.Monitor) (lane : M.Lane) : M.Monitor :=
  match target with
  | .lower => { monitor with lower := lane, lastOriginal := some .lower }
  | .upper => { monitor with upper := lane, lastOriginal := some .upper }
  | .retry => { monitor with retry := lane }

structure DataServiced (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (path : DataTicket initial checks current part lane)
    (target : DataTarget) (actual : Step input) where
  value : A.DataServed core.live.gatewayState path.ticket part actual
  paths : P.Serviced core.live.gatewayState path value
  next : Core initial checks routing quantum allowance reverseLower reverseUpper
    value.value.move.after (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = value.next
  work : DataWork initial checks value.value.move.after next.live.gatewayState part
    (linkLane lane current.report.final.services.length paths.linked.packetID)
  observed : W.observe cfg monitor actual = afterService monitor (target.update monitor.exchange.forward
    (linkLane lane current.report.final.services.length paths.linked.packetID))
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book
  ack : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack

private theorem data_finish (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (path : DataTicket initial checks current part lane)
    (selected : path.assignedGateway = location) (target : DataTarget)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (value : A.DataServed core.live.gatewayState path.ticket part actual)
    (paths : P.Serviced core.live.gatewayState path value)
    (observed : W.observe cfg monitor actual = afterService monitor (target.update monitor.exchange.forward
      (linkLane lane current.report.final.services.length paths.linked.packetID)))
    (queue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward) :
    Nonempty (DataServiced core path target actual) := by
  have located : path.ticket.value.gateway = location := path.ticket_gateway.trans selected
  have drops : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops := by
    rw [observed]; cases target <;> rfl
  have retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by
    rw [observed]; cases target <;> rfl
  have wholeDrops : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops := by rw [observed]; rfl
  have timeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts := by rw [observed]; rfl
  have frames := F.data_frames core.live.gatewayState value located (data_fields path) core.peerWindow
  let next := serviceCore core value.value value.next value.reserved (by rw [frames.1]; exact core.gatewayAck)
    frames.2.1 frames.2.2 (fun role arrived => value.preserved role (core.covered role arrived))
    drops retries wholeDrops timeouts queue
  exact ⟨{
    value, paths, next, gateway := rfl, work := paths.work, observed
    healthy := by rw [observed]; exact CampusTCPTwoTransferServiceObserve.afterService_healthy ordinary _
    book := rfl
    ack := by rw [observed]; cases target <;> rfl }⟩

theorem lower_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (path : DataTicket initial checks current .lower monitor.exchange.forward.lower)
    (selected : path.assignedGateway = location) (source : SelectedOutput initial current path.output.produced)
    (allowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none))
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none) :
    ∃ actual, Nonempty (DataServiced core path .lower actual) := by
  have located : path.ticket.value.gateway = location := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_data_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact service_phase phase ordinary) located
    (by rw [path.ingress, selected]) (data_actor path) (data_fields path)
  obtain ⟨paths⟩ := CampusTCPTwoTransferServicePaths.data_work_at core.live.gatewayState path value source
  obtain ⟨packet, custody, observed⟩ := O.lower_observe (config := cfg) value.value ordinary (control_none ordinary allowed)
    active.exchange (by rw [value.value.facts.event]; exact allowed) mode path.phase path.ticketRef active.upper_not_needSend ack
  have packetEq : packet = paths.linked.packetID := Option.some.inj (custody.symm.trans paths.linked.custody)
  subst packet
  have queue := core.primaryQueue.serve_lower value.value ⟨path.phase, path.ticketRef⟩
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    apply queue.reframe <;> rfl
  exact ⟨actual, data_finish core path selected .lower ordinary value paths observed afterQueue⟩

private theorem ticket_id_ne (first : DataTicket initial checks current .lower firstLane)
    (second : DataTicket initial checks current .upper secondLane) : first.ticket.id ≠ second.ticket.id := by
  intro same
  have valid := CampusTCPOrigins.Report.work_valid current.report
  obtain ⟨completed, _, identity⟩ := Theory.Outstanding.complete_item current.report.final.work first.ticket valid first.pending
  have selected := completed.item_eq valid second.ticket second.pending same.symm
  have tickets : first.ticket = second.ticket := identity.symm.trans selected
  apply CampusTCPTwoProgressPathsDistinct.produced_ne first.output.fields second.output.fields
  exact first.toTicketPath.produced.symm.trans
    ((congrArg (fun item => item.value.produced) tickets).trans second.toTicketPath.produced)

private theorem lower_unserved (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (path : DataTicket initial checks current .upper monitor.exchange.forward.upper) :
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward
        monitor.exchange.forward.lower) (.serve path.ticket.id none) = false := by
  apply Bool.eq_false_iff.mpr
  intro served
  obtain ⟨demand, selected, served⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp served
  obtain ⟨action, next, kind⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  have event : Event.serve path.ticket.id none = action.event := by
    rcases kind with same | ⟨packet, same⟩
    · rw [same] at served
      exact (CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp served
    · rw [same] at served
      rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp served with selected | dropped
      · exact selected
      · cases dropped
  cases active.lowerLane with
  | done phase =>
    simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
    cases next
  | active work _ =>
    have same := Option.some.inj (next.symm.trans (work.command_next ((cfg).at current.report.final).forward))
    rw [same] at event
    cases underlying : work.work with
    | ingress lowerPath =>
      simp only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
        CampusTCPRoundMonitor.Action.event] at event
      cases event
    | ticket lowerPath _ =>
      have idEq : path.ticket.id = lowerPath.ticket.id := by
        simpa only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
          CampusTCPRoundMonitor.Action.event, Event.serve.injEq, and_true] using event
      exact ticket_id_ne lowerPath path idEq.symm
    | link lowerPath =>
      simp only [CampusTCPTwoTransferWork.DataWork.command, underlying, CampusTCPTwoTransferWork.Work.command,
        CampusTCPRoundMonitor.Action.event] at event
      cases event

theorem upper_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (path : DataTicket initial checks current .upper monitor.exchange.forward.upper)
    (selected : path.assignedGateway = location) (source : SelectedOutput initial current path.output.produced)
    (allowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none))
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none) :
    ∃ actual, Nonempty (DataServiced core path .upper actual) := by
  have located : path.ticket.value.gateway = location := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_data_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact service_phase phase ordinary) located
    (by rw [path.ingress, selected]) (data_actor path) (data_fields path)
  obtain ⟨paths⟩ := CampusTCPTwoTransferServicePaths.data_work_at core.live.gatewayState path value source
  obtain ⟨packet, custody, observed⟩ := O.upper_observe (config := cfg) value.value ordinary (control_none ordinary allowed)
    active.exchange (by rw [value.value.facts.event]; exact allowed) mode active.lower_not_needSend path.phase path.ticketRef ack
    (by rw [value.value.move.beforeEq, value.value.facts.event]; exact lower_unserved core active path)
  have packetEq : packet = paths.linked.packetID := Option.some.inj (custody.symm.trans paths.linked.custody)
  subst packet
  have queue := core.primaryQueue.serve_upper value.value ⟨path.phase, path.ticketRef⟩
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    apply queue.reframe <;> rfl
  exact ⟨actual, data_finish core path selected .upper ordinary value paths observed afterQueue⟩

theorem retry_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (path : DataTicket initial checks current part monitor.exchange.forward.retry)
    (selected : path.assignedGateway = location) (source : SelectedOutput initial current path.output.produced)
    (allowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none))
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none)
    (waiting : monitor.exchange.forward.waiting = false) :
    ∃ actual, Nonempty (DataServiced core path .retry actual) := by
  have located : path.ticket.value.gateway = location := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_data_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact service_phase phase ordinary) located
    (by rw [path.ingress, selected]) (data_actor path) (data_fields path)
  obtain ⟨paths⟩ := CampusTCPTwoTransferServicePaths.data_work_at core.live.gatewayState path value source
  obtain ⟨packet, custody, observed⟩ := O.retry_observe (config := cfg) value.value ordinary (control_none ordinary allowed)
    active.exchange (by rw [value.value.facts.event]; exact allowed) mode path.phase ack waiting
  have packetEq : packet = paths.linked.packetID := Option.some.inj (custody.symm.trans paths.linked.custody)
  subst packet
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    exact (queue_service core value.value).reframe rfl rfl rfl rfl
  exact ⟨actual, data_finish core path selected .retry ordinary value paths observed afterQueue⟩

structure AckLinked (view : ViewAt initial current location)
    (path : AckTicket initial checks current count lane)
    (value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.other.direction⟩
      view.gateway.session actual served emission emitted) where
  packetID : Nat
  custody : actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packetID
  link : AckLink initial value.move.after count (ackLinkLane lane current.report.final.services.length packetID)
  index : link.index = current.report.final.services.length
  served : link.served = served
  produced : link.served.ticket.value.produced = path.output.produced

theorem ack_link_at (view : ViewAt initial current location) (path : AckTicket initial checks current count lane)
    (value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.other.direction⟩
      view.gateway.session actual served emission emitted) : Nonempty (AckLinked view path value) := by
  have fields : CampusTCPTwoProgressWire.AckFields initial count served.ticket.value.produced := by
    rw [value.facts.ticket]
    exact ack_fields path
  have actor : served.ticket.value.produced.actor = sender.other := by rw [value.facts.ticket]; exact ack_actor path
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at custody
  let link : AckLink initial value.move.after count (ackLinkLane lane current.report.final.services.length packetID) := {
    index := current.report.final.services.length
    served, stored := by rw [value.move.final]; exact value.facts.serviceIndex
    emission, emitted, actor
    application := by rw [value.facts.ticket, path.toTicketPath.produced]; exact path.output.application
    fields
    target := by
      change emission.target = _
      rw [← view.gateway.identity.entry]
      exact value.facts.target
    packetID, custody := by rw [value.move.final]; exact custody
    phase := rfl, serviceRef := rfl, packetRef := rfl }
  exact ⟨⟨packetID, custody, link, rfl, rfl, by rw [value.facts.ticket, path.toTicketPath.produced]⟩⟩

structure AckServiced (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received)
    (path : AckTicket initial checks current (received.bytes lower upper).length lane) (actual : Step input) where
  value : A.AckServed core.live.gatewayState path.ticket (received.bytes lower upper).length actual
  paths : AckLinked core.live.gatewayState path value.value
  next : Core initial checks routing quantum allowance reverseLower reverseUpper
    value.value.move.after (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = value.next
  observed : W.observe cfg monitor actual = afterService monitor
    { monitor.exchange.forward with ack := some (ackLinkLane lane current.report.final.services.length paths.packetID) }
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book
  acknowledged : (next.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
    initial.geometry.«prefix» + (received.bytes lower upper).length
  lowerRun : next.live.gatewayState.ranges.lowerRun = core.live.gatewayState.ranges.lowerRun
  upperRun : next.live.gatewayState.ranges.upperRun = core.live.gatewayState.ranges.upperRun

theorem ack_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (active : Active core)
    (phase : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (path : AckTicket initial checks current (received.bytes lower upper).length lane)
    (selected : path.assignedGateway = location)
    (allowed : W.Allowed cfg current.report.final monitor (.serve path.ticket.id none))
    (ack : monitor.exchange.forward.ack = some lane) : ∃ actual, Nonempty (AckServiced core path actual) := by
  have located : path.ticket.value.gateway = location := path.ticket_gateway.trans selected
  obtain ⟨actual, ⟨value⟩⟩ := A.serve_ack_at core.live.gatewayState core.live.anchor.toRetained checks core.live.gatewayWindow
    path.ticket path.pending (by rw [located]; exact service_phase phase ordinary) located
    (by rw [path.ingress, selected]) (ack_actor path) (ack_fields path) core.gateway_observed core.gatewayAck
  obtain ⟨paths⟩ := ack_link_at core.live.gatewayState path value.value
  obtain ⟨packet, custody, observed⟩ := O.ack_observe (config := cfg) value.value ordinary (control_none ordinary allowed)
    active.exchange (by rw [value.value.facts.event]; exact allowed) active.mode active.lower_not_needSend active.upper_not_needSend
    lane ack path.phase
  have packetEq : packet = paths.packetID := Option.some.inj (custody.symm.trans paths.custody)
  subst packet
  have drops : (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops := by rw [observed]; rfl
  have retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by rw [observed]; rfl
  have wholeDrops : (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops := by rw [observed]; rfl
  have timeouts : (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts := by rw [observed]; rfl
  have queue : CampusTCPTwoTransferQueue.Closed value.value.move.after.report.final (W.observe cfg monitor actual).exchange.forward := by
    rw [observed]
    exact (queue_service core value.value).reframe rfl rfl rfl rfl
  have covered : ∀ role, CampusTCPTwoProgressPhaseBase.Arrived received role → (A.rangeAt value.next role).isSome = true := by
    intro role arrived
    have old := core.covered role arrived
    cases role
    · simpa only [A.rangeAt, value.lowerRun] using old
    · simpa only [A.rangeAt, value.upperRun] using old
  have frames := F.ack_frames core.live.gatewayState value located core.peerSettled core.peerWindow
  let next := serviceCore core value.value value.next value.reserved (Nat.le_of_eq value.acknowledged)
    frames.1 frames.2.1 covered drops retries wholeDrops timeouts queue
  exact ⟨actual, ⟨{
    value, paths, next, gateway := rfl, observed
    healthy := by rw [observed]; exact CampusTCPTwoTransferServiceObserve.afterService_healthy ordinary _
    book := rfl
    acknowledged := value.acknowledged
    lowerRun := value.lowerRun
    upperRun := value.upperRun }⟩⟩

theorem DataServiced.sender_recovery {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} {path : DataTicket initial checks current part lane} {target : DataTarget}
    (value : DataServiced core path target actual) : value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.value.value.endpoints
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))

theorem AckServiced.sender_recovery {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual) : value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.value.value.endpoints
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))

theorem DataServiced.receiver_reaction {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} {path : DataTicket initial checks current part lane} {target : DataTarget}
    (value : DataServiced core path target actual) :
    value.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) value.value.value.endpoints
  exact Option.some.inj (value.next.live.receiverFacts.ackRuntime.symm.trans (same.trans core.live.receiverFacts.ackRuntime))

theorem AckServiced.receiver_reaction {core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received} {path : AckTicket initial checks current (received.bytes lower upper).length lane}
    (value : AckServiced core path actual) :
    value.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) value.value.value.endpoints
  exact Option.some.inj (value.next.live.receiverFacts.ackRuntime.symm.trans (same.trans core.live.receiverFacts.ackRuntime))

end Netlib.Check.CampusTCPTwoTransferLocatedService
