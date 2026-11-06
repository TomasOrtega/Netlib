import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPTwoProgressMonitorFacts

/-!
# Stored packet paths at the current cut

Each path selects its actual output, ticket, or emission.
The monitor references select that same current object.
-/

namespace Netlib.Check.CampusTCPTwoProgressPaths

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

namespace M
export CampusTCPTwoProgressMonitor (Config Lane)
end M
namespace R
export CampusTCPRoundMonitor (Action ingressAction ticketAction linkAction)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {fields : Produced input.active input.passive → Prop}

structure Output (current : Cut input complete) (actor : Actor)
    (fields : Produced input.active input.passive → Prop) where
  index : Nat
  produced : Produced input.active input.passive
  stored : current.report.final.outputs[index]? = some produced
  actor : produced.actor = actor
  application : CampusTCPDeliveryEnabled.ApplicationSource produced
  fields : fields produced

structure Ingress (current : Cut input complete) (actor : Actor)
    (fields : Produced input.active input.passive → Prop) where
  output : Output current actor fields
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.ingressAt output.index) = some packetID

structure TicketPath (current : Cut input complete) (actor : Actor)
    (fields : Produced input.active input.passive → Prop) (gateway : Gateway) (ingress : I.InterfaceRef) where
  output : Output current actor fields
  ticket : Work.Item (Ticket input.active input.passive)
  pending : ticket ∈ current.report.final.work.pending
  outputIndex : ticket.value.outputIndex = output.index
  produced : ticket.value.produced = output.produced
  gateway : ticket.value.gateway = gateway
  ingress : ticket.value.ingress = ingress

structure Link (current : Cut input complete) (actor : Actor)
    (fields : Produced input.active input.passive → Prop) (target : Header) where
  index : Nat
  served : Served input
  stored : current.report.final.services[index]? = some served
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  actor : served.ticket.value.produced.actor = actor
  application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced
  fields : fields served.ticket.value.produced
  target : emission.target = target
  packetID : Nat
  custody : current.report.final.custody.pendingID (Transit.linkAt index) = some packetID

variable {ingress : I.InterfaceRef} {target : Header}

theorem Ingress.pending (path : Ingress current actor fields) : IngressPending current.report.final path.output.index := by
  obtain ⟨item, member, _, selected⟩ := current.report.final.custody.pendingID_source _ _ path.custody
  exact ⟨item, member, selected⟩

theorem Ingress.action (path : Ingress current actor fields) (ingress : I.InterfaceRef) :
    R.ingressAction current.report.final (some path.output.index) (some path.packetID) ingress =
      some (.assign path.output.index ingress) := by
  simp only [R.ingressAction, path.output.stored, path.custody, bind, Option.bind,
    beq_self_eq_true, ite_true, pure]

theorem TicketPath.action (path : TicketPath current actor fields gateway ingress) :
    R.ticketAction current.report.final (some path.ticket.id) = some (.serve path.ticket.id) := by
  unfold R.ticketAction
  simp only [bind, Option.bind]
  cases found : current.report.final.work.pending.find? (fun item => item.id == path.ticket.id) with
  | none => exact False.elim ((List.find?_eq_none.mp found) path.ticket path.pending (beq_self_eq_true _))
  | some item => rfl

theorem TicketPath.completes (path : TicketPath current actor fields gateway ingress) :
    ∃ completed, Work.complete current.report.final.work path.ticket.id = .ok completed ∧ completed.item = path.ticket :=
  Theory.Outstanding.complete_item _ path.ticket (CampusTCPOrigins.Report.work_valid current.report) path.pending

theorem Link.pending (path : Link current actor fields target) : CampusTCPDeliveryEnabled.LinkPending current.report.final path.index := by
  obtain ⟨item, member, _, selected⟩ := current.report.final.custody.pendingID_source _ _ path.custody
  exact ⟨item, member, selected⟩

theorem Link.action (path : Link current actor fields target) :
    R.linkAction current.report.final (some path.index) (some path.packetID) =
      some (.deliver path.index path.emission.bytes true) := by
  simp only [R.linkAction, path.stored, path.emitted, path.custody, bind, Option.bind,
    beq_self_eq_true, ite_true, pure]

abbrev DataOutput (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (part : CampusTCPTwoProgressSender.Part) :=
  Output current sender (CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper))

abbrev AckOutput (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete) (count : Nat) :=
  Output current sender.other (CampusTCPTwoProgressWire.AckFields initial count)

structure DataIngress (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) extends
    Ingress current sender (CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper)) where
  phase : lane.phase = .dataIngress
  outputRef : lane.refs.dataOutput = some output.index
  packetRef : lane.refs.dataIngressPacket = some packetID

structure DataTicket (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) extends
    TicketPath current sender (CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper))
      gateway (native.ingress sender) where
  phase : lane.phase = .dataTicket
  outputRef : lane.refs.dataOutput = some output.index
  ticketRef : lane.refs.dataTicket = some ticket.id

structure DataLink (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) extends
    Link current sender (CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper))
      (initial.gatewayState.session.entry.flow.output sender.direction) where
  phase : lane.phase = .dataLink
  serviceRef : lane.refs.dataService = some index
  packetRef : lane.refs.dataLinkPacket = some packetID

structure AckIngress (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (count : Nat) (lane : M.Lane) extends Ingress current sender.other (CampusTCPTwoProgressWire.AckFields initial count) where
  phase : lane.phase = .ackIngress
  outputRef : lane.refs.ackOutput = some output.index
  packetRef : lane.refs.ackIngressPacket = some packetID

structure AckTicket (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (count : Nat) (lane : M.Lane) extends
    TicketPath current sender.other (CampusTCPTwoProgressWire.AckFields initial count) gateway (native.ingress sender.other) where
  phase : lane.phase = .ackTicket
  outputRef : lane.refs.ackOutput = some output.index
  ticketRef : lane.refs.ackTicket = some ticket.id

structure AckLink (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (count : Nat) (lane : M.Lane) extends
    Link current sender.other (CampusTCPTwoProgressWire.AckFields initial count)
      (initial.gatewayState.session.entry.flow.output sender.other.direction) where
  phase : lane.phase = .ackLink
  serviceRef : lane.refs.ackService = some index
  packetRef : lane.refs.ackLinkPacket = some packetID

variable {part : CampusTCPTwoProgressSender.Part} {lane : M.Lane} {count : Nat}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}

theorem DataIngress.action (path : DataIngress initial current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap =
      some (.assign path.output.index (config.toConfig.ingress config.sender)) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase,
    path.outputRef, path.packetRef]
  exact path.toIngress.action _

theorem DataTicket.action (path : DataTicket initial native current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.ticketRef]
  exact path.toTicketPath.action

theorem DataLink.action (path : DataLink initial current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.deliver path.index path.emission.bytes true) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase,
    path.serviceRef, path.packetRef]
  exact path.toLink.action

theorem AckIngress.action (path : AckIngress initial current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap =
      some (.assign path.output.index (config.toConfig.ingress config.sender.other)) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase,
    path.outputRef, path.packetRef]
  exact path.toIngress.action _

theorem AckTicket.action (path : AckTicket initial native current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.ticketRef]
  exact path.toTicketPath.action

theorem AckLink.action (path : AckLink initial current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.deliver path.index path.emission.bytes true) := by
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase,
    path.serviceRef, path.packetRef]
  exact path.toLink.action

end Netlib.Check.CampusTCPTwoProgressPaths
