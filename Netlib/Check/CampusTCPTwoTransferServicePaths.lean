import Netlib.Check.CampusTCPTwoTransferWork
import Netlib.Check.CampusTCPTwoTransferSources
import Netlib.Check.CampusTCPTwoTransferDrainObserve

/-!
# Actual serviced data links at the current gateway

The stored service supplies the link and its custody identity.
Selected writer evidence follows that same produced packet.
-/

namespace Netlib.Check.CampusTCPTwoTransferServicePaths

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferNative (Checks)
open CampusTCPTwoTransferPaths (DataTicket DataLink)
open CampusTCPTwoTransferWork (DataWork)
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoTransferDrainObserve (linkLane afterDrain)

namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace A
export CampusTCPTwoTransferAdmission (DataServed)
end A
namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {view : ViewAt initial current location} {actual : Step input}
variable {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

structure Linked (view : ViewAt initial current location) (path : DataTicket initial checks current part lane)
    (value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session actual served emission emitted) where
  packetID : Nat
  custody : actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packetID
  link : DataLink initial value.move.after part (linkLane lane current.report.final.services.length packetID)
  observed : CampusTCPTwoProgressMonitor.Lane.ofGap (CampusTCPGapProgressMonitor.observeService lane.toGap actual true .dataLink) =
    linkLane lane current.report.final.services.length packetID
  index : link.index = current.report.final.services.length
  served : link.served = served
  produced : link.served.ticket.value.produced = path.output.produced
  source : SelectedOutput initial value.move.after link.served.ticket.value.produced

theorem link_at (view : ViewAt initial current location) (path : DataTicket initial checks current part lane)
    (value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session actual served emission emitted)
    (source : SelectedOutput initial current path.output.produced) : Nonempty (Linked view path value) := by
  have fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper)
      served.ticket.value.produced := by
    rw [value.facts.ticket, path.toTicketPath.produced]
    exact path.output.fields
  have actor : served.ticket.value.produced.actor = sender := by
    rw [value.facts.ticket, path.toTicketPath.produced]
    exact path.output.actor
  have produced : served.ticket.value.produced = path.output.produced := by
    rw [value.facts.ticket, path.toTicketPath.produced]
  obtain ⟨packetID, custody⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at custody
  have observed : CampusTCPTwoProgressMonitor.Lane.ofGap (CampusTCPGapProgressMonitor.observeService lane.toGap actual true .dataLink) =
      linkLane lane current.report.final.services.length packetID := by
    simp only [CampusTCPGapProgressMonitor.observeService, value.facts.recorded, value.move.beforeEq, emitted, custody,
      CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap, linkLane, ite_true]
  let link : DataLink initial value.move.after part (linkLane lane current.report.final.services.length packetID) := {
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
  exact ⟨⟨packetID, custody, link, observed, rfl, rfl, produced,
    ((CampusTCPTwoTransferSources.Frame.service value).selected source).reindex produced.symm⟩⟩

structure Serviced (view : ViewAt initial current location) (path : DataTicket initial checks current part lane)
    (value : A.DataServed view path.ticket part actual) where
  linked : Linked view path value.value
  work : DataWork initial checks value.value.move.after value.next part
    (linkLane lane current.report.final.services.length linked.packetID)

theorem data_work_at (view : ViewAt initial current location) (path : DataTicket initial checks current part lane)
    (value : A.DataServed view path.ticket part actual)
    (source : SelectedOutput initial current path.output.produced) : Nonempty (Serviced view path value) := by
  obtain ⟨linked⟩ := link_at view path value.value source
  exact ⟨⟨linked, .link linked.link linked.source value.covered⟩⟩

variable {config : CampusTCPTwoTransferMonitor.Config} {monitor : W.Monitor}

theorem lower_drain_observe {path : DataTicket initial checks current part monitor.exchange.forward.lower}
    {value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session actual served emission emitted}
    (linked : Linked view path value)
    (selected : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = some path.ticket.id)
    (primary : path.ticket.value.gateway = .primary) (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    CampusTCPTwoTransferMonitor.observe config monitor actual = afterDrain monitor
      { monitor.exchange.forward with
        lower := linkLane monitor.exchange.forward.lower current.report.final.services.length linked.packetID
        lastOriginal := some .lower } := by
  obtain ⟨packet, custody, observed⟩ := CampusTCPTwoTransferDrainObserve.lower_observe (config := config) value selected primary
    path.phase path.ticketRef healthy
  have same : packet = linked.packetID := Option.some.inj (custody.symm.trans linked.custody)
  exact same ▸ observed

theorem upper_drain_observe {path : DataTicket initial checks current part monitor.exchange.forward.upper}
    {value : N.Service current path.ticket ⟨view.gateway.session.entry.flow, sender.direction⟩
      view.gateway.session actual served emission emitted}
    (linked : Linked view path value)
    (selected : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = some path.ticket.id)
    (primary : path.ticket.value.gateway = .primary)
    (other : ¬(monitor.exchange.forward.lower.phase = .dataTicket ∧
      monitor.exchange.forward.lower.refs.dataTicket = some path.ticket.id))
    (healthy : monitor.exchange.forward.mode ≠ .invalid) :
    CampusTCPTwoTransferMonitor.observe config monitor actual = afterDrain monitor
      { monitor.exchange.forward with
        upper := linkLane monitor.exchange.forward.upper current.report.final.services.length linked.packetID
        lastOriginal := some .upper } := by
  obtain ⟨packet, custody, observed⟩ := CampusTCPTwoTransferDrainObserve.upper_observe (config := config) value selected primary
    path.phase path.ticketRef other healthy
  have same : packet = linked.packetID := Option.some.inj (custody.symm.trans linked.custody)
  exact same ▸ observed

end Netlib.Check.CampusTCPTwoTransferServicePaths
