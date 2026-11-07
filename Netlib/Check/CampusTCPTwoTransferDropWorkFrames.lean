import Netlib.Check.CampusTCPTwoTransferLocatedDrop
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoProgressPathsDistinct
import Netlib.Check.CampusTCPTwoProgressPathRetain

namespace Netlib.Check.CampusTCPTwoTransferDropWorkFrames

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork
open CampusTCPTwoProgressPaths

namespace P
export CampusTCPTwoProgressPaths (Ingress Link)
end P

namespace D
export CampusTCPTwoTransferLocatedDrop (Selected Dropped Result)
end D

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {item : Theory.PacketCustody.Item (Transit input)}
variable {target : CampusTCPTwoProgressMonitor.DropTarget}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {produced : Produced input.active input.passive} {packetID : Nat}
variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
variable {fields : Produced input.active input.passive → Prop} {header : Header}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem ingress_source (path : P.Ingress current actor fields) (selected : D.Selected core item target actual)
    (identity : path.packetID = item.id) : selected.loss.source = path.output.produced := by
  obtain ⟨stored, member, id, payload⟩ := path.custody_item
  have same : item = stored := selected.resolved.symm.trans
    (selected.appended.facts.resolved.item_eq (CampusTCPCustodyFacts.Report.valid current.report)
      stored member (id.trans identity))
  exact selected.source_ingress (by rw [same]; exact payload)

theorem link_source (path : P.Link current actor fields header) (selected : D.Selected core item target actual)
    (identity : path.packetID = item.id) : selected.loss.source = path.served.ticket.value.produced := by
  obtain ⟨stored, member, id, payload⟩ := path.custody_item
  have same : item = stored := selected.resolved.symm.trans
    (selected.appended.facts.resolved.item_eq (CampusTCPCustodyFacts.Report.valid current.report)
      stored member (id.trans identity))
  exact selected.source_link path.served path.emission path.emitted (by rw [same]; exact payload)

def keepDataWork (work : DataWork initial checks current core.live.gatewayState part lane)
    (drop : D.Dropped core produced packetID target actual) {nextBook : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : D.Result drop.selected nextBook)
    (different : ∀ other, other.actor = sender →
      CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) other → produced ≠ other) :
    DataWork initial checks drop.selected.appended.move.after result.next.live.gatewayState part lane := by
  have ingressOther (path : DataIngress initial current part lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := ingress_source path.toIngress drop.selected (Option.some.inj same).symm
    exact different path.output.produced path.output.actor path.output.fields (drop.sourceEq.symm.trans source)
  have linkOther (path : DataLink initial current part lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := link_source path.toLink drop.selected (Option.some.inj same).symm
    exact different path.served.ticket.value.produced path.actor path.fields (drop.sourceEq.symm.trans source)
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move drop.selected.appended.move (ingressOther path))
      (source.retain_steps drop.selected.appended.move.retained)
  | ticket path located source =>
    exact .ticket (path.after_quiet drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial))
      located (source.retain_steps drop.selected.appended.move.retained)
  | link path source covered =>
    exact .link (path.after_move drop.selected.appended.move (linkOther path))
      (source.retain_steps drop.selected.appended.move.retained) (by rw [result.range]; exact covered)

def keepOriginalLane (work : OriginalLane initial checks current core.live.gatewayState received part lane)
    (drop : D.Dropped core produced packetID target actual) {nextBook : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : D.Result drop.selected nextBook)
    (different : ∀ other, other.actor = sender →
      CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) other → produced ≠ other) :
    OriginalLane initial checks drop.selected.appended.move.after result.next.live.gatewayState received part lane := by
  cases work with
  | done phase => exact .done phase
  | active work missing => exact .active (keepDataWork work drop result different) missing

theorem actors_ne (first second : Produced input.active input.passive)
    (data : first.actor = sender) (ack : second.actor = sender.other) : first ≠ second := by
  intro same
  have actors := data.symm.trans ((congrArg Produced.actor same).trans ack)
  cases sender <;> cases actors

def keepAckWork (work : AckWork checks core.live lane)
    (drop : D.Dropped core produced packetID target actual) {nextBook : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : D.Result drop.selected nextBook) (data : produced.actor = sender) :
    AckWork checks result.next.live lane := by
  have ingressOther (path : AckIngress initial current (received.bytes lower upper).length lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := ingress_source path.toIngress drop.selected (Option.some.inj same).symm
    exact actors_ne produced path.output.produced data path.output.actor (drop.sourceEq.symm.trans source)
  have linkOther (path : AckLink initial current (received.bytes lower upper).length lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := link_source path.toLink drop.selected (Option.some.inj same).symm
    exact actors_ne produced path.served.ticket.value.produced data path.actor (drop.sourceEq.symm.trans source)
  cases work with
  | pending phase queue => exact .pending phase (by rw [result.receiver_reaction]; exact queue)
  | ingress path => exact .ingress (path.after_move drop.selected.appended.move (ingressOther path))
  | ticket path located =>
    exact .ticket (path.after_quiet drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial)) located
  | link path => exact .link (path.after_move drop.selected.appended.move (linkOther path))

end Netlib.Check.CampusTCPTwoTransferDropWorkFrames
