import Netlib.Check.CampusTCPTwoProgressPhaseDrop
import Netlib.Check.CampusTCPTwoProgressPathsFrames

/-!
# Loss causes from the current packet path

Custody identity ties each loss to its literal stored source.
The raw drop target remains an explicit current priority check.
-/

namespace Netlib.Check.CampusTCPTwoProgressPathDrop

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane DropTarget Allowed dropTarget)
end M
namespace P
export CampusTCPTwoProgressPaths (Ingress Link DataIngress DataLink AckIngress AckLink)
end P
namespace D
export CampusTCPTwoProgressPhaseDrop (Selected Result lowerBook upperBook drop_at)
end D
namespace L
export CampusTCPTwoProgressLossHistory (Head Supports Book)
end L
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {item : Theory.PacketCustody.Item (Transit input)} {target : M.DropTarget}
variable {fields : Produced input.active input.passive → Prop} {header : Header}
variable {part : S.Part} {lane : M.Lane} {count packetID : Nat}
variable {produced : Produced input.active input.passive}

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

theorem drop_allowed
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor packetID = some target) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.dropPacket packetID) := by
  have healthy : monitor.mode ≠ .invalid := by
    intro invalid
    unfold M.dropTarget at chosen
    rw [invalid] at chosen
    change none = some target at chosen
    cases chosen
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mpr
  exact ⟨healthy, .inr (.inl ⟨packetID, target, rfl, chosen⟩), rfl⟩

structure Dropped (core : Core initial native quantum allowance current monitor sent received)
    (produced : Produced input.active input.passive) (packetID : Nat) (target : M.DropTarget) (actual : Step input) where
  item : Theory.PacketCustody.Item (Transit input)
  identity : item.id = packetID
  selected : D.Selected core item target actual
  sourceEq : selected.loss.source = produced
  unassigned : D.Result selected (core.losses.book.appendLoss selected.loss)

def originalTarget : S.Part → M.DropTarget
  | .lower => .lower
  | .upper => .upper

def creditBook (selected : D.Selected core item target actual) : S.Part → L.Book initial (config initial native quantum allowance)
  | .lower => D.lowerBook selected
  | .upper => D.upperBook selected

structure Credited (drop : Dropped core produced packetID target actual) (part : S.Part) where
  support : L.Supports drop.selected.loss part
  result : D.Result drop.selected (creditBook drop.selected part)

private def credited (drop : Dropped core produced packetID target actual) (support : L.Supports drop.selected.loss part) :
    Credited drop part := by
  refine ⟨support, ?_⟩
  cases part
  · exact drop.selected.credit_lower support
  · exact drop.selected.credit_upper support

theorem ingress_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.Ingress current actor fields)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some target) :
    ∃ actual : Step input, Nonempty (Dropped core path.output.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  have selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor item.id = some target := by
    rw [id]
    exact chosen
  obtain ⟨actual, selected, ⟨result⟩⟩ := D.drop_at core item member selected (drop_allowed selected)
  exact ⟨actual, ⟨⟨item, id, selected, selected.source_ingress payload, result⟩⟩⟩

theorem link_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.Link current actor fields header)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some target) :
    ∃ actual : Step input, Nonempty (Dropped core path.served.ticket.value.produced path.packetID target actual) := by
  obtain ⟨item, member, id, payload⟩ := path.custody_item
  have selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor item.id = some target := by
    rw [id]
    exact chosen
  obtain ⟨actual, selected, ⟨result⟩⟩ := D.drop_at core item member selected (drop_allowed selected)
  exact ⟨actual, ⟨⟨item, id, selected, selected.source_link path.served path.emission path.emitted payload, result⟩⟩⟩

private theorem original_support (drop : Dropped core produced packetID (originalTarget part) actual)
    (actor : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    L.Supports drop.selected.loss part := by
  cases part
  · apply Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.lower rfl
    · rw [drop.sourceEq]; exact actor
    · rw [drop.sourceEq]; exact fields
  · apply Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.upper rfl
    · rw [drop.sourceEq]; exact actor
    · rw [drop.sourceEq]; exact fields

private theorem retry_support (drop : Dropped core produced packetID .retry actual)
    (head : L.Head initial current part) (actor : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) produced) :
    L.Supports drop.selected.loss part := by
  apply Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.retry part rfl head
  · rw [drop.sourceEq]; exact actor
  · rw [drop.sourceEq]; exact fields

private theorem ack_support (drop : Dropped core produced packetID .ack actual)
    (head : L.Head initial current part) (actor : produced.actor = sender.other)
    (fields : CampusTCPTwoProgressWire.AckFields initial count produced)
    (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count) : L.Supports drop.selected.loss part := by
  apply Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.ack part rfl head count
  · rw [drop.sourceEq]; exact actor
  · rw [drop.sourceEq]; exact fields
  · exact within
  · exact covered

theorem original_ingress_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataIngress initial current part lane)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some (originalTarget part)) :
    ∃ actual : Step input, ∃ drop : Dropped core path.output.produced path.packetID (originalTarget part) actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core path.toIngress chosen
  exact ⟨actual, drop, ⟨credited drop (original_support drop path.output.actor path.output.fields)⟩⟩

theorem original_link_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataLink initial current part lane)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some (originalTarget part)) :
    ∃ actual : Step input, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID (originalTarget part) actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core path.toLink chosen
  exact ⟨actual, drop, ⟨credited drop (original_support drop path.actor path.fields)⟩⟩

theorem retry_ingress_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataIngress initial current part lane) (head : L.Head initial current part)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .retry) :
    ∃ actual : Step input, ∃ drop : Dropped core path.output.produced path.packetID .retry actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core path.toIngress chosen
  exact ⟨actual, drop, ⟨credited drop (retry_support drop head path.output.actor path.output.fields)⟩⟩

theorem retry_link_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.DataLink initial current part lane) (head : L.Head initial current part)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .retry) :
    ∃ actual : Step input, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .retry actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core path.toLink chosen
  exact ⟨actual, drop, ⟨credited drop (retry_support drop head path.actor path.fields)⟩⟩

theorem ack_ingress_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckIngress initial current count lane) (head : L.Head initial current part)
    (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack) :
    ∃ actual : Step input, ∃ drop : Dropped core path.output.produced path.packetID .ack actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core path.toIngress chosen
  exact ⟨actual, drop, ⟨credited drop (ack_support drop head path.output.actor path.output.fields within covered)⟩⟩

theorem ack_link_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current count lane) (head : L.Head initial current part)
    (within : count ≤ lower.length + upper.length)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ count)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack) :
    ∃ actual : Step input, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .ack actual,
      Nonempty (Credited drop part) := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core path.toLink chosen
  exact ⟨actual, drop, ⟨credited drop (ack_support drop head path.actor path.fields within covered)⟩⟩

theorem gap_ack_ingress_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckIngress initial current 0 lane)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack) :
    ∃ actual : Step input, ∃ drop : Dropped core path.output.produced path.packetID .ack actual,
      ∀ part, ¬L.Supports drop.selected.loss part := by
  obtain ⟨actual, ⟨drop⟩⟩ := ingress_at core path.toIngress chosen
  refine ⟨actual, drop, fun part => Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.no_gap_ack rfl ?_⟩
  rw [drop.sourceEq]
  exact path.output.fields

theorem gap_ack_link_at (core : Core initial native quantum allowance current monitor sent received)
    (path : P.AckLink initial current 0 lane)
    (chosen : M.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .ack) :
    ∃ actual : Step input, ∃ drop : Dropped core path.served.ticket.value.produced path.packetID .ack actual,
      ∀ part, ¬L.Supports drop.selected.loss part := by
  obtain ⟨actual, ⟨drop⟩⟩ := link_at core path.toLink chosen
  refine ⟨actual, drop, fun part => Netlib.Check.CampusTCPTwoProgressLossHistory.Supports.no_gap_ack rfl ?_⟩
  rw [drop.sourceEq]
  exact path.fields

end Netlib.Check.CampusTCPTwoProgressPathDrop
