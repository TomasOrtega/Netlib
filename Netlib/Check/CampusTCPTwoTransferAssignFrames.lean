import Netlib.Check.CampusTCPTwoTransferLocatedAssign
import Netlib.Check.CampusTCPTwoProgressPhaseNetworkState

/-!
# Frames for the same actual assignment

Distinct current custody items retain unselected paths. The actual assignment
keeps endpoint recovery, gateway ranges, and all existing loss causes.
-/

namespace Netlib.Check.CampusTCPTwoTransferAssignFrames

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (DataIngress DataLink)
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferAdmission (rangeAt)

namespace N
export CampusTCPTwoTransferNetwork (Assignment)
end N
namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace P
export CampusTCPTwoProgressPaths (Ingress Link)
end P
namespace F
export CampusTCPTwoProgressPhaseNetworkState (Frame)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor other : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {actual : Step input} {index : Nat} {ingress : I.InterfaceRef}
variable {produced : Produced input.active input.passive} {fields secondFields : Produced input.active input.passive → Prop}
variable {target : Packet.Header}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem pending_eq (first second : Theory.PacketCustody.Item (Transit input))
    (firstMember : first ∈ current.report.final.custody.pending)
    (secondMember : second ∈ current.report.final.custody.pending) (same : first.id = second.id) : first = second := by
  obtain ⟨resolved, _⟩ := Theory.PacketCustody.resolve_completes current.report.final.custody first firstMember .assigned
  have valid := CampusTCPCustodyFacts.Report.valid current.report
  exact (resolved.item_eq valid first firstMember rfl).symm.trans (resolved.item_eq valid second secondMember same.symm)

theorem ingress_packet_ne (first : P.Ingress current actor fields) (second : P.Ingress current other secondFields)
    (different : first.output.produced ≠ second.output.produced) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  exact different (congrArg CampusTCPTwoProgressLossHistory.transitSource payload)

theorem ingress_link_packet_ne (first : P.Ingress current actor fields) (second : P.Link current other secondFields target) :
    first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  cases payload

private theorem ingress_other (selected : P.Ingress current actor fields)
    (value : N.Assignment current selected.output.index ingress selected.output.produced actual)
    (id : Nat) (different : selected.packetID ≠ id) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some id := by
  rw [value.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket, selected.custody]
  exact fun same => different (Option.some.inj same)

def data_after {view : ViewAt initial current location} (selected : P.Ingress current actor fields)
    (value : N.Assignment current selected.output.index ingress selected.output.produced actual)
    (work : DataWork initial checks current view part lane)
    (different : ∀ path : DataIngress initial current part lane, selected.output.produced ≠ path.output.produced) :
    DataWork initial checks value.move.after (view.reframe (value.serviceFrame location)) part lane := by
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move value.move (ingress_other selected value path.packetID
      (ingress_packet_ne selected path.toIngress (different path)))) (source.retain_steps value.move.retained)
  | ticket path located source =>
    exact .ticket (path.after_assignment value) located (source.retain_steps value.move.retained)
  | link path source covered =>
    exact .link (path.after_move value.move (ingress_other selected value path.packetID
      (ingress_link_packet_ne selected path.toLink))) (source.retain_steps value.move.retained) covered

def original_after {view : ViewAt initial current location} (selected : P.Ingress current actor fields)
    (value : N.Assignment current selected.output.index ingress selected.output.produced actual)
    (work : OriginalLane initial checks current view received part lane)
    (different : ∀ path : DataIngress initial current part lane, selected.output.produced ≠ path.output.produced) :
    OriginalLane initial checks value.move.after (view.reframe (value.serviceFrame location)) received part lane := by
  cases work with
  | active work missing => exact .active (data_after selected value work different) missing
  | done phase => exact .done phase

theorem sender_recovery
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : N.Assignment current index ingress produced actual)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received) :
    next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (next.live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))

def assemble
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    (active : Active core) (value : N.Assignment current index ingress produced actual)
    (next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received)
    (book : next.losses.book = core.losses.book)
    (exchange : (W.observe cfg monitor actual).exchange.mode = monitor.exchange.mode)
    (frame : F.Frame monitor.exchange.forward (W.observe cfg monitor actual).exchange.forward)
    (lowerLane : OriginalLane initial checks value.move.after next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower)
    (upperLane : OriginalLane initial checks value.move.after next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper)
    (retry : RetryLane initial checks value.move.after next.live.gatewayState sent (W.observe cfg monitor actual).exchange.forward.retry)
    (ack : AckState checks next.live (W.observe cfg monitor actual).exchange.forward.ack)
    (ackGateway : ∀ lane, (W.observe cfg monitor actual).exchange.forward.ack = some lane → lane.phase = .ackLink →
      (next.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
        initial.geometry.«prefix» + (received.bytes lower upper).length) : Active next := by
  let raw := (W.observe cfg monitor actual).exchange.forward
  change AckState checks next.live raw.ack at ack
  have someBefore : raw.ack.isSome = true → monitor.exchange.forward.ack.isSome = true := by
    intro pending
    cases old : monitor.exchange.forward.ack with
    | none => rw [frame.ackNone.mpr old] at pending; cases pending
    | some lane => rfl
  have runtime := sender_recovery core value next
  refine {
    exchange := exchange.trans active.exchange
    mode := by rw [frame.mode]; exact active.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane, retry, ack, ackGateway
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_
    recoveryHead := fun mode waiting => active.recoveryHead (frame.mode ▸ mode) (frame.waiting ▸ waiting)
    originalOpen := ?_, debt := ?_, upperMissing := ?_, zeroAck := ?_
    sources := (CampusTCPTwoTransferSources.Frame.assignment value).receipts active.sources }
  · intro mode
    obtain ⟨done, waiting, retries⟩ := active.originals (frame.mode ▸ mode)
    exact ⟨frame.retryDone.mpr done, frame.waiting.trans waiting, frame.retries.trans retries⟩
  · intro mode
    obtain ⟨first, second⟩ := active.recovery (frame.mode ▸ mode)
    exact ⟨frame.lowerDone.mpr first, frame.upperDone.mpr second⟩
  · intro pending
    exact frame.retryDone.mpr (active.serial (someBefore pending))
  · intro pending
    exact active.ackNonempty (someBefore pending)
  · intro waiting
    obtain ⟨ack, done⟩ := active.waiting (frame.waiting ▸ waiting)
    exact ⟨frame.ackNone.mpr ack, frame.retryDone.mpr done⟩
  · intro mode waiting ack done
    exact active.runnable (frame.mode ▸ mode) (frame.waiting ▸ waiting) (frame.ackNone.mp ack) (frame.retryDone.mp done)
  · intro mode ack both
    exact active.originalOpen (frame.mode ▸ mode) (frame.ackNone.mp ack)
      ⟨frame.lowerDone.mp both.1, frame.upperDone.mp both.2⟩
  · intro role head rest selected
    obtain ⟨debt⟩ := active.debt role head rest selected
    cases debt with
    | cause position chosen => exact ⟨.cause position (by rw [book]; exact chosen)⟩
    | lower same work => exact ⟨.lower same (lowerLane.work (fun done => work.not_done (frame.lowerDone.mp done)))⟩
    | upper same work => exact ⟨.upper same (upperLane.work (fun done => work.not_done (frame.upperDone.mp done)))⟩
    | retry work => exact ⟨.retry (retry.work (fun done => work.not_done (frame.retryDone.mp done)) selected)⟩
    | ack lane pending _ covered =>
      have notNone : raw.ack ≠ none := by intro absent; rw [frame.ackNone.mp absent] at pending; cases pending
      cases found : raw.ack with
      | none => exact False.elim (notNone found)
      | some lane =>
        exact ⟨.ack lane found (by simpa only [AckState, found] using ack) covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (frame.upperDone.mp done)
    exact ⟨position, by rw [book]; exact chosen⟩
  · intro lane pending retired
    have old : monitor.exchange.forward.ack.isSome = true := someBefore (by rw [pending]; rfl)
    cases found : monitor.exchange.forward.ack with
    | none => rw [found] at old; cases old
    | some lane => rw [runtime]; exact active.zeroAck lane found retired

end Netlib.Check.CampusTCPTwoTransferAssignFrames
