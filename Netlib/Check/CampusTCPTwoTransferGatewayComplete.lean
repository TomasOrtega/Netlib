import Netlib.Check.CampusTCPTwoTransferEvidenceRead
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

/-!
# Gateway settlement at the actual located read boundary

Both admitted ranges and the full ACK belong to the current task.
The same read retains the gateway session and its actual coverage sources.
-/

namespace Netlib.Check.CampusTCPTwoTransferGatewayComplete

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferLocatedCore (Core)
open CampusTCPTwoTransferNative (Checks Routing)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location target : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure Facts (view : ViewAt initial current location) : Prop where
  lowerPresent : view.ranges.lowerRun.isSome = true
  upperPresent : view.ranges.upperRun.isSome = true
  mainAck : (view.gateway.session.lane sender.direction).acknowledged =
    initial.geometry.«prefix» + (lower ++ upper).length
  peerAck : (view.gateway.session.peer sender.direction).acknowledged =
    (view.gateway.session.peer sender.direction).observed
  peerWindow : CampusTCPTwoTransferState.PeerReserved view


theorem session_same (before : ViewAt initial current location) (after : ViewAt initial next target)
    (same : beforeService input next.report.final target = beforeService input current.report.final location) :
    after.gateway.session = before.gateway.session := by
  have phase := after.gateway.phase
  rw [same, before.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm


theorem ranges_same (before : ViewAt initial current location) (after : ViewAt initial next target)
    (same : beforeService input next.report.final target = beforeService input current.report.final location) :
    after.ranges.lowerRun = before.ranges.lowerRun ∧ after.ranges.upperRun = before.ranges.upperRun := by
  have session := session_same before after same
  apply after.ranges.unique before.ranges initial.lowerNonempty
  rw [session]


theorem Facts.same_service {before : ViewAt initial current location} (facts : Facts before)
    (after : ViewAt initial next target)
    (same : beforeService input next.report.final target = beforeService input current.report.final location) : Facts after := by
  have ranges := ranges_same before after same
  have session := session_same before after same
  exact {
    lowerPresent := by rw [ranges.1]; exact facts.lowerPresent
    upperPresent := by rw [ranges.2]; exact facts.upperPresent
    mainAck := by rw [session]; exact facts.mainAck
    peerAck := by rw [session]; exact facts.peerAck
    peerWindow := by
      unfold CampusTCPTwoTransferState.PeerReserved
      rw [session]
      exact facts.peerWindow }


theorem Facts.main_observed {view : ViewAt initial current location} (facts : Facts view) :
    (view.gateway.session.lane sender.direction).observed = initial.geometry.«prefix» + (lower ++ upper).length := by
  rw [view.observed, facts.lowerPresent, facts.upperPresent]
  simp only [ite_true, List.length_append, Nat.add_assoc]


theorem Facts.main_highEnd {view : ViewAt initial current location} (facts : Facts view) :
    (view.gateway.session.lane sender.direction).highEnd = initial.geometry.«prefix» + (lower ++ upper).length := by
  rw [view.highEnd, facts.upperPresent]
  simp only [ite_true, List.length_append, Nat.add_assoc]


theorem peer_complete (view : ViewAt initial current location) :
    (view.gateway.session.peer sender.direction).observed = (view.gateway.session.peer sender.direction).highEnd := by
  change (view.gateway.session.peer sender.direction).coverage.frontier =
    (view.gateway.session.peer sender.direction).coverage.highEnd
  rw [view.peerCoverage]
  exact initial.geometry.peerComplete


theorem Facts.peer_complete {view : ViewAt initial current location} (facts : Facts view) :
    (view.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).highEnd :=
  facts.peerAck.trans (CampusTCPTwoTransferGatewayComplete.peer_complete view)


theorem of_core {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
    {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
    {monitor : CampusTCPTwoTransferMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .allReleased)
    (mainAck : (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (lower ++ upper).length) : Facts core.live.gatewayState := by
  have lowerPresent := core.covered .lower trivial
  have upperPresent := core.covered .upper trivial
  change core.live.gatewayState.ranges.lowerRun.isSome = true at lowerPresent
  change core.live.gatewayState.ranges.upperRun.isSome = true at upperPresent
  exact ⟨lowerPresent, upperPresent, mainAck, core.peerSettled (.inl lowerPresent), core.peerWindow⟩

end Netlib.Check.CampusTCPTwoTransferGatewayComplete

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}

theorem ReadAdvanced.gateway_complete (advance : ReadAdvanced evidence actual) :
    CampusTCPTwoTransferGatewayComplete.Facts advance.value.gatewayState :=
  (CampusTCPTwoTransferGatewayComplete.of_core advance.core advance.mainAck).same_service
    advance.value.gatewayState (advance.value.value.gateway location)

end Netlib.Check.CampusTCPTwoTransferEvidence
