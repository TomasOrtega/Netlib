import Netlib.Check.CampusTCPTwoProgressPhaseBase

/-!
# Gateway settlement after the actual full ACK

The record retains both admitted ranges and the current lane coordinates.
-/

namespace Netlib.Check.CampusTCPTwoProgressGatewayComplete

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressGatewayState
open CampusTCPTwoProgressPhaseBase (Core)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure Facts (view : View initial current) : Prop where
  lowerPresent : view.ranges.lowerRun.isSome = true
  upperPresent : view.ranges.upperRun.isSome = true
  mainAck : (view.gateway.session.lane sender.direction).acknowledged =
    initial.geometry.«prefix» + (lower ++ upper).length
  peerAck : (view.gateway.session.peer sender.direction).acknowledged =
    (view.gateway.session.peer sender.direction).observed
  peerWindow : CampusTCPTwoProgressGatewayPeerWindow.Reserved view

theorem session_same (before : View initial current) (after : View initial next)
    (same : beforeService input next.report.final gateway = beforeService input current.report.final gateway) :
    after.gateway.session = before.gateway.session := by
  have phase := after.gateway.phase
  rw [same, before.gateway.phase] at phase
  exact (Admission.Phase.data.inj phase).symm

theorem Facts.same_service {before : View initial current} (facts : Facts before) (after : View initial next)
    (same : beforeService input next.report.final gateway = beforeService input current.report.final gateway) : Facts after := by
  have ranges := before.ranges_same after same
  have session := session_same before after same
  exact {
    lowerPresent := by rw [ranges.1]; exact facts.lowerPresent
    upperPresent := by rw [ranges.2]; exact facts.upperPresent
    mainAck := by rw [session]; exact facts.mainAck
    peerAck := by rw [session]; exact facts.peerAck
    peerWindow := by
      unfold CampusTCPTwoProgressGatewayPeerWindow.Reserved
      rw [session]
      exact facts.peerWindow }

theorem Facts.main_observed {view : View initial current} (facts : Facts view) :
    (view.gateway.session.lane sender.direction).observed = initial.geometry.«prefix» + (lower ++ upper).length := by
  rw [view.observed, facts.lowerPresent, facts.upperPresent]
  simp only [ite_true, List.length_append, Nat.add_assoc]

theorem Facts.main_highEnd {view : View initial current} (facts : Facts view) :
    (view.gateway.session.lane sender.direction).highEnd = initial.geometry.«prefix» + (lower ++ upper).length := by
  rw [view.highEnd, facts.upperPresent]
  simp only [ite_true, List.length_append, Nat.add_assoc]

theorem peer_complete (view : View initial current) :
    (view.gateway.session.peer sender.direction).observed = (view.gateway.session.peer sender.direction).highEnd := by
  change (view.gateway.session.peer sender.direction).coverage.frontier =
    (view.gateway.session.peer sender.direction).coverage.highEnd
  rw [view.peerCoverage]
  exact initial.geometry.peerComplete

theorem Facts.peer_complete {view : View initial current} (facts : Facts view) :
    (view.gateway.session.peer sender.direction).acknowledged = (view.gateway.session.peer sender.direction).highEnd :=
  facts.peerAck.trans (CampusTCPTwoProgressGatewayComplete.peer_complete view)

theorem of_core {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
    {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
    (core : Core initial native quantum allowance current monitor sent .allReleased)
    (mainAck : (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (lower ++ upper).length) : Facts core.live.gatewayState := by
  have lowerPresent := core.covered .lower trivial
  have upperPresent := core.covered .upper trivial
  exact ⟨lowerPresent, upperPresent, mainAck, core.peerSettled (.inl lowerPresent), core.peerWindow⟩

end Netlib.Check.CampusTCPTwoProgressGatewayComplete
