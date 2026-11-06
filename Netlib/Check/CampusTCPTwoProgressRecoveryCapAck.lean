import Netlib.Check.CampusTCPTwoProgressRecoveryCap
import Netlib.Check.CampusTCPTwoProgressRecoveryKarn
import Netlib.Check.CampusTCPTwoProgressEvidenceAck

/-!
# Fixed pending-head cap through the actual ACK path

The cap stays fixed while the current ACK advances through its stored path.
An advancing ACK uses the current retry correlation only while a head remains.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCapAck

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressRecoveryCap (PendingCap at_core of_core)
open CampusTCPTwoProgressEvidence (Hop Evidence)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (normalize_counters ordinary_counters counters)
end F
namespace N
export CampusTCPTwoProgressPhaseNetwork (AckAssigned AckServed)
end N
namespace A
export CampusTCPTwoProgressPhaseAckReceive (Advanced Zero)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance C : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {lane : M.Lane} {actual : Step input}

private theorem network_cap (core : Core initial native quantum allowance current monitor sent received)
    (move : Move current actual)
    (next : Core initial native quantum allowance move.after (M.observe (config initial native quantum allowance) monitor actual) sent received)
    (endpoints : move.after.endpoints = current.endpoints)
    (ordinary : M.observe (config initial native quantum allowance) monitor actual =
      CampusTCPTwoProgressMonitor.observeOrdinary (config initial native quantum allowance) monitor actual)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) := by
  have recovery : next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact next.live.senderFlight.runtime.symm.trans (by rw [endpoints]; exact core.live.senderFlight.runtime)
  have retries : (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries := by
    rw [ordinary]
    exact congrArg Prod.fst (F.ordinary_counters _ _ _)
  apply of_core next
  intro pending
  rw [recovery, retries]
  exact at_core core cap pending

theorem assigned_cap {count : Nat} {path : CampusTCPTwoProgressPaths.AckIngress initial current count lane}
    (value : N.AckAssigned core path actual)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C value.value.value.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) :=
  network_cap core value.value.value.move value.advance.nextCore value.value.value.endpoints value.advance.ordinary cap

theorem served_cap {path : CampusTCPTwoProgressPaths.AckTicket initial native current (received.bytes lower upper).length lane}
    (value : N.AckServed core path actual)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C value.value.value.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) :=
  network_cap core value.value.value.move value.advance.nextCore value.value.value.endpoints value.advance.ordinary cap

theorem send_cap (value : CampusTCPTwoProgressPhaseAckSend.AckSent core lane actual)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C value.value.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) := by
  have recovery : value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact value.next.live.senderFlight.runtime.symm.trans
      ((congrArg Endpoint.State.recovery value.value.peer).trans core.live.senderFlight.runtime)
  apply of_core value.next
  intro pending
  rw [recovery, value.observed]
  exact at_core core cap pending

private theorem advanced_retries {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : A.Advanced core path) :
    (M.observe (config initial native quantum allowance) monitor value.value.delivery.step).retries = monitor.retries := by
  rw [value.observed]
  exact congrArg Prod.fst (F.normalize_counters _ _ _)

private theorem zero_retries {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : A.Zero core path) :
    (M.observe (config initial native quantum allowance) monitor value.value.delivery.step).retries = monitor.retries := by
  rw [value.observed]
  exact congrArg Prod.fst (F.normalize_counters _ _ _)

theorem advanced_cap {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (active : Active core) (value : A.Advanced core path) (nonoriginal : monitor.mode ≠ .originals)
    (selected : monitor.ack = some lane)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C value.value.delivery.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor value.value.delivery.step) := by
  apply of_core value.nextCore
  intro pending
  rw [CampusTCPTwoProgressRecoveryKarn.pending_rto active value nonoriginal selected pending, advanced_retries value]
  exact at_core core cap active.nonempty

theorem zero_cap {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}
    (value : A.Zero core path)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor) :
    PendingCap (config initial native quantum allowance) C value.value.delivery.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor value.value.delivery.step) := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  have recovery : value.nextCore.live.senderFlight.recovery = Endpoint.zeroAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
    apply Option.some.inj
    exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)
  apply of_core value.nextCore
  intro pending
  rw [recovery, zero_retries value]
  unfold Endpoint.zeroAckRecovery
  split <;> exact at_core core cap pending

theorem ack_hop_cap (active : Active core) (nonoriginal : monitor.mode ≠ .originals)
    (cap : PendingCap (config initial native quantum allowance) C current.report.final monitor)
    (selected : monitor.ack = some lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction (config initial native quantum allowance).toConfig
      current.report.final lane.toGap = some action) :
    ∃ hop : Hop initial native quantum allowance current monitor action.event,
      PendingCap (config initial native quantum allowance) C hop.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor hop.actual) := by
  have work : AckWork core lane := by simpa only [AckState, selected] using active.ack
  cases work with
  | pending phase queue =>
    have command : CampusTCPGapProgressMonitor.nextAction (config initial native quantum allowance).toConfig
        current.report.final lane.toGap = some (.emitAck sender.other true) := by
      simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase]
      rfl
    have same := Option.some.inj (next.symm.trans command)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseAckState.send_at active selected phase
    exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event, .active value.value.next value.next⟩,
      send_cap value.value cap⟩
  | ingress path =>
    have command : CampusTCPGapProgressMonitor.nextAction (config initial native quantum allowance).toConfig
        current.report.final lane.toGap = some (.assign path.output.index (native.ingress sender.other)) := by
      cases sender <;> exact path.action _
    have same := Option.some.inj (next.symm.trans command)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseNetwork.assign_ack_at core path
      (CampusTCPTwoProgressEvidence.ack_action_allowed active selected _ command)
    exact ⟨⟨actual, value.value.value.move, value.value.event,
      .active value.advance.nextCore (CampusTCPTwoProgressPhaseNetworkState.ack_assigned active path selected value)⟩,
      assigned_cap value cap⟩
  | ticket path =>
    have command := path.action (config initial native quantum allowance)
    have same := Option.some.inj (next.symm.trans command)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseNetwork.serve_ack_at core path
      (CampusTCPTwoProgressEvidence.ack_action_allowed active selected _ command)
    exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event,
      .active value.advance.nextCore (CampusTCPTwoProgressPhaseNetworkState.ack_served active path selected value)⟩,
      served_cap value cap⟩
  | link path =>
    have command := path.action (config initial native quantum allowance)
    have same := Option.some.inj (next.symm.trans command)
    subst action
    obtain ⟨record⟩ := CampusTCPTwoProgressPhaseAckRetire.receive_at active path selected
      (CampusTCPTwoProgressEvidence.ack_action_allowed active selected _ command)
    refine ⟨⟨record.actual, record.move, record.event, record.evidence⟩, ?_⟩
    cases record with
    | zero value => exact zero_cap value.value cap
    | advanced value => exact advanced_cap active value.value nonoriginal selected cap

end Netlib.Check.CampusTCPTwoProgressRecoveryCapAck
