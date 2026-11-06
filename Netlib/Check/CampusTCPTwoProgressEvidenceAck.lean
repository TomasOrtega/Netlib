import Netlib.Check.CampusTCPTwoProgressEvidenceHop
import Netlib.Check.CampusTCPTwoProgressPhaseAckState
import Netlib.Check.CampusTCPTwoProgressPhaseAckRetire
import Netlib.Check.CampusTCPTwoProgressPhaseNetworkStateMore

/-!
# Actual service for the current serialized ACK

The current ACK path determines the event and its packet.
Each operation returns the same actual step in the outer evidence.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed nextDemand)
end M
namespace G
export CampusTCPGapProgressMonitor (nextAction)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff servesOption_iff phase_beq_false)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received} {lane : M.Lane}

theorem ack_action_allowed (active : Active core) (pending : monitor.ack = some lane)
    (action : CampusTCPRoundMonitor.Action)
    (selected : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor action.event := by
  have served := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
    current.report.final monitor lane action selected
  obtain ⟨demand, next, serves⟩ := (F.servesOption_iff _ _).mp served
  have beforeLower := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.lowerLane
  have beforeUpper := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.upperLane
  have current : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single demand) := by
    rcases active.mode with mode | mode <;>
      simp only [M.nextDemand, mode, (F.phase_beq_false _ _).mpr beforeLower,
        (F.phase_beq_false _ _).mpr beforeUpper, Bool.false_eq_true, ite_false, pending, next, Option.map_some]
  apply (F.allowed_iff _ _ _ _).mpr
  refine ⟨?_, .inl ⟨_, current, serves⟩, ?_⟩
  · rcases active.mode with mode | mode <;> rw [mode] <;> decide
  · cases action <;> rfl

theorem ack_hop (active : Active core) (pending : monitor.ack = some lane)
    (action : CampusTCPRoundMonitor.Action)
    (selected : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action) :
    Nonempty (Hop initial native quantum allowance current monitor action.event) := by
  have work : AckWork core lane := by simpa only [AckState, pending] using active.ack
  cases work with
  | pending phase queue =>
    have next : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap =
        some (.emitAck sender.other true) := by
      simp only [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase]
      rfl
    have same := Option.some.inj (selected.symm.trans next)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseAckState.send_at active pending phase
    exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event, .active value.value.next value.next⟩⟩
  | ingress path =>
    have next : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap =
        some (.assign path.output.index (native.ingress sender.other)) := by cases sender <;> exact path.action _
    have same := Option.some.inj (selected.symm.trans next)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseNetwork.assign_ack_at core path (ack_action_allowed active pending _ next)
    exact ⟨⟨actual, value.value.value.move, value.value.event,
      .active value.advance.nextCore (CampusTCPTwoProgressPhaseNetworkState.ack_assigned active path pending value)⟩⟩
  | ticket path =>
    have next := path.action (config initial native quantum allowance)
    have same := Option.some.inj (selected.symm.trans next)
    subst action
    obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseNetwork.serve_ack_at core path (ack_action_allowed active pending _ next)
    exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event,
      .active value.advance.nextCore (CampusTCPTwoProgressPhaseNetworkState.ack_served active path pending value)⟩⟩
  | link path =>
    have next := path.action (config initial native quantum allowance)
    have same := Option.some.inj (selected.symm.trans next)
    subst action
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseAckRetire.receive_at active path pending (ack_action_allowed active pending _ next)
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩⟩

end Netlib.Check.CampusTCPTwoProgressEvidence
