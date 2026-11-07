import Netlib.Check.CampusTCPTwoTransferOriginalRank
import Netlib.Check.CampusTCPTwoTransferEvidenceDrain

/-!
# Rank changes on actual transfer controls and clocks

Controls spend reserved work. Primary drain also advances its original lane.
An actual allowed clock keeps both parts of the rank fixed.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)

namespace T
export CampusTCPTwoTransferMonitor (Monitor Control Mode controlDemand drainTicket observe)
end T

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : T.Monitor} {actual : Step input} {kind : T.Control} {actor : Actor} {millis : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private def beforeMode : T.Control → T.Mode
  | .pause => .armed
  | .capture => .capture
  | .install => .install
  | .clientRoute => .clientRoute
  | .serverRoute => .serverRoute
  | .fence => .fence
  | .resume => .resume

private theorem selected_mode (selected : T.controlDemand monitor = some kind) : monitor.mode = beforeMode kind := by
  cases kind <;> cases mode : monitor.mode <;> simp_all [T.controlDemand, beforeMode]
  all_goals split at selected <;> simp_all

theorem control_strict
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : T.controlDemand monitor = some kind) (drainless : T.drainTicket current.report.final monitor = none) :
    rank value.move.after.report.final (T.observe cfg monitor actual) < rank current.report.final monitor := by
  have scope := evidence.control_scope selected
  have before := selected_mode selected
  have queue := evidence.control_primary_le_one selected
  have work : value.move.after.report.final.outstanding .primary = current.report.final.outstanding .primary := by
    simp only [State.outstanding, value.frame.work]
  rw [current_rank evidence scope.mode, CampusTCPTwoTransferControlObserve.control_observe value selected drainless]
  cases kind <;>
    simp [rank, reserve, B.potential, B.remainingControls, CampusTCPTwoTransferControlObserve.afterControl,
      CampusTCPTwoTransferMonitor.Control.after, beforeMode, before, scope.exchange, scope.mode, work]
  all_goals omega

theorem clock_same
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (clocked : CampusTCPTwoTransferLocatedClock.Clocked evidence.core actor millis actual) :
    rank clocked.move.after.report.final (T.observe cfg monitor actual) = rank current.report.final monitor := by
  rw [clocked.observed]
  simp only [rank]
  split
  · congr 1
    cases mode : monitor.mode <;>
      simp [reserve, B.potential, B.remainingControls, mode, State.outstanding, clocked.placement.frame.work]
  · rfl

theorem drain_strict
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary)
    (drained : CampusTCPTwoTransferDrainProgress.Advanced evidence.core ticket actual)
    (selected : T.drainTicket current.report.final monitor = some ticket) :
    rank drained.value.value.value.move.after.report.final (T.observe cfg monitor actual) < rank current.report.final monitor := by
  have scope := evidence.drain_scope selected
  have mode := CampusTCPTwoTransferDrainObserve.drain_mode selected
  rcases drained with ⟨part, path, ticketEq, located, value, active, phase⟩
  have primary := (congrArg (fun item => item.value.gateway) value.value.value.facts.ticket).trans
    (path.ticket_gateway.trans located)
  have counted := CampusTCPPrimaryDrain.serve_primary_count actual path.ticket.id
    value.value.value.facts.event _ value.value.value.facts.recorded primary
  rw [value.value.value.move.beforeEq, ← value.value.value.move.final] at counted
  rw [current_rank evidence scope.mode, value.observed]
  cases part with
  | lower =>
    have pathPhase : monitor.exchange.forward.lower.phase = .dataTicket := path.phase
    simp [rank, reserve, B.potential, B.remainingControls, CampusTCPTwoTransferDrainObserve.afterDrain,
      CampusTCPTwoTransferLocatedDrain.forwardAfter, CampusTCPTwoTransferDrainObserve.linkLane,
      mode, scope.exchange, scope.mode, O.originalRank, pathPhase, O.dataCost]
    omega
  | upper =>
    have pathPhase : monitor.exchange.forward.upper.phase = .dataTicket := path.phase
    simp [rank, reserve, B.potential, B.remainingControls, CampusTCPTwoTransferDrainObserve.afterDrain,
      CampusTCPTwoTransferLocatedDrain.forwardAfter, CampusTCPTwoTransferDrainObserve.linkLane,
      mode, scope.exchange, scope.mode, O.originalRank, pathPhase, O.dataCost]
    omega

end Netlib.Check.CampusTCPTwoTransferOriginalRank
