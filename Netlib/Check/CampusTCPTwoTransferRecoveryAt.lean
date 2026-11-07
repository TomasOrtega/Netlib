import Netlib.Check.CampusTCPTwoTransferHandoffRTO
import Netlib.Check.CampusTCPTwoTransferNonoriginal

/-!
# Current recovery evidence on the original whole trace

The fixed cap starts at the actual original exit.
The current point retains the original report, loss book, and clock bound.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidenceHandoffTrace (At Finished)
open CampusTCPTwoTransferOriginalBounded (Exited)
open CampusTCPTwoTransferHandoffRTO (PendingCap cap)

namespace W
export CampusTCPTwoTransferMonitor (Monitor monitorAt controlDemand drainTicket)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {steps : List (Step input)} {slot horizon : Nat}

structure RecoveryAt (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (capacity : Nat)
    (steps : List (Step input)) (slot : Nat) where
  point : At initial checks routing quantum allowance reverseLower reverseUpper steps slot
  nonoriginal : (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot).exchange.forward.mode ≠ .originals
  pendingCap : PendingCap (config initial checks routing quantum allowance reverseLower reverseUpper) capacity
    point.current.report.final (W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps slot)

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def RecoveryAt.ofExited (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (within : slot ≤ horizon) :
    RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper (cap initial (horizon * quantum)) steps slot :=
  ⟨value.point, value.nonoriginal, CampusTCPTwoTransferHandoffRTO.Exited.pending_cap value within⟩

def RecoveryAt.finished (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    Finished initial checks routing quantum allowance reverseLower reverseUpper steps slot :=
  ⟨value.point, value.point.evidence.nonoriginal_finished value.nonoriginal⟩

theorem RecoveryAt.standby_location (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    value.point.location = .standby := value.finished.standby_location

theorem RecoveryAt.standby_routing (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    Routing value.point.current .standby := value.finished.standby_routing

theorem RecoveryAt.retry_bound (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    (W.monitorAt cfg .initial steps slot).exchange.forward.retries ≤ allowance :=
  Nat.le_trans value.point.evidence.core.losses.count value.point.evidence.core.lossBound

theorem RecoveryAt.ordinary (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    W.controlDemand (W.monitorAt cfg .initial steps slot) = none ∧
      W.drainTicket value.point.current.report.final (W.monitorAt cfg .initial steps slot) = none :=
  CampusTCPTwoTransferNonoriginal.ordinary value.point.evidence value.nonoriginal

theorem RecoveryAt.local_mode (value : RecoveryAt initial checks routing quantum allowance reverseLower reverseUpper capacity steps slot) :
    (W.monitorAt cfg .initial steps slot).exchange.forward.mode = .recovery ∨
      (W.monitorAt cfg .initial steps slot).exchange.forward.mode = .needRead := by
  have evidence := value.point.evidence
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (value.nonoriginal state.mode)
  | pending state => exact False.elim (value.nonoriginal state.mode)
  | active state => exact .inl (state.mode.resolve_left value.nonoriginal)
  | readable _ _ mode _ _ _ => exact .inr mode

end Netlib.Check.CampusTCPTwoTransferRecoveryTrace
