import Netlib.Check.CampusTCPTwoProgressRecoveryBounds

/-!
# Timer bounds from the retained current invariant

The deadline bound is proved by each actual transition.
The only fresh sample that leaves a head uses the initial estimator.
-/

namespace Netlib.Check.CampusTCPTwoProgressTimerInvariant

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}

theorem target_le (core : Core initial native quantum allowance current monitor sent received) (target : Nat)
    (selected : CampusTCPTwoProgressMonitor.timerTarget core.live.senderFlight.recovery = some target) :
    target ≤ core.live.senderFlight.recovery.now + core.live.senderFlight.recovery.rto :=
  CampusTCPTwoProgressRecoveryBounds.target_le _ core.live.senderFlight.clocked core.deadline target selected

theorem remaining_le (core : Core initial native quantum allowance current monitor sent received) :
    CampusTCPTwoProgressTimer.remaining core.live.senderFlight.recovery ≤ core.live.senderFlight.recovery.rto :=
  CampusTCPTwoProgressRecoveryBounds.remaining_le _ core.live.senderFlight.clocked core.deadline

theorem slots_le (core : Core initial native quantum allowance current monitor sent received) :
    CampusTCPTwoProgressTimer.slots quantum core.live.senderFlight.recovery ≤
      CampusTCPTwoProgressTimer.waitSlots quantum core.live.senderFlight.recovery.rto :=
  CampusTCPTwoProgressRecoveryBounds.slots_le _ _ core.live.senderFlight.clocked core.deadline

theorem partial_initial_cap
    {first : CampusTCPTwoProgressSender.Original initial .lower} {second : CampusTCPTwoProgressSender.Original initial .upper}
    {head : Recovery.Outstanding} {lane : CampusTCPTwoProgressMonitor.Lane}
    {core : Core initial native quantum allowance current monitor (.both first second head) .lowerReleased}
    {path : CampusTCPTwoProgressPaths.AckLink initial current lower.length lane}
    (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) (fresh : head.retried = false)
    (age : Nat) (elapsed : core.live.senderFlight.recovery.now - head.sentAt ≤ age) :
    value.nextCore.live.senderFlight.recovery.rto ≤ RTO.sampleCap initial.senderState.idle.recovery.estimator age := by
  have bound := CampusTCPTwoProgressRecoveryBounds.partial_fresh_cap value fresh age elapsed
  rw [core.estimatorBeforeRetire rfl] at bound
  exact bound

end Netlib.Check.CampusTCPTwoProgressTimerInvariant
