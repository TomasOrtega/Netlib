import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Check.CampusTCPTwoProgressMonitor
import Netlib.Check.CampusTCPTwoProgressHistory
import Netlib.Check.CampusTCPGapProgressPhaseBase
import Netlib.Protocol.TCP.RTOBound

/-!
# Initial obligations after the actual two-record write

The first demand sends the lower record.
The finite RTT cap uses the initial estimator and a bounded sample age.
-/

namespace Netlib.Check.CampusTCPTwoProgressSetup

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Demand nextDemand)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway}
variable {lower upper : List UInt8}

def config (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) : M.Config where
  sender := sender
  bytes := lower ++ upper
  clientIngress := native.ingress .client
  serverIngress := native.ingress .server
  quantum := quantum
  initialRTO := initial.senderState.idle.recovery.rto
  initialRemaining := 0
  lossAllowance := allowance
  lowerCount := lower.length
  upperCount := upper.length

theorem initial_guards (initial : TwoWriteInitial cut sender gateway lower upper) : Guards cut.endpoints := by
  intro actor
  cases sender <;> cases actor
  all_goals first
    | exact ⟨initial.senderState.idle.coherent, initial.senderState.idle.prepared,
        congrArg Option.isSome initial.senderState.idle.runtime⟩
    | exact ⟨initial.receiverState.idle.coherent, initial.receiverState.idle.prepared,
        congrArg Option.isSome initial.receiverState.idle.runtime⟩

theorem initial_anchor (initial : TwoWriteInitial cut sender gateway lower upper) :
    CampusTCPGapProgressPhaseBase.Anchor cut cut :=
  CampusTCPGapProgressPhaseBase.Anchor.refl cut (initial_guards initial)

def initial_history (_initial : TwoWriteInitial cut sender gateway lower upper) :
    CampusTCPTwoProgressHistory.History cut cut sender.other (lower ++ upper) [] :=
  CampusTCPTwoProgressHistory.History.ofCut cut sender.other (lower ++ upper)

theorem initial_demand (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) :
    M.nextDemand (config initial native quantum allowance) cut.report.final CampusTCPTwoProgressMonitor.Monitor.initial =
      some (.single (.operation (.send sender lower.length true))) := by
  rfl

def sampleAge (bound quantum : Nat) : Nat := 16 * bound * quantum

def sampleCap (initial : TwoWriteInitial cut sender gateway lower upper) (bound quantum : Nat) : Nat :=
  max initial.senderState.idle.recovery.rto
    (RTO.sampleCap initial.senderState.idle.recovery.estimator (sampleAge bound quantum))

theorem initial_rto_le_sampleCap (initial : TwoWriteInitial cut sender gateway lower upper) (bound quantum : Nat) :
    initial.senderState.idle.recovery.rto ≤ sampleCap initial bound quantum :=
  Nat.le_max_left _ _

theorem sampleCap_floor (initial : TwoWriteInitial cut sender gateway lower upper) (bound quantum : Nat) :
    1000 ≤ sampleCap initial bound quantum :=
  Nat.le_trans (RTO.sampleCap_floor _ _) (Nat.le_max_right _ _)

theorem observed_interval_le_sampleCap (initial : TwoWriteInitial cut sender gateway lower upper)
    (bound quantum sample : Nat) (age : sample ≤ sampleAge bound quantum) :
    RTO.interval (RTO.observe initial.senderState.idle.recovery.estimator sample) ≤ sampleCap initial bound quantum :=
  Nat.le_trans (RTO.interval_observe_le_sampleCap _ _ _ age) (Nat.le_max_right _ _)

theorem sampleCap_mono (initial : TwoWriteInitial cut sender gateway lower upper)
    (first last quantum : Nat) (bounds : first ≤ last) :
    sampleCap initial first quantum ≤ sampleCap initial last quantum := by
  have ages := Nat.mul_le_mul_right quantum (Nat.mul_le_mul_left 16 bounds)
  have caps := RTO.sampleCap_mono initial.senderState.idle.recovery.estimator
    (sampleAge first quantum) (sampleAge last quantum) ages
  unfold sampleCap
  omega

end Netlib.Check.CampusTCPTwoProgressSetup
