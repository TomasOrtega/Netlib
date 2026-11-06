import Netlib.Check.CampusTCPTwoProgressEvidenceHop
import Netlib.Check.CampusTCPTwoProgressPhaseRetryState

/-!
# Actual timeout hops from the selected timer demand

The current demand supplies both timer bounds.
The waiting debt supplies the actual loss cause.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)
open CampusTCPTwoProgressSetup (config)

namespace TimerM
export CampusTCPTwoProgressMonitor (Monitor nextDemand timerDemand Demand)
end TimerM

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : TimerM.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem selected_timer (active : Active core) (waiting : monitor.waiting = true)
    (selected : TimerM.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.timeout sender))) :
    TimerM.timerDemand (config initial native quantum allowance) current.report.final = some (.timeout sender) := by
  have mode := active.waiting_mode waiting
  have ack := (active.waiting waiting).1
  simp only [TimerM.nextDemand, mode, ack, waiting, ite_true] at selected
  cases found : TimerM.timerDemand (config initial native quantum allowance) current.report.final with
  | none => rw [found] at selected; cases selected
  | some demand =>
    have same : CampusTCPTwoProgressMonitor.Demand.single demand = .single (.timeout sender) := by
      simpa only [found, Option.map_some, Option.some.injEq] using selected
    have demandEq := CampusTCPTwoProgressMonitor.Demand.single.inj same
    rw [demandEq]

theorem timeout_hop (active : Active core) (waiting : monitor.waiting = true) (budget : allowance ≤ 2)
    (selected : TimerM.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.timeout sender))) :
    Nonempty (Hop initial native quantum allowance current monitor (.timeout sender true)) := by
  obtain ⟨recovery, head, rest, deadline, runtime, ledger, timer, deadlineDue, elapsed, _⟩ :=
    CampusTCPTwoProgressTimer.timerDemand_timeout (selected_timer active waiting selected)
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  have target := CampusTCPTwoProgressTimer.target_of_fields ledger timer
  have due := Nat.max_le.mpr (And.intro deadlineDue elapsed)
  cases sent with
  | written | lower => cases active.preparing
  | retired first second => exact False.elim (active.nonempty rfl)
  | both first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.lower_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩⟩
  | tail first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.upper_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩⟩

end Netlib.Check.CampusTCPTwoProgressEvidence
