import Netlib.Check.CampusTCPTwoProgressEvidenceRecoveryRank
import Netlib.Check.CampusTCPTwoProgressEvidenceChoice
import Netlib.Check.CampusTCPTwoProgressPhaseClock
import Netlib.Check.CampusTCPTwoProgressPhaseRetryState

namespace Netlib.Check.CampusTCPTwoProgressRecoveryRankTimer

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane nextDemand laneDemand timerDemand Allowed observe)
end M
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G
namespace K
export CampusTCPTwoProgressRecoveryRank (rank timerSlots)
end K

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {actor : Actor} {millis : Nat} {actual : Step input}

private theorem lane_not_tick (lane : M.Lane)
    (selected : M.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some (.tick actor millis)) : False := by
  obtain ⟨_, _, ordinary | ⟨_, resolution⟩⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  · cases ordinary
  · cases resolution

private theorem selected_tick (active : Active core)
    (next : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single (.tick actor millis))) :
    monitor.mode = .recovery ∧ monitor.waiting = true ∧ monitor.ack = none ∧
      M.timerDemand (config initial native quantum allowance) current.report.final = some (.tick actor millis) := by
  have first := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.lowerLane
  have second := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.upperLane
  rcases active.mode with mode | mode
  · simp only [M.nextDemand, mode,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr second, Bool.false_eq_true, ite_false] at next
    cases pending : monitor.ack with
    | none =>
      simp only [pending] at next
      split at next <;> cases next
    | some lane =>
      simp only [pending] at next
      cases chosen : M.laneDemand (config initial native quantum allowance) current.report.final monitor lane with
      | none => simp only [chosen, Option.map_none] at next; cases next
      | some demand =>
        have same : demand = .tick actor millis := by simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
        subst demand
        exact False.elim (lane_not_tick lane chosen)
  · simp only [M.nextDemand, mode] at next
    cases pending : monitor.ack with
    | some lane =>
      simp only [pending] at next
      cases chosen : M.laneDemand (config initial native quantum allowance) current.report.final monitor lane with
      | none => simp only [chosen, Option.map_none] at next; cases next
      | some demand =>
        have same : demand = .tick actor millis := by simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
        subst demand
        exact False.elim (lane_not_tick lane chosen)
    | none =>
      simp only [pending] at next
      cases waiting : monitor.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at next
        cases chosen : M.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.retry with
        | none => simp only [chosen, Option.map_none] at next; cases next
        | some demand =>
          have same : demand = .tick actor millis := by simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
          subst demand
          exact False.elim (lane_not_tick monitor.retry chosen)
      | true =>
        simp only [waiting, ite_true] at next
        cases chosen : M.timerDemand (config initial native quantum allowance) current.report.final with
        | none => simp only [chosen, Option.map_none] at next; cases next
        | some demand =>
          have same : demand = .tick actor millis := by simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
          subst demand
          exact ⟨mode, rfl, rfl, rfl⟩

theorem selected_tick_strict (active : Active core) (bound : Nat) (positive : 0 < quantum)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance) monitor actor millis actual)
    (_allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.advanceClock actor millis))
    (next : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single (.tick actor millis))) :
    K.rank (config initial native quantum allowance) bound allowance clocked.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) <
      K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  obtain ⟨mode, waiting, _, pending⟩ := selected_tick active next
  obtain ⟨recovery, _, _, _, target, runtime, timer, _, _, _, early, selectedActor, tick⟩ := CampusTCPTwoProgressTimer.timerDemand_tick pending
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  have actorEq : actor = sender := selectedActor
  subst actor
  have updated := clocked.base.sender_recovery rfl core.live.senderFlight.runtime
  have decrease : K.timerSlots (config initial native quantum allowance) clocked.move.after.report.final <
      K.timerSlots (config initial native quantum allowance) current.report.final := by
    change K.timerSlots (config initial native quantum allowance) clocked.base.move.after.report.final < _
    rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ updated,
      CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ runtime, tick]
    exact CampusTCPTwoProgressTimer.tick_slots_lt timer positive early
  rw [clocked.observed]
  exact CampusTCPTwoProgressRecoveryRank.waiting_step _ _ _ _ _ _ _ mode mode waiting waiting rfl decrease

private theorem timeout_demand (active : Active core)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.timeout sender true)) :
    monitor.mode = .recovery ∧ monitor.waiting = true ∧ monitor.ack = none ∧
      M.timerDemand (config initial native quantum allowance) current.report.final = some (.timeout sender) := by
  have choice := CampusTCPTwoProgressEvidence.allowed_choice active allowed
    (by intro actor millis impossible; cases impossible) (by intro id impossible; cases impossible)
  cases choice with
  | lower action _ _ _ same => cases action <;> cases same
  | upper action _ _ _ _ same => cases action <;> cases same
  | ack _ action _ _ same => cases action <;> cases same
  | retry action _ _ _ _ same => cases action <;> cases same
  | timeout mode ack waiting next _ =>
    simp only [M.nextDemand, mode, ack, waiting, ite_true] at next
    cases chosen : M.timerDemand (config initial native quantum allowance) current.report.final with
    | none => simp only [chosen, Option.map_none] at next; cases next
    | some demand =>
      have same : demand = .timeout sender := by simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
      subst demand
      exact ⟨mode, waiting, ack, rfl⟩

theorem timeout_exact (active : Active core) (bound : Nat) {part : CampusTCPTwoProgressSender.Part}
    {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) :
    K.rank (config initial native quantum allowance) bound allowance value.value.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor actual) + 1 =
      K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  have allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor (.timeout sender true) := by
    rw [← value.value.facts.event]
    exact value.allowed
  obtain ⟨mode, waiting, ackNone, pending⟩ := timeout_demand active allowed
  obtain ⟨recovery, entry, tail, deadline, runtime, ledger, timer, due, elapsed, _⟩ := CampusTCPTwoProgressTimer.timerDemand_timeout pending
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  have zero : K.timerSlots (config initial native quantum allowance) current.report.final = 0 := by
    rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ runtime]
    have target := CampusTCPTwoProgressTimer.target_of_fields ledger timer
    have remaining : CampusTCPTwoProgressTimer.remaining core.live.senderFlight.recovery = 0 := by
      rw [CampusTCPTwoProgressTimer.remaining_of_target target]
      omega
    rw [CampusTCPTwoProgressTimer.slots, remaining]
    by_cases positive : 0 < quantum
    · exact CampusTCPRecoveryRoundMonitor.waitSlots_zero positive
    · have zero : quantum = 0 := by omega
      change CampusTCPRecoveryRoundMonitor.waitSlots quantum 0 = 0
      rw [zero]
      rfl
  have credit := CampusTCPTwoProgressEvidenceRecoveryRank.active_waiting_credit active waiting
  apply CampusTCPTwoProgressRecoveryRank.timeout_step _ _ _ _ _ _ _ mode
  · rw [value.observed]; exact mode
  · exact waiting
  · rw [value.observed]
  · rw [value.observed]
  · exact credit
  · exact zero
  · rw [value.observed]
    simp only [CampusTCPTwoProgressRecoveryRank.work, ackNone, CampusTCPTwoProgressPhaseRetry.ingressLane,
      CampusTCPTwoProgressOriginalRank.dataCost]

theorem timeout_hop_strict (active : Active core) (bound : Nat) (budget : allowance ≤ 2)
    (waiting : monitor.waiting = true)
    (selected : M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single (.timeout sender))) :
    ∃ hop : CampusTCPTwoProgressEvidence.Hop initial native quantum allowance current monitor (.timeout sender true),
      K.rank (config initial native quantum allowance) bound allowance hop.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor hop.actual) + 1 =
        K.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  have mode := active.waiting_mode waiting
  have ack := (active.waiting waiting).1
  have demand : M.timerDemand (config initial native quantum allowance) current.report.final = some (.timeout sender) := by
    simp only [M.nextDemand, mode, ack, waiting, ite_true] at selected
    cases found : M.timerDemand (config initial native quantum allowance) current.report.final with
    | none => rw [found] at selected; cases selected
    | some demand =>
      have same : CampusTCPTwoProgressMonitor.Demand.single demand = .single (.timeout sender) := by
        simpa only [found, Option.map_some, Option.some.injEq] using selected
      rw [CampusTCPTwoProgressMonitor.Demand.single.inj same]
  obtain ⟨recovery, head, rest, deadline, runtime, ledger, timer, deadlineDue, elapsed, _⟩ :=
    CampusTCPTwoProgressTimer.timerDemand_timeout demand
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  have target := CampusTCPTwoProgressTimer.target_of_fields ledger timer
  have due := Nat.max_le.mpr (And.intro deadlineDue elapsed)
  cases sent with
  | written | lower => cases active.preparing
  | retired => exact False.elim (active.nonempty rfl)
  | both first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.lower_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩, timeout_exact active bound value.value⟩
  | tail first second head =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseRetryState.upper_at active waiting budget target due
    exact ⟨⟨value.actual, value.move, value.event, value.evidence⟩, timeout_exact active bound value.value⟩

end Netlib.Check.CampusTCPTwoProgressRecoveryRankTimer
