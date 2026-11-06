import Netlib.Check.CampusTCPTwoProgressEvidenceBasic
import Netlib.Check.CampusTCPTwoProgressOriginalRank

/-!
# Current work bounds for the original paths

Typed current paths supply the rank shape.
An active ACK leaves at most one original data path live.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)

namespace OriginalM
export CampusTCPTwoProgressMonitor (Monitor Config nextDemand laneDemand)
end OriginalM

namespace ORank
export CampusTCPTwoProgressOriginalRank
  (RankShape DataPhase RetryPhase AckPhase dataCost ackCost ackWork originalRank dataCost_zero ackCost_positive)
end ORank

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem original_phase {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
    (path : OriginalLane initial native current core.live.gatewayState received part lane) : ORank.DataPhase lane.phase := by
  cases path with
  | active work missing =>
    cases work with
    | ingress path _ => exact .inr (.inl path.phase)
    | ticket path _ => exact .inr (.inr (.inl path.phase))
    | link path _ _ => exact .inr (.inr (.inr (.inl path.phase)))
  | done phase => exact .inr (.inr (.inr (.inr phase)))

private theorem original_cost {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
    (path : OriginalLane initial native current core.live.gatewayState received part lane) : ORank.dataCost lane.phase ≤ 7 := by
  cases path with
  | active work missing =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide
  | done phase => rw [phase]; decide

private theorem ack_phase (active : Active core) (lane : CampusTCPTwoProgressMonitor.Lane)
    (selected : monitor.ack = some lane) : ORank.AckPhase lane.phase := by
  have work : AckWork core lane := by simpa only [AckState, selected] using active.ack
  cases work with
  | pending phase queue => exact .inl phase
  | ingress path => exact .inr (.inl path.phase)
  | ticket path => exact .inr (.inr (.inl path.phase))
  | link path => exact .inr (.inr (.inr path.phase))

private theorem ack_one_done (active : Active core) (lane : CampusTCPTwoProgressMonitor.Lane)
    (selected : monitor.ack = some lane) : monitor.lower.phase = .done ∨ monitor.upper.phase = .done := by
  have nonempty := active.ackNonempty (by rw [selected]; rfl)
  cases received with
  | empty => exact False.elim (nonempty rfl)
  | upperHeld =>
    right
    cases active.upperLane with
    | active work missing => exact False.elim (missing trivial)
    | done phase => exact phase
  | lowerReleased | allReleased =>
    left
    cases active.lowerLane with
    | active work missing => exact False.elim (missing trivial)
    | done phase => exact phase

theorem Evidence.original_shape (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) : ORank.RankShape monitor := by
  cases value with
  | written before sources =>
    exact {
      lower := .inl before.lowerPending, upper := .inl before.upperPending
      retry := .inr (.inr (.inr before.retry))
      originalRetry := fun _ => before.retry
      ack := by intro lane selected; rw [before.ack] at selected; cases selected
      handoff := by intro different; exact False.elim (different mode) }
  | upper first before sources =>
    have lowerPhase : ORank.DataPhase monitor.lower.phase := by
      rcases before.lowerPath.phase with ingress | done
      · exact .inr (.inl ingress)
      · exact .inr (.inr (.inr (.inr done)))
    exact {
      lower := lowerPhase, upper := .inl before.upperPending
      retry := .inr (.inr (.inr before.retry))
      originalRetry := fun _ => before.retry
      ack := by intro lane selected; rw [before.ack] at selected; cases selected
      handoff := by intro different; exact False.elim (different mode) }
  | active core active =>
    have retry := (active.originals mode).1
    exact ⟨original_phase active.lowerLane, original_phase active.upperLane, .inr (.inr (.inr retry)),
      fun _ => retry, ack_phase active, by intro different; exact False.elim (different mode)⟩
  | ready core ready => rw [ready.mode] at mode; cases mode
  | done done => rw [done.mode] at mode; cases mode

private theorem active_bound (active : Active core) (mode : monitor.mode = .originals) : ORank.originalRank monitor ≤ 16 := by
  have first := original_cost active.lowerLane
  have second := original_cost active.upperLane
  rw [ORank.originalRank, mode]
  cases selected : monitor.ack with
  | none => simp only [ORank.ackWork]; omega
  | some lane =>
    have ackBound : ORank.ackCost lane.phase ≤ 4 := by
      rcases ack_phase active lane selected with phase | phase | phase | phase <;> rw [phase] <;> decide
    simp only [ORank.ackWork]
    rcases ack_one_done active lane selected with done | done
    · rw [done]
      change 0 + ORank.dataCost monitor.upper.phase + ORank.ackCost lane.phase ≤ 16
      omega
    · rw [done]
      change ORank.dataCost monitor.lower.phase + 0 + ORank.ackCost lane.phase ≤ 16
      omega

theorem Evidence.original_rank_le (value : Evidence initial native quantum allowance current monitor) : ORank.originalRank monitor ≤ 16 := by
  by_cases mode : monitor.mode = .originals
  · cases value with
    | written before sources => rw [ORank.originalRank, mode, before.lowerPending, before.upperPending, before.ack]; decide
    | upper first before sources =>
      rw [ORank.originalRank, mode, before.upperPending, before.ack]
      rcases before.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
    | active core active => exact active_bound active mode
    | ready core ready => rw [ready.mode] at mode; cases mode
    | done done => rw [done.mode] at mode; cases mode
  · rw [CampusTCPTwoProgressOriginalRank.rank_zero_of_nonoriginal mode]
    decide

theorem Evidence.original_positive (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) : 0 < ORank.originalRank monitor := by
  by_cases positive : 0 < ORank.originalRank monitor
  · exact positive
  · have zero : ORank.originalRank monitor = 0 := by omega
    have closed := CampusTCPTwoProgressOriginalRank.zero_resolved (value.original_shape mode) value.healthy zero
    cases value with
    | written before sources => have impossible := before.lowerPending.symm.trans closed.1; cases impossible
    | upper first before sources => have impossible := before.upperPending.symm.trans closed.2.1; cases impossible
    | active core active => exact False.elim ((active.originalOpen mode (closed.2.2 mode)) ⟨closed.1, closed.2.1⟩)
    | ready core ready => rw [ready.mode] at mode; cases mode
    | done done => rw [done.mode] at mode; cases mode

private theorem lane_demand_exists (cfg : OriginalM.Config) (state : State input) (monitor : OriginalM.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (action : CampusTCPRoundMonitor.Action)
    (selected : CampusTCPGapProgressMonitor.nextAction cfg.toConfig state lane.toGap = some action) :
    ∃ demand, OriginalM.laneDemand cfg state monitor lane = some demand := by
  unfold OriginalM.laneDemand
  rw [selected]
  simp only [bind, Option.bind]
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap with
  | none => exact ⟨.operation action, rfl⟩
  | some id =>
    by_cases budget : monitor.drops.length < cfg.lossAllowance
    · exact ⟨.resolution action id, by simp only [budget, ite_true]; rfl⟩
    · exact ⟨.operation action, by simp only [budget, ite_false]; rfl⟩

private theorem data_demand {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
    (work : DataWork initial native current core.live.gatewayState part lane) :
    ∃ demand, OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some demand := by
  cases work with
  | ingress path source => exact lane_demand_exists _ _ _ _ _ (path.action _)
  | ticket path source => exact lane_demand_exists _ _ _ _ _ (path.action _)
  | link path source covered => exact lane_demand_exists _ _ _ _ _ (path.action _)

private theorem ack_demand (active : Active core) (lane : CampusTCPTwoProgressMonitor.Lane) (selected : monitor.ack = some lane) :
    ∃ demand, OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some demand := by
  have work : AckWork core lane := by simpa only [AckState, selected] using active.ack
  cases work with
  | pending phase queue =>
    apply lane_demand_exists _ _ _ _ (.emitAck sender.other true)
    simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase]
    rfl
  | ingress path => exact lane_demand_exists _ _ _ _ _ (path.action _)
  | ticket path => exact lane_demand_exists _ _ _ _ _ (path.action _)
  | link path => exact lane_demand_exists _ _ _ _ _ (path.action _)

private theorem active_pending (active : Active core) (mode : monitor.mode = .originals) :
    ∃ demand, OriginalM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand := by
  have lowerSent : monitor.lower.phase ≠ .needSend := by
    intro pending
    have bound := original_cost active.lowerLane
    rw [pending] at bound
    change 8 ≤ 7 at bound
    omega
  have upperSent : monitor.upper.phase ≠ .needSend := by
    intro pending
    have bound := original_cost active.upperLane
    rw [pending] at bound
    change 8 ≤ 7 at bound
    omega
  cases ack : monitor.ack with
  | some lane =>
    obtain ⟨demand, pending⟩ := ack_demand active lane ack
    exact ⟨.single demand, by simp only [OriginalM.nextDemand, mode,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lowerSent,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr upperSent,
      Bool.false_eq_true, ite_false, ack, pending, Option.map_some]⟩
  | none =>
    have pending :
        (∃ demand, OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower = some demand) ∨
        (∃ demand, OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.upper = some demand) := by
      cases active.lowerLane with
      | active work missing => exact .inl (data_demand work)
      | done lowerDone =>
        cases active.upperLane with
        | active work missing => exact .inr (data_demand work)
        | done upperDone => exact False.elim (active.originalOpen mode ack ⟨lowerDone, upperDone⟩)
    rcases pending with ⟨demand, lower⟩ | ⟨demand, upper⟩
    · refine ⟨.originalChoice (some demand) (OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.upper), ?_⟩
      simp only [OriginalM.nextDemand, mode,
        (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lowerSent,
        (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr upperSent,
        Bool.false_eq_true, ite_false, ack, lower, Option.isSome_some, Bool.true_or, ite_true]
    · refine ⟨.originalChoice (OriginalM.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) (some demand), ?_⟩
      simp only [OriginalM.nextDemand, mode,
        (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lowerSent,
        (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr upperSent,
        Bool.false_eq_true, ite_false, ack, upper, Option.isSome_some, Bool.or_true, ite_true]

theorem Evidence.original_pending (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals) :
    ∃ demand, OriginalM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand := by
  cases value with
  | written before sources =>
    exact ⟨.single (.operation (.send sender lower.length true)), by
      simp only [OriginalM.nextDemand, mode, before.lowerPending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
      rfl⟩
  | upper first before sources =>
    have lowerSent : monitor.lower.phase ≠ .needSend := by
      rcases before.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
    exact ⟨.single (.operation (.send sender upper.length true)), by
      simp only [OriginalM.nextDemand, mode, (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lowerSent,
        Bool.false_eq_true, ite_false, before.upperPending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
      rfl⟩
  | active core active => exact active_pending active mode
  | ready core ready => rw [ready.mode] at mode; cases mode
  | done done => rw [done.mode] at mode; cases mode

end Netlib.Check.CampusTCPTwoProgressEvidence
