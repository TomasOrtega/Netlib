import Netlib.Check.CampusTCPTwoProgressEvidenceAck
import Netlib.Check.CampusTCPTwoProgressEvidenceData

/-!
# Actual service for an original-stage demand

Current typed paths supply a serving event and its actual campus step.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)

namespace SelectedM
export CampusTCPTwoProgressMonitor (Monitor Config Demand nextDemand laneDemand serves servesOption)
end SelectedM

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : SelectedM.Monitor} {demand : SelectedM.Demand}

private theorem ack_serves (cfg : SelectedM.Config) (state : State input) (monitor : SelectedM.Monitor)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (lane : CampusTCPTwoProgressMonitor.Lane)
    (ack : monitor.ack = some lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction cfg.toConfig state lane.toGap = some action)
    (pending : SelectedM.nextDemand cfg state monitor = some demand) :
    SelectedM.serves demand action.event = true := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves cfg state monitor lane action next
  simp only [SelectedM.nextDemand, mode,
    (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
    (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr second,
    Bool.false_eq_true, ite_false, ack] at pending
  cases found : SelectedM.laneDemand cfg state monitor lane with
  | none => rw [found] at pending; cases pending
  | some raw =>
    have same : (.single raw : SelectedM.Demand) = demand := by simpa only [found, Option.map_some, Option.some.injEq] using pending
    cases same
    simpa only [SelectedM.servesOption, found, SelectedM.serves] using serves

private theorem data_serves (cfg : SelectedM.Config) (state : State input) (monitor : SelectedM.Monitor)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (action : CampusTCPRoundMonitor.Action)
    (serves : SelectedM.servesOption (SelectedM.laneDemand cfg state monitor monitor.lower) action.event = true ∨
      SelectedM.servesOption (SelectedM.laneDemand cfg state monitor monitor.upper) action.event = true)
    (pending : SelectedM.nextDemand cfg state monitor = some demand) : SelectedM.serves demand action.event = true := by
  simp only [SelectedM.nextDemand, mode,
    (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
    (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr second,
    Bool.false_eq_true, ite_false, ack] at pending
  split at pending
  · have same := Option.some.inj pending
    rw [← same]
    exact (CampusTCPTwoProgressMonitorFacts.serves_originalChoice _ _ _).mpr serves
  · cases pending

theorem Evidence.original_selected (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .originals)
    (pending : SelectedM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    ∃ event, Nonempty (Hop initial native quantum allowance current monitor event) ∧ SelectedM.serves demand event = true := by
  cases value with
  | written before sources =>
    have same : demand = .single (.operation (.send sender lower.length true)) := by
      simpa only [SelectedM.nextDemand, before.mode, before.lowerPending,
        CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true, config, Option.some.injEq] using pending.symm
    subst demand
    exact ⟨_, written_send_hop before sources, by cases sender <;> simp [SelectedM.serves, CampusTCPGapProgressMonitor.serves, CampusTCPRoundMonitor.actionOf]⟩
  | upper first before sources =>
    have noLower : monitor.lower.phase ≠ .needSend := by
      rcases before.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
    have same : demand = .single (.operation (.send sender upper.length true)) := by
      simpa only [SelectedM.nextDemand, before.mode,
        (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr noLower, Bool.false_eq_true, ite_false,
        before.upperPending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true, config, Option.some.injEq] using pending.symm
    subst demand
    exact ⟨_, upper_send_hop before sources, by cases sender <;> simp [SelectedM.serves, CampusTCPGapProgressMonitor.serves, CampusTCPRoundMonitor.actionOf]⟩
  | active core active =>
    have noLower := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.lowerLane
    have noUpper := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.upperLane
    cases ack : monitor.ack with
    | some lane =>
      have work : AckWork core lane := by simpa only [AckState, ack] using active.ack
      have command : ∃ action, CampusTCPGapProgressMonitor.nextAction
          (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action := by
        cases work with
        | pending phase queue =>
          exact ⟨.emitAck sender.other true, by simp only [CampusTCPGapProgressMonitor.nextAction,
            CampusTCPTwoProgressMonitor.Lane.toGap, phase]; rfl⟩
        | ingress path => exact ⟨_, path.action _⟩
        | ticket path => exact ⟨_, path.action _⟩
        | link path => exact ⟨_, path.action _⟩
      obtain ⟨action, next⟩ := command
      exact ⟨action.event, ack_hop active ack action next, ack_serves _ _ _ mode noLower noUpper lane ack action next pending⟩
    | none =>
      cases first : active.lowerLane with
      | active work missing =>
        let action := work.command (config initial native quantum allowance)
        have next := work.command_next (config initial native quantum allowance)
        have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance) current.report.final monitor monitor.lower action next
        exact ⟨action.event, lower_hop active mode ack action next,
          data_serves _ _ _ mode noLower noUpper ack action (.inl serves) pending⟩
      | done lowerDone =>
        cases active.upperLane with
        | active work missing =>
          let action := work.command (config initial native quantum allowance)
          have next := work.command_next (config initial native quantum allowance)
          have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance) current.report.final monitor monitor.upper action next
          exact ⟨action.event, upper_hop active mode ack action next,
            data_serves _ _ _ mode noLower noUpper ack action (.inr serves) pending⟩
        | done upperDone => exact False.elim (active.originalOpen mode ack ⟨lowerDone, upperDone⟩)
  | ready core ready => rw [ready.mode] at mode; cases mode
  | done done => rw [done.mode] at mode; cases mode

end Netlib.Check.CampusTCPTwoProgressEvidence
