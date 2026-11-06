import Netlib.Check.CampusTCPTwoProgressEvidenceHop

/-!
# Allowed events before service and after retirement

The raw monitor selects the actual send, side loss, read or clock.
Determinism binds each enabled witness to the supplied trace step.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidenceDispatch

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Config Allowed nextDemand dropTarget exposedPacket)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff serves_operation freeClock_event dropTarget_packet)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {event : Event}

private theorem unexposed (cfg : M.Config) (state : State input) (lane : M.Lane)
    (phase : lane.phase = .needSend ∨ lane.phase = .done) : M.exposedPacket cfg state lane = none := by
  rcases phase with phase | phase <;>
    simp only [M.exposedPacket, CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap,
      phase, bind, Option.bind]

theorem drop_budget (cfg : M.Config) (state : State input) (monitor : M.Monitor) (id : Nat)
    (selected : M.dropTarget cfg state monitor id = some target) : monitor.drops.length < cfg.lossAllowance := by
  unfold M.dropTarget at selected
  split at selected
  · split at selected
    · assumption
    · cases selected
  · cases selected

private theorem written_no_drop (before : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
    (id : Nat) : M.dropTarget (config initial native quantum allowance) current.report.final monitor id = none := by
  have first := unexposed (config initial native quantum allowance) current.report.final monitor.lower (.inl before.lowerPending)
  have second := unexposed (config initial native quantum allowance) current.report.final monitor.upper (.inl before.upperPending)
  have retry := unexposed (config initial native quantum allowance) current.report.final monitor.retry (.inr before.retry)
  simp [M.dropTarget, before.mode, first, second, retry, before.ack]

theorem written_event (before : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor event) :
    event = .send sender lower.length true ∨ ∃ actor millis, event = .advanceClock actor millis := by
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    have next : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
        some (.single (.operation (.send sender lower.length true))) := by
      simp only [M.nextDemand, before.mode, before.lowerPending,
        CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
      rfl
    have same := Option.some.inj (pending.symm.trans next)
    subst demand
    exact .inl ((F.serves_operation _ _).mp served)
  · obtain ⟨id, target, _, selected⟩ := dropped
    rw [written_no_drop before id] at selected
    cases selected
  · obtain ⟨actor, millis, event, _⟩ := F.freeClock_event _ _ _ _ free
    exact .inr ⟨actor, millis, event⟩

private theorem upper_drop (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (id : Nat) (selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target) :
    target = .lower ∧ monitor.lower.phase = .dataIngress ∧ monitor.drops.length < allowance := by
  have packet := F.dropTarget_packet _ _ _ _ selected
  have onlyLower : target = .lower := by
    cases target with
    | lower => rfl
    | upper =>
      rw [unexposed _ _ monitor.upper (.inl before.upperPending)] at packet
      cases packet
    | retry =>
      rw [unexposed _ _ monitor.retry (.inr before.retry)] at packet
      cases packet
    | ack =>
      obtain ⟨lane, pending, _⟩ := packet
      rw [before.ack] at pending
      cases pending
  subst target
  have phase : monitor.lower.phase = .dataIngress := by
    rcases before.lowerPath.phase with ingress | done
    · exact ingress
    · rw [unexposed _ _ monitor.lower (.inr done)] at packet
      cases packet
  exact ⟨rfl, phase, drop_budget _ _ _ _ selected⟩

theorem upper_event (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor event) :
    event = .send sender upper.length true ∨
      (∃ id, event = .dropPacket id ∧
        M.dropTarget (config initial native quantum allowance) current.report.final monitor id = some .lower ∧
        monitor.lower.phase = .dataIngress ∧ monitor.drops.length < allowance) ∨
      ∃ actor millis, event = .advanceClock actor millis := by
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    have notPending : monitor.lower.phase ≠ .needSend := by
      rcases before.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
    have next : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
        some (.single (.operation (.send sender upper.length true))) := by
      simp only [M.nextDemand, before.mode, (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr notPending,
        Bool.false_eq_true, ite_false, before.upperPending, CampusTCPTwoProgressMonitorFacts.phase_beq_self, ite_true]
      rfl
    have same := Option.some.inj (pending.symm.trans next)
    subst demand
    exact .inl ((F.serves_operation _ _).mp served)
  · obtain ⟨id, target, event, selected⟩ := dropped
    obtain ⟨targetEq, phase, budget⟩ := upper_drop before id selected
    subst target
    exact .inr (.inl ⟨id, event, selected, phase, budget⟩)
  · obtain ⟨actor, millis, event, _⟩ := F.freeClock_event _ _ _ _ free
    exact .inr (.inr ⟨actor, millis, event⟩)

private theorem settled_event (mode : monitor.mode = .needRead ∨ monitor.mode = .done)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor event) :
    (monitor.mode = .needRead ∧ event = .read sender.other (lower ++ upper).length) ∨
      ∃ actor millis, event = .advanceClock actor millis := by
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    rcases mode with mode | mode
    · have next : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
          some (.single (.operation (.read sender.other (lower ++ upper).length))) := by rw [M.nextDemand, mode]; rfl
      have same := Option.some.inj (pending.symm.trans next)
      subst demand
      exact .inl ⟨mode, (F.serves_operation _ _).mp served⟩
    · simp only [M.nextDemand, mode] at pending
      cases pending
  · obtain ⟨id, target, _, selected⟩ := dropped
    rcases mode with mode | mode <;> rw [M.dropTarget, mode] at selected <;> cases selected
  · obtain ⟨actor, millis, event, _⟩ := F.freeClock_event _ _ _ _ free
    exact .inr ⟨actor, millis, event⟩

theorem written_step (before : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) (actual : Step input)
    (beforeEq : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  rcases written_event before allowed with selected | ⟨actor, millis, selected⟩
  · obtain ⟨hop⟩ := written_send_hop before sources
    exact hop.for_step actual beforeEq selected
  · obtain ⟨hop⟩ := (Evidence.written before sources).clock_hop actor millis (by rw [← selected]; exact allowed)
    exact hop.for_step actual beforeEq selected

theorem upper_step (before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) (actual : Step input)
    (beforeEq : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  rcases upper_event before allowed with selected | ⟨id, selected, target, pending, budget⟩ | ⟨actor, millis, selected⟩
  · obtain ⟨hop⟩ := upper_send_hop before sources
    exact hop.for_step actual beforeEq selected
  · obtain ⟨hop⟩ := upper_lower_drop_hop before sources id pending budget target
    exact hop.for_step actual beforeEq selected
  · obtain ⟨hop⟩ := (Evidence.upper _ before sources).clock_hop actor millis (by rw [← selected]; exact allowed)
    exact hop.for_step actual beforeEq selected

theorem ready_step {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
    {core : CampusTCPTwoProgressPhaseBase.Core initial native quantum allowance current monitor sent received}
    (ready : Ready core) (actual : Step input) (beforeEq : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  rcases settled_event (.inl ready.mode) allowed with ⟨_, selected⟩ | ⟨actor, millis, selected⟩
  · cases sent with
    | written | lower => cases ready.preparing
    | both | tail => cases ready.retired
    | retired first second =>
      have all := CampusTCPTwoProgressPhaseNormalize.retired_allReleased core
      cases all
      obtain ⟨hop⟩ := ready_read_hop ready
      exact hop.for_step actual beforeEq selected
  · obtain ⟨hop⟩ := (Evidence.ready core ready).clock_hop actor millis (by rw [← selected]; exact allowed)
    exact hop.for_step actual beforeEq selected

theorem done_step (done : Complete initial native quantum allowance current monitor) (actual : Step input)
    (beforeEq : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  rcases settled_event (.inr done.mode) allowed with ⟨reading, _⟩ | ⟨actor, millis, selected⟩
  · rw [done.mode] at reading
    cases reading
  · obtain ⟨hop⟩ := (Evidence.done done).clock_hop actor millis (by rw [← selected]; exact allowed)
    exact hop.for_step actual beforeEq selected

end Netlib.Check.CampusTCPTwoProgressEvidenceDispatch
