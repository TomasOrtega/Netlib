import Netlib.Check.CampusTCPTwoProgressRecoveryRank
import Netlib.Check.CampusTCPTwoProgressRecoveryCapBasic
import Netlib.Check.CampusTCPTwoProgressEvidenceDispatch

/-!
# Fixed recovery caps after sender retirement

The actual retired sender has no outstanding timer work.
Reads and allowed clocks retain that settled state on the same trace.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCapSettled

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence Ready Complete Hop)
open CampusTCPTwoProgressRecoveryCap (PendingCap empty_core complete_cap clock_hop_cap)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Allowed nextDemand dropTarget observe)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff serves_operation freeClock_event)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {event : Event}

theorem settled_cap (value : Evidence initial native quantum allowance current monitor)
    (mode : monitor.mode = .needRead ∨ monitor.mode = .done) :
    PendingCap (config initial native quantum allowance) capacity current.report.final monitor := by
  cases value with
  | written value _ => rcases mode with mode | mode <;> rw [value.mode] at mode <;> cases mode
  | upper _ value _ => rcases mode with mode | mode <;> rw [value.mode] at mode <;> cases mode
  | active core active =>
    rcases active.mode with before | before <;>
      rcases mode with mode | mode <;> rw [before] at mode <;> cases mode
  | ready core ready => exact empty_core core ready.retired
  | done value => exact complete_cap value

theorem settled_event (mode : monitor.mode = .needRead ∨ monitor.mode = .done)
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
  · obtain ⟨actor, millis, selected, _⟩ := F.freeClock_event _ _ _ _ free
    exact .inr ⟨actor, millis, selected⟩

theorem ready_read_hop_cap (ready : Ready core) :
    ∃ hop : Hop initial native quantum allowance current monitor (.read sender.other (lower ++ upper).length),
      PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor hop.actual) := by
  cases sent with
  | written | lower => cases ready.preparing
  | both | tail => cases ready.retired
  | retired first second =>
    have all := CampusTCPTwoProgressPhaseNormalize.retired_allReleased core
    cases all
    obtain ⟨actual, ⟨record⟩⟩ := CampusTCPTwoProgressPhaseRead.read_at core ready.mode
    let done : Complete initial native quantum allowance record.value.move.after
        (M.observe (config initial native quantum allowance) monitor actual) := {
      first, second, timeouts := monitor.retries
      completed := record.completed
      retryCount := record.retries.symm
      losses := record.losses
      lossBound := record.lossBound
      sources := ready.sources.non_delivery record.value.move (by rw [record.value.event]; trivial)
      mode := record.mode
      stamp := by rw [record.completed_operation]; exact record.stamp
      bytes := record.bytes
      originals := record.originals
      originalTimes := record.originalTimes
      writer := record.writer
      senderDuplicate := ready.read_duplicate record
      gatewayComplete := ready.read_gateway record }
    exact ⟨⟨actual, record.value.move, record.value.event, .done done⟩, complete_cap done⟩

private theorem observed_read_done (monitor : M.Monitor) (actual : Step input)
    (ready : monitor.mode = .needRead) (selected : actual.event = .read actor count)
    (healthy : (M.observe cfg monitor actual).mode ≠ .invalid) :
    (M.observe cfg monitor actual).mode = .done := by
  unfold M.observe at healthy ⊢
  simp only [selected, CampusTCPTwoProgressMonitor.observeOrdinary, ready] at healthy ⊢
  unfold CampusTCPTwoProgressMonitor.observeRead at healthy ⊢
  repeat' first
    | (solve | rfl)
    | (solve | exact False.elim (healthy rfl))
    | split at *

theorem read_hop_strict (ready : Ready core) (bound : Nat) :
    ∃ hop : Hop initial native quantum allowance current monitor (.read sender.other (lower ++ upper).length),
      CampusTCPTwoProgressRecoveryRank.rank (config initial native quantum allowance) bound allowance hop.move.after.report.final
          (M.observe (config initial native quantum allowance) monitor hop.actual) <
        CampusTCPTwoProgressRecoveryRank.rank (config initial native quantum allowance) bound allowance current.report.final monitor := by
  obtain ⟨hop, _⟩ := ready_read_hop_cap (capacity := 0) ready
  have done := observed_read_done monitor hop.actual ready.mode hop.selected hop.next.healthy
  exact ⟨hop, CampusTCPTwoProgressRecoveryRank.read_done_step _ _ _ _ _ _ _ ready.mode done⟩

theorem read_step_done (ready : Ready core) (actual : Step input) (move : Move current actual)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event)
    (selected : actual.event = .read sender.other (lower ++ upper).length) :
    (M.observe (config initial native quantum allowance) monitor actual).mode = .done := by
  obtain ⟨_, ⟨next⟩⟩ := CampusTCPTwoProgressEvidenceDispatch.ready_step ready actual move.beforeEq allowed
  exact observed_read_done monitor actual ready.mode selected next.healthy

private theorem cap_for_step {selectedEvent : Event}
    (hop : Hop initial native quantum allowance current monitor selectedEvent)
    (cap : PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
      (M.observe (config initial native quantum allowance) monitor hop.actual))
    (actual : Step input) (before : actual.before = current.report.final) (selected : actual.event = selectedEvent) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (M.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (M.observe (config initial native quantum allowance) monitor actual) := by
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event hop.actual actual
    (hop.move.beforeEq.trans before.symm) (hop.selected.trans selected.symm)
  cases same
  exact ⟨hop.move, ⟨hop.next⟩, cap⟩

theorem ready_cap_step (ready : Ready core) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (M.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (M.observe (config initial native quantum allowance) monitor actual) := by
  rcases settled_event (.inl ready.mode) allowed with ⟨_, selected⟩ | ⟨actor, millis, selected⟩
  · obtain ⟨hop, cap⟩ := ready_read_hop_cap (capacity := capacity) ready
    exact cap_for_step hop cap actual before selected
  · obtain ⟨hop, cap⟩ := clock_hop_cap (.ready core ready) (empty_core core ready.retired) actor millis
      (by rw [← selected]; exact allowed)
    exact cap_for_step hop cap actual before selected

theorem done_cap_step (done : Complete initial native quantum allowance current monitor)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (M.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (M.observe (config initial native quantum allowance) monitor actual) := by
  rcases settled_event (.inr done.mode) allowed with ⟨reading, _⟩ | ⟨actor, millis, selected⟩
  · rw [done.mode] at reading
    cases reading
  · obtain ⟨hop, cap⟩ := clock_hop_cap (.done done) (complete_cap done) actor millis (by rw [← selected]; exact allowed)
    exact cap_for_step hop cap actual before selected

end Netlib.Check.CampusTCPTwoProgressRecoveryCapSettled
