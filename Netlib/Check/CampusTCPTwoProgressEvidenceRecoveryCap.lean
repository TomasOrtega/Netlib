import Netlib.Check.CampusTCPTwoProgressRecoveryCapBasic
import Netlib.Check.CampusTCPTwoProgressRecoveryCapAck
import Netlib.Check.CampusTCPTwoProgressRecoveryCapData
import Netlib.Check.CampusTCPTwoProgressRecoveryCapSettled
import Netlib.Check.CampusTCPTwoProgressEvidenceStep

/-!
# Fixed caps on allowed recovery steps

Each current selection preserves the same fixed cap.
Determinism identifies its witness with the supplied actual step.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)
open CampusTCPTwoProgressEvidence (Evidence Hop)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received} {event : Event}

theorem hop_for_step (hop : Hop initial native quantum allowance current monitor event)
    (bounded : PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor hop.actual))
    (actual : Step input) (before : actual.before = current.report.final) (selected : actual.event = event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) := by
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event hop.actual actual
    (hop.move.beforeEq.trans before.symm) (hop.selected.trans selected.symm)
  cases same
  exact ⟨hop.move, ⟨hop.next⟩, bounded⟩

theorem active_cap_step (active : Active core) (nonoriginal : monitor.mode ≠ .originals)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨hop, bounded⟩ := clock_hop_cap (.active core active) prior actor millis (by rw [← event]; exact allowed)
    exact hop_for_step hop bounded actual before event
  by_cases drop : ∃ id, actual.event = .dropPacket id
  · obtain ⟨id, event⟩ := drop
    obtain ⟨target, selected⟩ := CampusTCPTwoProgressEvidence.allowed_drop_target active id (by rw [← event]; exact allowed)
    obtain ⟨hop, bounded⟩ := CampusTCPTwoProgressRecoveryCapData.drop_cap_hop active nonoriginal prior id target selected
    exact hop_for_step hop bounded actual before event
  have nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis := fun actor millis same => clock ⟨actor, millis, same⟩
  have nonDrop : ∀ id, actual.event ≠ .dropPacket id := fun id same => drop ⟨id, same⟩
  cases CampusTCPTwoProgressEvidence.allowed_choice active allowed nonClock nonDrop with
  | lower _ mode _ _ _ => exact False.elim (nonoriginal mode)
  | upper _ mode _ _ _ _ => exact False.elim (nonoriginal mode)
  | ack lane action pending next event =>
    obtain ⟨hop, bounded⟩ := CampusTCPTwoProgressRecoveryCapAck.ack_hop_cap active nonoriginal prior pending action next
    exact hop_for_step hop bounded actual before event
  | retry action _ _ _ next event =>
    obtain ⟨hop, bounded⟩ := CampusTCPTwoProgressRecoveryCapData.retry_cap_hop active nonoriginal prior action next
    exact hop_for_step hop bounded actual before event
  | timeout _ _ waiting next event =>
    obtain ⟨hop, bounded⟩ := timeout_hop_cap active prior waiting budget next
    exact hop_for_step hop bounded actual before event

theorem cap_step (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) ∧
      PendingCap (config initial native quantum allowance) capacity move.after.report.final
        (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) := by
  cases value with
  | written value _ => exact False.elim (nonoriginal value.mode)
  | upper _ value _ => exact False.elim (nonoriginal value.mode)
  | active core value => exact active_cap_step value nonoriginal prior budget actual before allowed
  | ready _ value => exact CampusTCPTwoProgressRecoveryCapSettled.ready_cap_step value actual before allowed
  | done value => exact CampusTCPTwoProgressRecoveryCapSettled.done_cap_step value actual before allowed

end Netlib.Check.CampusTCPTwoProgressRecoveryCap
