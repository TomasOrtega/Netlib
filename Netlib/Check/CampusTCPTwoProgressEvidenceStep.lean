import Netlib.Check.CampusTCPTwoProgressEvidenceDispatch
import Netlib.Check.CampusTCPTwoProgressEvidenceChoice
import Netlib.Check.CampusTCPTwoProgressEvidenceAck
import Netlib.Check.CampusTCPTwoProgressEvidenceData
import Netlib.Check.CampusTCPTwoProgressEvidenceDrop
import Netlib.Check.CampusTCPTwoProgressEvidenceTimer

/-!
# Preservation under every allowed actual step

The current raw selection determines an enabled operation.
Its deterministic step preserves evidence on the same report suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {core : Core initial native quantum allowance current monitor sent received}

theorem active_step (active : Active core) (budget : allowance ≤ 2) (actual : Step input)
    (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  classical
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · obtain ⟨actor, millis, event⟩ := clock
    obtain ⟨hop⟩ := (Evidence.active core active).clock_hop actor millis (by rw [← event]; exact allowed)
    exact hop.for_step actual before event
  by_cases drop : ∃ id, actual.event = .dropPacket id
  · obtain ⟨id, event⟩ := drop
    obtain ⟨target, selected⟩ := allowed_drop_target active id (by rw [← event]; exact allowed)
    obtain ⟨hop⟩ := drop_hop active id target selected
    exact hop.for_step actual before event
  have nonClock : ∀ actor millis, actual.event ≠ .advanceClock actor millis := fun actor millis same => clock ⟨actor, millis, same⟩
  have nonDrop : ∀ id, actual.event ≠ .dropPacket id := fun id same => drop ⟨id, same⟩
  cases allowed_choice active allowed nonClock nonDrop with
  | lower action mode ack next event =>
    obtain ⟨hop⟩ := lower_hop active mode ack action next
    exact hop.for_step actual before event
  | upper action mode ack _ next event =>
    obtain ⟨hop⟩ := upper_hop active mode ack action next
    exact hop.for_step actual before event
  | ack lane action pending next event =>
    obtain ⟨hop⟩ := ack_hop active pending action next
    exact hop.for_step actual before event
  | retry action _ _ _ next event =>
    obtain ⟨hop⟩ := retry_hop active action next
    exact hop.for_step actual before event
  | timeout _ _ waiting next event =>
    obtain ⟨hop⟩ := timeout_hop active waiting budget next
    exact hop.for_step actual before event

theorem Evidence.step (value : Evidence initial native quantum allowance current monitor) (budget : allowance ≤ 2)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance move.after
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual)) := by
  cases value with
  | written value sources => exact CampusTCPTwoProgressEvidenceDispatch.written_step value sources actual before allowed
  | upper first value sources => exact CampusTCPTwoProgressEvidenceDispatch.upper_step value sources actual before allowed
  | active core value => exact active_step value budget actual before allowed
  | ready core value => exact CampusTCPTwoProgressEvidenceDispatch.ready_step value actual before allowed
  | done value => exact CampusTCPTwoProgressEvidenceDispatch.done_step value actual before allowed

end Netlib.Check.CampusTCPTwoProgressEvidence
