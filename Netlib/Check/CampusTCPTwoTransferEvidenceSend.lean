import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferSendSelection
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Original sends extend the same forward evidence

The actual allowed send selects the lower or upper pending original.
Its new output and writer source stay on the original recorded trace.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {count : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem allowed_send (config : CampusTCPTwoTransferMonitor.Config) (state : State input) (monitor : W.Monitor)
    (actor : Actor) (count : Nat) (allowed : W.Allowed config state monitor (.send actor count true)) :
    W.controlDemand monitor = none ∧
      CampusTCPTwoExchangeMonitor.Allowed (config.at state) state monitor.exchange (.send actor count true) := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : W.drainTicket state monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : W.controlDemand monitor with
      | none => exact ⟨rfl, by simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid,
          decide_false, Bool.false_eq_true, ite_false, drain, selected, CampusTCPTwoExchangeMonitor.Allowed] using allowed⟩
      | some kind =>
        cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.send_step (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .send sender count true)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced evidence actual) := by
  obtain ⟨ordinary, localAllowed⟩ := allowed_send cfg current.report.final monitor sender count (by rw [← event]; exact allowed)
  have localCheck : CampusTCPTwoProgressMonitor.Allowed ((cfg).at current.report.final).forward current.report.final
      monitor.exchange.forward (.send sender count true) := by
    simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
      evidence.forward.exchange, CampusTCPTwoProgressMonitor.Allowed] using localAllowed
  have selected := CampusTCPTwoTransferSendSelection.local_send localCheck
  have idle := evidence.controls.ordinary_modes ordinary
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    have countEq : count = lower.length := by
      rcases selected.2 with lower | upper
      · exact lower.2.2
      · exact False.elim (upper.1 state.lowerPending)
    subst count
    obtain ⟨value⟩ := CampusTCPTwoTransferPreparationSend.Step.first_send state
      (by rw [← event]; exact allowed) actual before event
    have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.observed]; rfl
    exact ⟨{
      move := value.facts.move, location
      next := {
        sent := _, received := .empty, core := value.next.core, forward := .pending value.next
        controls := by rw [nextMode]; exact controls.nonservice ordinary value.facts.move (by rw [value.facts.event]; trivial)
        scope := by
          intro unarmed unfinished
          rw [nextMode] at unarmed unfinished
          rcases idle with idle | idle
          · exact False.elim (unarmed idle)
          · exact False.elim (unfinished idle)
        armed := fun _ => value.next.mode
        recorded := recorded.snoc value.facts.move value.allowed } }⟩
  | pending state =>
    have countEq : count = upper.length := by
      rcases selected.2 with lower | upper
      · rcases state.lowerPath.phase with ingress | lost
        · rw [ingress] at lower
          cases lower.1
        · rw [lost] at lower
          cases lower.1
      · exact upper.2.2.2
    subst count
    obtain ⟨value⟩ := CampusTCPTwoTransferPreparationSend.Step.second_send state
      (by rw [← event]; exact allowed) actual before event
    have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.observed]; rfl
    exact ⟨{
      move := value.facts.move, location
      next := {
        sent := _, received := .empty, core := value.next, forward := .active value.active
        controls := by rw [nextMode]; exact controls.nonservice ordinary value.facts.move (by rw [value.facts.event]; trivial)
        scope := by
          intro unarmed unfinished
          rw [nextMode] at unarmed unfinished
          rcases idle with idle | idle
          · exact False.elim (unarmed idle)
          · exact False.elim (unfinished idle)
        armed := by rw [value.observed]; intro _; exact state.mode
        recorded := recorded.snoc value.facts.move value.allowed } }⟩
  | active state =>
    rcases selected.2 with lower | upper
    · exact False.elim (state.lower_not_needSend lower.1)
    · exact False.elim (state.upper_not_needSend upper.2.1)
  | readable core exchange mode sources _ _ =>
    have impossible := selected.1
    rw [mode] at impossible
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
