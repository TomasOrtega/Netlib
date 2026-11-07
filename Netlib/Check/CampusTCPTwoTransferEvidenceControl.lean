import Netlib.Check.CampusTCPTwoTransferEvidence

/-!
# Actual control steps extend the same forward evidence

The current control demand supplies the move and stored checkpoint result.
Each phase retains the original task, action record, and loss history.
-/

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferScope (TransferScope)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {kind : W.Control}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem before_scope (scope : Scoped monitor) (selected : W.controlDemand monitor = some kind) :
    TransferScope monitor := by
  by_cases armed : monitor.mode = .armed
  · have same : kind = .pause := by
      simp only [W.controlDemand, armed] at selected
      split at selected
      · exact Option.some.inj selected.symm
      · cases selected
    subst kind
    exact TransferScope.of_pause armed selected
  · by_cases finished : monitor.mode = .finished
    · simp only [W.controlDemand, finished] at selected
      cases selected
    · exact scope armed finished

private theorem next_scope (scope : Scoped monitor)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    Scoped (W.observe cfg monitor actual) :=
  fun _ _ => (before_scope scope selected).control value selected drainless

private theorem next_armed (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    (W.observe cfg monitor actual).mode = .armed →
      (W.observe cfg monitor actual).exchange.forward.mode = .originals := by
  rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]
  cases kind <;> intro impossible <;> cases impossible

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

theorem Evidence.control_step (selected : W.controlDemand monitor = some kind)
    (drainless : W.drainTicket current.report.final monitor = none)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = kind.event cfg) :
    Nonempty (Advanced evidence actual) := by
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    obtain ⟨value⟩ := state.control_step controls selected drainless actual before event
    have allowed := CampusTCPTwoTransferControlObserve.control_allowed value.advance.value selected drainless
    exact ⟨{
      move := value.advance.value.move
      location := CampusTCPTwoTransferControlState.afterLocation kind
      next := {
        sent := .written, received := .empty, core := value.next.core, forward := .written value.next
        controls := value.next_phase
        scope := next_scope scope value.advance.value selected drainless
        armed := next_armed value.advance.value selected drainless
        recorded := recorded.snoc value.advance.value.move allowed } }⟩
  | pending state =>
    obtain ⟨value⟩ := state.control_step controls selected drainless actual before event
    have allowed := CampusTCPTwoTransferControlObserve.control_allowed value.advance.value selected drainless
    exact ⟨{
      move := value.advance.value.move
      location := CampusTCPTwoTransferControlState.afterLocation kind
      next := {
        sent := _, received := .empty, core := value.next.core, forward := .pending value.next
        controls := value.next_phase
        scope := next_scope scope value.advance.value selected drainless
        armed := next_armed value.advance.value selected drainless
        recorded := recorded.snoc value.advance.value.move allowed } }⟩
  | active state =>
    obtain ⟨value⟩ := state.control_step controls selected drainless actual before event
    have allowed := CampusTCPTwoTransferControlObserve.control_allowed value.advance.value selected drainless
    exact ⟨{
      move := value.advance.value.move
      location := CampusTCPTwoTransferControlState.afterLocation kind
      next := {
        sent := _, received := _, core := value.next, forward := .active value.active
        controls := value.next_phase
        scope := next_scope scope value.advance.value selected drainless
        armed := next_armed value.advance.value selected drainless
        recorded := recorded.snoc value.advance.value.move allowed } }⟩
  | readable core exchange mode sources _ _ =>
    have finished : monitor.mode = .finished := by
      by_cases finished : monitor.mode = .finished
      · exact finished
      · by_cases unarmed : monitor.mode = .armed
        · have original := armed unarmed
          rw [mode] at original
          cases original
        · have original := (scope unarmed finished).mode
          rw [mode] at original
          cases original
    simp only [W.controlDemand, finished] at selected
    cases selected

theorem Evidence.control_at (selected : W.controlDemand monitor = some kind)
    (drainless : W.drainTicket current.report.final monitor = none) :
    ∃ actual, Nonempty (Advanced evidence actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoTransferControlState.control_at evidence.core evidence.controls selected drainless
  exact ⟨actual, evidence.control_step selected drainless actual value.value.move.beforeEq value.value.eventEq⟩

end Netlib.Check.CampusTCPTwoTransferEvidence
