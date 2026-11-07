import Netlib.Check.CampusTCPTwoTransferEvidence

/-!
# A selected drain extends the same recorded task

Queue closure selects the actual original ticket.
The same service preserves forward evidence and empties the primary queue.
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
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

include evidence in
theorem Evidence.drain_location (selected : W.drainTicket current.report.final monitor = some ticket) : location = .primary := by
  have controls := evidence.controls
  rw [CampusTCPTwoTransferDrainObserve.drain_mode selected] at controls
  cases controls
  rfl

include evidence in
theorem Evidence.drain_scope (selected : W.drainTicket current.report.final monitor = some ticket) : TransferScope monitor := by
  have mode := CampusTCPTwoTransferDrainObserve.drain_mode selected
  exact evidence.scope (by rw [mode]; decide) (by rw [mode]; decide)

theorem Evidence.drain_step (selected : W.drainTicket current.report.final monitor = some ticket)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .serve ticket none) :
    Nonempty (Advanced evidence actual) := by
  have locationEq := evidence.drain_location selected
  subst location
  have scopeBefore := evidence.drain_scope selected
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    have empty : current.report.final.outstanding .primary = 0 :=
      state.core.primaryQueue.no_tickets_zero (CampusTCPOrigins.Report.work_valid current.report)
        (by rw [state.lowerPending]; decide) (by rw [state.upperPending]; decide)
    have absent := CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero current.report.final monitor empty
    rw [absent] at selected
    cases selected
  | pending state =>
    have absent := CampusTCPTwoTransferControlObserve.noDrain_of_primary_zero current.report.final monitor state.primary_empty
    rw [absent] at selected
    cases selected
  | active state =>
    obtain ⟨value⟩ := CampusTCPTwoTransferDrainProgress.drain_step state controls scopeBefore.mode scopeBefore.resolved
      selected actual before event
    have allowed := value.allowed selected
    have nextMode : (W.observe cfg monitor actual).mode = .capture := by
      rw [value.value.observed]
      exact CampusTCPTwoTransferDrainObserve.drain_mode selected
    exact ⟨{
      move := value.value.value.value.move
      location := .primary
      next := {
        sent := _, received := _, core := value.value.next, forward := .active value.active
        controls := value.phase
        scope := fun _ _ => value.scope scopeBefore
        armed := by rw [nextMode]; intro impossible; cases impossible
        recorded := recorded.snoc value.value.value.value.move allowed } }⟩
  | readable core exchange mode sources _ _ =>
    have impossible := scopeBefore.mode
    rw [mode] at impossible
    cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
