import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferTimeoutProgress
import Netlib.Check.CampusTCPTwoTransferTimeoutSelection
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

include evidence in
theorem Evidence.timeout_fields (allowed : W.Allowed cfg current.report.final monitor (.timeout actor true)) :
    monitor.exchange.forward.mode = .recovery ∧ monitor.exchange.forward.waiting = true ∧ actor = sender := by
  have fields := CampusTCPTwoTransferTimeoutObserve.allowed_timeout_fields cfg current.report.final monitor actor allowed evidence.forward.exchange
  obtain ⟨mode, waiting, actor⟩ := CampusTCPTwoTransferTimeoutSelection.allowed_timeout _ _ _ fields.2.2.2
  exact ⟨mode, waiting, by simpa only [config, CampusTCPTwoTransferNative.Checks.monitorConfig,
    CampusTCPTwoTransferMonitor.Config.at, CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config] using actor⟩

theorem Evidence.timeout_step (budget : allowance ≤ 2) (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .timeout actor true) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Nonempty (Advanced evidence actual) := by
  have timeoutAllowed : W.Allowed cfg current.report.final monitor (.timeout actor true) := by rw [← event]; exact allowed
  obtain ⟨mode, waiting, senderEq⟩ := evidence.timeout_fields timeoutAllowed
  subst actor
  have ordinary := (CampusTCPTwoTransferTimeoutObserve.allowed_timeout_fields cfg current.report.final monitor sender timeoutAllowed
    evidence.forward.exchange).2.2.1
  have finished := evidence.recovery_finished mode
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => rw [state.mode] at mode; cases mode
  | pending state => rw [state.mode] at mode; cases mode
  | readable _ _ ready _ _ _ => rw [ready] at mode; cases mode
  | active state =>
    obtain ⟨value⟩ := CampusTCPTwoTransferTimeoutProgress.Step.timeout state waiting budget timeoutAllowed actual before event
    have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.value.observed]; rfl
    have nextControls : C.Phase value.value.value.move.after.report.final (W.observe cfg monitor actual).mode location := by
      rw [nextMode]
      exact controls.nonservice ordinary value.value.value.move (by rw [event]; trivial)
    exact ⟨{
      move := value.value.value.move, location
      next := {
        sent := _, received := _, core := value.value.next, forward := .active value.next
        controls := nextControls
        scope := by intro _ unfinished; exact False.elim (unfinished (nextMode.trans finished))
        armed := by intro nextArmed; have impossible := nextMode.symm.trans nextArmed; rw [finished] at impossible; cases impossible
        recorded := recorded.snoc value.value.value.move allowed } }⟩

end Netlib.Check.CampusTCPTwoTransferEvidence
