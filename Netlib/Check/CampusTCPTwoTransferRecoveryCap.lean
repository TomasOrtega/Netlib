import Netlib.Check.CampusTCPTwoTransferRecoveryCapData

/-!
# Fixed pending cap on every actual recovery step

Current evidence supplies each selected path and timeout cause.
The cap follows the same supplied step until the actual read.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferHandoffRTO (PendingCap)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem read_cap (value : ReadAdvanced evidence actual) :
    PendingCap cfg capacity value.value.finalCut.report.final (W.observe cfg monitor actual) := by
  intro recovery runtime pending
  have source : G.senderRecovery (cfg).exchange.forward.toConfig value.value.finalCut.report.final =
      some value.value.value.senderFlight.recovery := by
    change G.senderRecovery (cfg).exchange.forward.toConfig value.value.value.move.after.report.final = _
    simp only [G.senderRecovery, value.value.value.move.after.connection, config,
      CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoExchangeSetup.config,
      CampusTCPTwoProgressSetup.config, value.value.value.senderFlight.runtime]
  have same := Option.some.inj (runtime.symm.trans source)
  have empty := value.value.value.senderFlight.ledger
  rw [← same] at empty
  exact False.elim (pending empty)

private theorem quiet_step (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (prior : PendingCap cfg capacity current.report.final monitor) (budget : allowance ≤ 2)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (quiet : QuietEvent actual.event) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) := by
  rcases evidence.step budget actual move.beforeEq allowed with advance | done
  · obtain ⟨advance⟩ := advance
    apply quiet_cap prior move quiet
    apply advanced_retries advance
    cases event : actual.event <;> simp_all [QuietEvent, CampusTCPTwoExchangeLoss.isTimeoutOutput]
  · obtain ⟨done⟩ := done
    rw [done.value.value.event] at quiet
    cases quiet

private theorem application_step (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (prior : PendingCap cfg capacity current.report.final monitor)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (application : ApplicationEvent actual.event) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) := by
  have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed evidence nonoriginal allowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => exact False.elim (nonoriginal state.mode)
  | pending state => exact False.elim (nonoriginal state.mode)
  | active state =>
    exact application_cap ⟨_, _, _, .active state, controls, scope, armed, recorded⟩ state
      (state.mode.resolve_left nonoriginal) prior move allowed application
  | readable core exchange mode sources duplicate mainAck =>
    obtain ⟨_, selected | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp localAllowed
    · obtain ⟨demand, pending, served⟩ := selected
      simp only [M.nextDemand, mode] at pending
      cases pending
      have event := (CampusTCPTwoProgressMonitorFacts.serves_operation _ _).mp served
      rw [event] at application
      cases application
    · obtain ⟨id, _, event, _⟩ := dropped
      rw [event] at application
      cases application
    · obtain ⟨actor, millis, event, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
      rw [event] at application
      cases application

private theorem timeout_step (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (prior : PendingCap cfg capacity current.report.final monitor) (budget : allowance ≤ 2)
    (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (event : actual.event = .timeout sender true) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) := by
  have canonical : W.Allowed cfg current.report.final monitor (.timeout sender true) := by rw [← event]; exact allowed
  obtain ⟨mode, waiting, _⟩ := evidence.timeout_fields canonical
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state => rw [state.mode] at mode; cases mode
  | pending state => rw [state.mode] at mode; cases mode
  | readable core exchange ready sources duplicate mainAck => rw [ready] at mode; cases mode
  | active state =>
    obtain ⟨value⟩ := CampusTCPTwoTransferTimeoutProgress.Step.timeout state waiting budget canonical actual move.beforeEq event
    have bounded := retried_cap value.value prior
    rw [value.value.value.move.final, ← move.final] at bounded
    exact bounded

theorem step (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (prior : PendingCap cfg capacity current.report.final monitor)
    (budget : allowance ≤ 2) (move : Move current actual) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    PendingCap cfg capacity move.after.report.final (W.observe cfg monitor actual) := by
  have ordinary := CampusTCPTwoTransferNonoriginal.ordinary evidence nonoriginal
  cases CampusTCPTwoTransferEvidenceEvents.classify evidence ordinary.2 ordinary.1 allowed with
  | send count event =>
    have localAllowed := CampusTCPTwoTransferNonoriginal.local_allowed evidence nonoriginal allowed
    rw [event] at localAllowed
    exact False.elim (nonoriginal (CampusTCPTwoTransferSendSelection.local_send localAllowed).1)
  | assign index ingress event => exact quiet_step evidence prior budget move allowed (by rw [event]; trivial)
  | serve ticket event => exact quiet_step evidence prior budget move allowed (by rw [event]; trivial)
  | deliver index bytes event => exact application_step evidence nonoriginal prior move allowed (by rw [event]; trivial)
  | ack event => exact application_step evidence nonoriginal prior move allowed (by rw [event]; trivial)
  | read mode event =>
    obtain ⟨value⟩ := evidence.read_step mode actual move.beforeEq event
    have bounded := read_cap (capacity := capacity) value
    change PendingCap cfg capacity value.value.value.move.after.report.final _ at bounded
    rw [value.value.value.move.final, ← move.final] at bounded
    exact bounded
  | clock actor millis event =>
    obtain ⟨value⟩ := CampusTCPTwoTransferLocatedClock.Step.clock evidence.core evidence.forward.exchange evidence.forward.not_done
      actual move.beforeEq event (by rw [← event]; exact allowed)
    have bounded := clock_cap value prior
    rw [value.move.final, ← move.final] at bounded
    exact bounded
  | timeout event => exact timeout_step evidence prior budget move allowed event
  | drop id event => exact quiet_step evidence prior budget move allowed (by rw [event]; trivial)

end Netlib.Check.CampusTCPTwoTransferRecoveryCap
