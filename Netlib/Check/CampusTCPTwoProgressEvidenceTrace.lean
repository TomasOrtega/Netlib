import Netlib.Check.CampusTCPTwoProgressEvidence

/-!
# Checked steps in the same retained suffix

An invalid monitor cannot become healthy again.
A healthy final phase therefore proves that every suffix step passed.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidenceTrace

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Evidence Complete)

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Allowed observe)
end M

theorem observe_invalid {input : Input} (cfg : M.Config) (monitor : M.Monitor) (actual : Step input)
    (invalid : monitor.mode = .invalid) : (M.observe cfg monitor actual).mode = .invalid := by
  simp only [M.observe, CampusTCPTwoProgressMonitor.allowed, invalid,
    show (CampusTCPTwoProgressMonitor.Mode.invalid == .invalid) = true from rfl,
    ite_true, Bool.and_false, Bool.false_eq_true, ite_false]
  rfl

theorem observe_checked {input : Input} (cfg : M.Config) (monitor : M.Monitor) (actual : Step input)
    (healthy : (M.observe cfg monitor actual).mode ≠ .invalid) :
    monitor.mode ≠ .invalid ∧ actual.result.supported = true ∧ actual.result.passed = true ∧
      M.Allowed cfg actual.before monitor actual.event := by
  have before : monitor.mode ≠ .invalid := fun invalid => healthy (observe_invalid cfg monitor actual invalid)
  refine ⟨before, ?_⟩
  unfold M.observe at healthy
  split at healthy
  · rename_i checked
    simp only [Bool.and_eq_true] at checked
    exact ⟨checked.1.1, checked.1.2, checked.2⟩
  · exact False.elim (healthy rfl)

theorem fold_passed {input : Input} (cfg : M.Config) (monitor : M.Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (M.observe cfg) monitor).mode ≠ .invalid) :
    monitor.mode ≠ .invalid ∧ ∀ actual ∈ steps, actual.result.supported = true ∧ actual.result.passed = true := by
  induction steps generalizing monitor with
  | nil => exact ⟨healthy, by simp⟩
  | cons actual rest ih =>
    obtain ⟨next, tail⟩ := ih (M.observe cfg monitor actual) healthy
    obtain ⟨before, supported, passed, _⟩ := observe_checked cfg monitor actual next
    refine ⟨before, ?_⟩
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · subst chosen
      exact ⟨supported, passed⟩
    · exact tail chosen later

end Netlib.Check.CampusTCPTwoProgressEvidenceTrace

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor}

def Evidence.losses (value : Evidence initial native quantum allowance current monitor) :
    CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) current monitor := by
  cases value with
  | written value _ => exact value.core.losses
  | upper _ value _ => exact value.core.losses
  | active core _ => exact core.losses
  | ready core _ => exact core.losses
  | done value => exact value.losses

theorem Evidence.passed (value : Evidence initial native quantum allowance current monitor) :
    ∀ actual ∈ value.losses.suffix, actual.result.passed = true := by
  have healthy : (value.losses.suffix.foldl (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance)) .initial).mode ≠ .invalid := by
    rw [value.losses.observed]
    exact value.healthy
  have checked := (CampusTCPTwoProgressEvidenceTrace.fold_passed _ _ _ healthy).2
  exact fun actual member => (checked actual member).2

theorem Evidence.compliant (value : Evidence initial native quantum allowance current monitor)
    (prior : cut.report.compliant = true) : current.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report current.report current.supported prior
    value.losses.suffix value.losses.steps value.passed

theorem Complete.compliant (value : Complete initial native quantum allowance current monitor)
    (prior : cut.report.compliant = true) : current.report.compliant = true :=
  (Evidence.done value).compliant prior

theorem Complete.read_permissions (value : Complete initial native quantum allowance current monitor)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin value.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served := by
  obtain ⟨origin, writer⟩ := value.read_writer index byte selected
  refine ⟨origin, writer, ?_⟩
  exact CampusTCPRoundOrigins.service_permissions current.report (value.compliant prior)
    origin.delivery.service.joint.step origin.delivery.service.joint.member origin.delivery.receive.receipt.served
    origin.delivery.service.present origin.delivery.receive.receipt.emission origin.delivery.receive.receipt.emitted

end Netlib.Check.CampusTCPTwoProgressEvidence
