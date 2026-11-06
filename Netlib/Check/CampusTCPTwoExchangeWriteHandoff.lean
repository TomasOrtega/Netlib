import Netlib.Check.CampusTCPTwoExchangeEvidenceWrite
import Netlib.Check.CampusTCPTwoExchangeAccounting

/-!
# The reverse start at the actual write exit

The observed reverse phase rules out a bridge clock.
The same stored write supplies the reverse initial state.
-/

namespace Netlib.Check.CampusTCPTwoExchangeWriteHandoff

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoReverseGeometry (Started)

namespace M
export CampusTCPTwoExchangeMonitor (Monitor observe Allowed)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

local notation "cfg" => CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper

theorem starts_of_exit (forward : Complete initial native quantum allowance current monitor.forward)
    (mode : monitor.mode = .needWrite)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : M.Allowed cfg current.report.final monitor actual.event)
    (after : (M.observe cfg monitor actual).mode = .reverse) :
    ∃ _start : Started forward reverseLower reverseUpper actual,
      (M.observe cfg monitor actual).forward = monitor.forward ∧ (M.observe cfg monitor actual).reverse = .initial := by
  have healthy : (M.observe cfg monitor actual).mode ≠ .invalid := by rw [after]; decide
  obtain ⟨_, supported, passed, checked⟩ := CampusTCPTwoExchangeAccounting.observe_checked cfg monitor actual healthy
  change CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event = true at checked
  have guard : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true := by
    simp only [supported, passed, checked, Bool.and_self]
  rcases CampusTCPTwoExchangeEvidence.needWrite_event mode actual allowed with event | ⟨actor, millis, event⟩
  · obtain ⟨start⟩ := CampusTCPTwoReverseGeometry.start_actual forward endpointReserve gatewayReserve
      lowerNonempty upperNonempty actual before event
    refine ⟨start, ?_, ?_⟩ <;> rw [M.observe, ite_eq_left guard, mode, event] <;> rfl
  · have unchanged : (M.observe cfg monitor actual).mode = .needWrite := by
      rw [M.observe, ite_eq_left guard, mode, event]
      exact mode
    cases unchanged.symm.trans after

end Netlib.Check.CampusTCPTwoExchangeWriteHandoff
