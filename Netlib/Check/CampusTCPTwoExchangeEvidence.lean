import Netlib.Check.CampusTCPTwoExchangeSetup
import Netlib.Check.CampusTCPTwoReverseGeometry
import Netlib.Check.CampusTCPTwoProgressProgress

/-!
# Actual phase evidence for one exchange

The reverse leg starts at the stored write after forward completion.
Each local proof keeps its own initial cut and loss allowance.
-/

namespace Netlib.Check.CampusTCPTwoExchangeEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

namespace M
export CampusTCPTwoExchangeMonitor (Monitor Mode)
end M
namespace L
export CampusTCPTwoProgressEvidence (Evidence Complete)
end L
namespace R
export CampusTCPTwoReverseGeometry (Started)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8}

inductive Evidence (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (reverseLower reverseUpper : List UInt8) : Cut input complete → M.Monitor → Type where
  | forward {current : Cut input complete} {monitor : M.Monitor}
      (value : L.Evidence initial native quantum allowance current monitor.forward)
      (mode : monitor.mode = .forward) (active : monitor.forward.mode ≠ .done) :
      Evidence initial native quantum allowance reverseLower reverseUpper current monitor
  | needWrite {current : Cut input complete} {monitor : M.Monitor}
      (value : L.Complete initial native quantum allowance current monitor.forward)
      (mode : monitor.mode = .needWrite) :
      Evidence initial native quantum allowance reverseLower reverseUpper current monitor
  | reverse {current : Cut input complete} {monitor : M.Monitor} {before : Cut input complete}
      (forward : L.Complete initial native quantum allowance before monitor.forward)
      {actual : Step input} (start : R.Started forward reverseLower reverseUpper actual)
      (value : L.Evidence start.reverseInitial start.reverseNative quantum
        (allowance - monitor.forward.drops.length) current monitor.reverse)
      (mode : monitor.mode = .reverse) (active : monitor.reverse.mode ≠ .done) :
      Evidence initial native quantum allowance reverseLower reverseUpper current monitor
  | done {current : Cut input complete} {monitor : M.Monitor} {before : Cut input complete}
      (forward : L.Complete initial native quantum allowance before monitor.forward)
      {actual : Step input} (start : R.Started forward reverseLower reverseUpper actual)
      (value : L.Complete start.reverseInitial start.reverseNative quantum
        (allowance - monitor.forward.drops.length) current monitor.reverse)
      (mode : monitor.mode = .done) :
      Evidence initial native quantum allowance reverseLower reverseUpper current monitor

variable {current : Cut input complete} {monitor : M.Monitor}

def Evidence.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (reverseLower reverseUpper : List UInt8) :
    Evidence initial native quantum allowance reverseLower reverseUpper cut .initial :=
  .forward (CampusTCPTwoProgressEvidence.Evidence.ofInitial initial native quantum allowance) rfl (by decide)

theorem Evidence.healthy (evidence : Evidence initial native quantum allowance reverseLower reverseUpper current monitor) :
    monitor.mode ≠ .invalid := by
  cases evidence with
  | forward _ mode _ | needWrite _ mode | reverse _ _ _ mode _ | done _ _ _ mode => rw [mode]; decide

theorem Evidence.forward_active (evidence : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .forward) : monitor.forward.mode ≠ .done := by
  cases evidence with
  | forward _ _ active => exact active
  | needWrite _ selected | reverse _ _ _ selected _ | done _ _ _ selected => rw [selected] at mode; cases mode

theorem Evidence.reverse_active (evidence : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .reverse) : monitor.reverse.mode ≠ .done := by
  cases evidence with
  | reverse _ _ _ _ active => exact active
  | forward _ selected _ | needWrite _ selected | done _ _ _ selected => rw [selected] at mode; cases mode

end Netlib.Check.CampusTCPTwoExchangeEvidence
