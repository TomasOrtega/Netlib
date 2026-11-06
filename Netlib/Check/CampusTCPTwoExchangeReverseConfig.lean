import Netlib.Check.CampusTCPTwoReverseGeometry
import Netlib.Check.CampusTCPTwoExchangeSetup

/-!
# The same reverse selector configuration

The actual reverse initial state retains the original ingress and recovery interval.
-/

namespace Netlib.Check.CampusTCPTwoExchangeReverseConfig

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoReverseGeometry (Started)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8}
variable {actual : Step input} {forward : Complete initial native quantum allowance current monitor}

theorem config_eq (start : Started forward reverseLower reverseUpper actual) (forwardDrops : Nat) :
    CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum (allowance - forwardDrops) =
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper).reverse forwardDrops := by
  simp only [CampusTCPTwoProgressSetup.config, CampusTCPTwoExchangeSetup.config,
    CampusTCPTwoExchangeMonitor.Config.reverse, CampusTCPTwoExchangeMonitor.Config.reverseBytes,
    start.reverse_ingress, start.reverse_rto]

end Netlib.Check.CampusTCPTwoExchangeReverseConfig
