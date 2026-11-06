import Netlib.Check.CampusTCPTwoExchangeMonitor
import Netlib.Check.CampusTCPTwoProgressSetup

/-!
# Static exchange inputs

The reverse direction keeps the original native ingress coordinates.
Its initial recovery interval comes from the original receiver.
-/

namespace Netlib.Check.CampusTCPTwoExchangeSetup

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

def config (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (reverseLower reverseUpper : List UInt8) : CampusTCPTwoExchangeMonitor.Config where
  forward := CampusTCPTwoProgressSetup.config initial native quantum allowance
  reverseLower
  reverseUpper
  reverseRTO := initial.receiverState.idle.recovery.rto

end Netlib.Check.CampusTCPTwoExchangeSetup
