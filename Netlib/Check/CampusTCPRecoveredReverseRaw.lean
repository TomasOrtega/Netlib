import Netlib.Check.CampusTCPRecoveredReverseReserves
import Netlib.Check.CampusTCPRecoveredConfig
import Netlib.Check.CampusTCPRecoveredWindows

/-!
# Reverse reserves from the original configuration

The raw byte bounds imply both reverse reserve records at the same actual
prepared cut. No current window or epoch certificate is supplied.
-/

namespace Netlib.Check.CampusTCPRecoveredReverseReserves

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {lower upper reverseLower reverseUpper : List UInt8}

structure RawReserves (input : Input) (reverseLower reverseUpper : List UInt8) : Prop where
  pending : (reverseLower ++ reverseUpper).length ≤ input.passive.pendingLimit
  mss : reverseLower.length + reverseUpper.length ≤ Handshake.effectiveMSS input.passive (Handshake.receiveOffer input.active)
  capacity : (reverseLower ++ reverseUpper).length ≤ input.active.capacity

theorem raw_reserves (prior : Prefix input events archive) (reserve : RawReserves input reverseLower reverseUpper) :
    Reserves archive reverseLower reverseUpper := by
  have config := CampusTCPRecoveredConfig.Prefix.configuration prior
  have windows := CampusTCPRecoveredWindows.Prefix.windows prior
  exact {
    pending := by rw [config.serverPending]; exact reserve.pending
    mss := by rw [config.serverMSS]; exact reserve.mss
    window := by rw [windows.2]; simpa only [List.length_append] using reserve.capacity
    capacity := by rw [config.clientCapacity]; exact reserve.capacity }

theorem endpoints_of_raw (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : RawReserves input reverseLower reverseUpper) :
    CampusTCPTwoReverseReserves.Initial built.initial reverseLower reverseUpper :=
  endpoints drained value built (raw_reserves drained.next reserve)

theorem gateway_of_raw (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : RawReserves input reverseLower reverseUpper) :
    CampusTCPTwoReverseGeometry.Initial built.initial reverseLower reverseUpper :=
  gateway drained value built (raw_reserves drained.next reserve)

theorem both_of_raw (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : RawReserves input reverseLower reverseUpper) :
    CampusTCPTwoReverseReserves.Initial built.initial reverseLower reverseUpper ∧
      CampusTCPTwoReverseGeometry.Initial built.initial reverseLower reverseUpper :=
  ⟨endpoints_of_raw drained value built reserve, gateway_of_raw drained value built reserve⟩

end Netlib.Check.CampusTCPRecoveredReverseReserves
