import Netlib.Check.CampusTCPRecoveredTwoWriteInitial
import Netlib.Check.CampusTCPRecoveredConfig
import Netlib.Check.CampusTCPRecoveredWindows

/-!
# Two-record setup from original configuration bounds

Record sizes refer to the original storage limits, MSS, and peer capacity.
Actual startup receives supply the archived send window.
-/

namespace Netlib.Check.CampusTCPRecoveredForwardRaw

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPRecoveryStartupCold CampusTCPRecoveryStartupTransport

namespace E
export CampusTCPRecoveredTwoWriteEndpoints (Reserves)
end E

structure RawReserves (input : Input) (lower upper : List UInt8) : Prop where
  lowerNonempty : lower ≠ []
  upperNonempty : upper ≠ []
  pending : (lower ++ upper).length ≤ input.active.pendingLimit
  mss : lower.length + upper.length ≤ Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive)
  capacity : (lower ++ upper).length ≤ input.passive.capacity

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {lower upper : List UInt8}

theorem raw_reserves (prior : Prefix input events archive) (raw : RawReserves input lower upper) :
    E.Reserves archive lower upper := by
  have config := CampusTCPRecoveredConfig.Prefix.configuration prior
  have windows := CampusTCPRecoveredWindows.Prefix.windows prior
  exact {
    lowerNonempty := raw.lowerNonempty
    upperNonempty := raw.upperNonempty
    window := by
      rw [windows.1]
      simpa only [List.length_append] using raw.capacity
    mss := by rw [config.clientMSS]; exact raw.mss
    space := by rw [config.serverCapacity]; exact raw.capacity }

theorem pending_fits (prior : Prefix input events archive) (raw : RawReserves input lower upper) :
    (lower ++ upper).length ≤ archive.client.current.pendingLimit := by
  rw [(CampusTCPRecoveredConfig.Prefix.configuration prior).clientPending]
  exact raw.pending

theorem setup (ready : DrainReady report) (raw : RawReserves input lower upper)
    (cold : ColdProfile report) (primary : PrimaryServices report) :
    ∃ archive, ∃ drained : Drained ready archive, ∃ value : Prepared drained.next (lower ++ upper),
      Nonempty (CampusTCPRecoveredTwoWriteInitial.Built drained value) := by
  obtain ⟨archive, ⟨drained⟩⟩ := drain ready
  obtain ⟨value⟩ := prepare drained (lower ++ upper) (pending_fits drained.next raw)
  exact ⟨archive, drained, value,
    CampusTCPRecoveredTwoWriteInitial.ofPrepared drained value (raw_reserves drained.next raw) cold primary⟩

end Netlib.Check.CampusTCPRecoveredForwardRaw
