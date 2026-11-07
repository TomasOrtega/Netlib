import Netlib.Check.CampusTCPRecoveredTwoWriteInitial
import Netlib.Check.CampusTCPTwoReverseReserves
import Netlib.Check.CampusTCPTwoReverseGeometry

/-!
# Reverse reserves at the actual recovered write cut

These intermediate numeric bounds refer to the retained startup archive.
The endpoint and gateway reserve records follow the same actual preparation.
-/

namespace Netlib.Check.CampusTCPRecoveredReverseReserves

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend

namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E

namespace I
export CampusTCPRecoveredTwoWriteInitial (Built)
end I

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {lower upper reverseLower reverseUpper : List UInt8}

structure Reserves (archive : RecoveryArchive input.active input.passive) (reverseLower reverseUpper : List UInt8) : Prop where
  pending : (reverseLower ++ reverseUpper).length ≤ archive.server.current.pendingLimit
  mss : reverseLower.length + reverseUpper.length ≤ archive.server.current.effectiveMSS
  window : reverseLower.length + reverseUpper.length ≤ archive.server.current.sendWindow
  capacity : (reverseLower ++ reverseUpper).length ≤ archive.client.current.core.capacity

private theorem client_start (drained : Drained ready archive) :
    endpoint drained.next.endpoints .client = archive.client.current := drained.cursors.1

private theorem server_start (drained : Drained ready archive) :
    endpoint drained.next.endpoints .server = archive.server.current := drained.cursors.2.1

theorem endpoints (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : Reserves archive reverseLower reverseUpper) :
    CampusTCPTwoReverseReserves.Initial built.initial reverseLower reverseUpper where
  unread := by
    change (endpoint value.next.endpoints .client).core.received = []
    rw [(prepared_geometry drained value).1]
    exact drained.next.archive_clean.1.fields.2.2.2.2.2.1
  pending := by
    change (reverseLower ++ reverseUpper).length ≤ (endpoint value.next.endpoints .server).pendingLimit
    rw [value.server_state, server_start drained]
    exact reserve.pending
  mss := by
    change reverseLower.length + reverseUpper.length ≤ (endpoint value.next.endpoints .server).effectiveMSS
    rw [value.server_state, server_start drained]
    exact reserve.mss
  window := by
    change reverseLower.length + reverseUpper.length ≤ (endpoint value.next.endpoints .server).sendWindow
    rw [value.server_state, server_start drained]
    exact reserve.window
  receive := by
    change (reverseLower ++ reverseUpper).length ≤ Endpoint.offeredWindow (endpoint value.next.endpoints .client)
    rw [value.client_state, client_start drained]
    exact reserve.capacity

theorem gateway (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : Reserves archive reverseLower reverseUpper) :
    CampusTCPTwoReverseGeometry.Initial built.initial reverseLower reverseUpper where
  window := by
    change reverseLower.length + reverseUpper.length ≤ built.initial.gatewayState.session.reply.peerWindow.val
    rw [built.gatewayShape.reply.window]
    have capacity : archive.client.current.core.capacity = input.active.capacity := by
      rw [drained.next.archive_clean.1.1.core]
      simpa only [archive.complete.activeConfig] using archive.complete.certificate.configuration.1
    have bound := reserve.capacity
    rw [capacity, List.length_append] at bound
    exact bound
  epoch := by
    have empty : CampusTCPTwoReverseGeometry.reversePrefix built.initial = 0 := built.gatewayShape.reply.observed
    have pending := reserve.pending
    have bounded := archive.server.valid.2.2.1
    change CampusTCPTwoReverseGeometry.reversePrefix built.initial + reverseLower.length + reverseUpper.length + 2 < Seq.halfSpace
    rw [empty]
    simp only [List.length_append] at pending
    unfold Seq.halfSpace
    omega

theorem both (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (built : I.Built drained value) (reserve : Reserves archive reverseLower reverseUpper) :
    CampusTCPTwoReverseReserves.Initial built.initial reverseLower reverseUpper ∧
      CampusTCPTwoReverseGeometry.Initial built.initial reverseLower reverseUpper :=
  ⟨endpoints drained value built reserve, gateway drained value built reserve⟩

end Netlib.Check.CampusTCPRecoveredReverseReserves
