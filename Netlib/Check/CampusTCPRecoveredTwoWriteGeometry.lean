import Netlib.Check.CampusTCPRecoveredTwoWriteEndpoints
import Netlib.Check.CampusTCPRecoveryStartupGeometry

/-!
# Current two-record geometry after recovered startup

The actual endpoint cores and empty-byte gateway lanes share the same cursors.
Window marker fields remain unchanged.
-/

namespace Netlib.Check.CampusTCPRecoveredTwoWriteGeometry

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPTwoProgressStart
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut Reserves)
end E

variable {input : Input} {events : List Event} {report : Report input events}
variable {archive : RecoveryArchive input.active input.passive} {ready : DrainReady report}
variable {lower upper : List UInt8}

private theorem client_core (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    (endpoint (E.cut value).endpoints .client).core = archive.complete.certificate.activeSeed.core :=
  (prepared_geometry drained value).1.trans drained.next.archive_clean.1.1.core

private theorem server_core (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    (endpoint (E.cut value).endpoints .server).core = archive.complete.certificate.passiveSeed.core :=
  (prepared_geometry drained value).2.1.trans drained.next.archive_clean.2.1.core

def geometry (drained : Drained ready archive) (value : Prepared drained.next (lower ++ upper))
    (reserves : E.Reserves archive lower upper)
    {basis : StartupBasis (E.cut value)} {location : Gateway}
    (gateway : GatewayStart (E.cut value) basis location)
    (shape : CampusTCPRecoveryStartupGeometry.Geometry input.active input.passive gateway.session) :
    Geometry gateway .client lower upper := by
  have sequences := archive.complete.certificate.initial_sequences
  have clientSend : (endpoint (E.cut value).endpoints .client).core.sendNext = input.active.iss.add 1 := by
    rw [client_core drained value]
    simpa only [archive.complete.activeConfig] using sequences.2.1
  have clientReceive : (endpoint (E.cut value).endpoints .client).core.receiveNext = input.passive.iss.add 1 := by
    rw [client_core drained value]
    simpa only [archive.complete.passiveConfig] using sequences.2.2.1
  have serverSend : (endpoint (E.cut value).endpoints .server).core.sendNext = input.passive.iss.add 1 := by
    rw [server_core drained value]
    simpa only [archive.complete.passiveConfig] using sequences.2.2.2.2.1
  have serverReceive : (endpoint (E.cut value).endpoints .server).core.receiveNext = input.active.iss.add 1 := by
    rw [server_core drained value]
    simpa only [archive.complete.activeConfig] using sequences.2.2.2.2.2
  refine ⟨0, shape.original.acknowledged, shape.original.observed, shape.original.highEnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change _ = gateway.session.original.base.add 0
    rw [shape.original.baseEq, Seq.add_zero]
    exact clientSend
  · exact serverReceive.trans clientSend.symm
  · change _ = gateway.session.reply.base.add gateway.session.reply.observed
    rw [shape.reply.baseEq, shape.reply.observed, Seq.add_zero]
    exact clientReceive
  · change _ = gateway.session.reply.base.add gateway.session.reply.highEnd
    rw [shape.reply.baseEq, shape.reply.highEnd, Seq.add_zero]
    exact serverSend
  · exact shape.reply.observed.trans shape.reply.highEnd.symm
  · change lower.length + upper.length ≤ gateway.session.original.peerWindow.val
    rw [shape.original.window]
    have capacity : archive.server.current.core.capacity = input.passive.capacity := by
      rw [drained.next.archive_clean.2.1.core]
      simpa only [archive.complete.passiveConfig] using archive.complete.certificate.configuration.2.2.2.1
    have space := reserves.space
    rw [capacity, List.length_append] at space
    exact space
  · have mss := reserves.mss
    have fits := archive.client.valid.2.2.2.2.2.1
    have limit := archive.client.valid.2.2.2.2.2.2
    change 0 + lower.length + upper.length + 2 < Seq.halfSpace
    unfold Seq.halfSpace
    omega

end Netlib.Check.CampusTCPRecoveredTwoWriteGeometry
