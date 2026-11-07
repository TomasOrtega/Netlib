import Netlib.Check.CampusTCPRecoveredSetup

/-!
# Configuration fields in the actual startup archive

Early empty ACKs retain storage limits, effective MSS values, and capacities.
-/

namespace Netlib.Check.CampusTCPRecoveredConfig

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup

structure Configuration (input : Input) (archive : RecoveryArchive input.active input.passive) : Prop where
  clientPending : archive.client.current.pendingLimit = input.active.pendingLimit
  serverPending : archive.server.current.pendingLimit = input.passive.pendingLimit
  clientMSS : archive.client.current.effectiveMSS = Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive)
  serverMSS : archive.server.current.effectiveMSS = Handshake.effectiveMSS input.passive (Handshake.receiveOffer input.active)
  clientCapacity : archive.client.current.core.capacity = input.active.capacity
  serverCapacity : archive.server.current.core.capacity = input.passive.capacity

private theorem frame_pending (frame : TCPHandshakeRecovery.WindowFrame before after) : after.pendingLimit = before.pendingLimit := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

private theorem frame_mss (frame : TCPHandshakeRecovery.WindowFrame before after) : after.effectiveMSS = before.effectiveMSS := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem Prefix.configuration (prior : Prefix input events archive) : Configuration input archive := by
  have clean := prior.archive_clean
  have config := archive.complete.certificate.configuration
  have mss := archive.complete.certificate.directional_mss
  exact {
    clientPending := (frame_pending clean.1.1).trans (by
      simpa only [archive.complete.activeConfig] using config.2.1)
    serverPending := (frame_pending clean.2.1).trans (by
      simpa only [archive.complete.passiveConfig] using config.2.2.2.2.1)
    clientMSS := (frame_mss clean.1.1).trans (by
      simpa only [archive.complete.activeConfig, archive.complete.passiveConfig] using mss.2.2.1)
    serverMSS := (frame_mss clean.2.1).trans (by
      simpa only [archive.complete.activeConfig, archive.complete.passiveConfig] using mss.2.2.2)
    clientCapacity := (congrArg (fun core => core.capacity) clean.1.1.core).trans (by
      simpa only [archive.complete.activeConfig] using config.1)
    serverCapacity := (congrArg (fun core => core.capacity) clean.2.1.core).trans (by
      simpa only [archive.complete.passiveConfig] using config.2.2.2.1) }

end Netlib.Check.CampusTCPRecoveredConfig
