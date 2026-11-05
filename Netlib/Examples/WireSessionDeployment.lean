import Netlib.Check.Wire
import Netlib.Examples.SessionFirewallDeployment

/-!
# Decoded packets and current session policy

The byte capture must describe the lifecycle's forward-stage header after destination NAT.
The session deployment still supplies tuple ownership and current installation assumptions.
Checksum validation is arithmetic evidence; a zero UDP checksum remains omitted.
-/

namespace Netlib.Examples.WireSessionDeployment

open Packet Protocol

def reencode (checked : Check.Wire.Checked bytes) : Except String (List UInt8) := checked.encode

theorem reencode_exact (checked : Check.Wire.Checked bytes) : reencode checked = .ok bytes := checked.encode_eq

theorem header_fields (checked : Check.Wire.Checked bytes) :
    checked.header = ⟨checked.packet.ip.packet.source, checked.packet.ip.packet.destination,
      checked.packet.ip.packet.protocol, checked.packet.datagram.sourcePort, checked.packet.datagram.destinationPort⟩ :=
  checked.header_fields

theorem payload_bytes (checked : Check.Wire.Checked bytes) :
    UDP.encode checked.packet.ip.packet.source checked.packet.ip.packet.destination checked.packet.datagram =
      .ok checked.packet.ip.packet.payload :=
  UDP.encode_decode _ _ _ _ (UDP.decodeIPv4_layers _ _ checked.transport).2.2

theorem ipv4_checksum (checked : Check.Wire.Checked bytes) :
    InternetChecksum.valid (IPv4.headerBytes checked.packet.ip.packet checked.packet.ip.checksum) = true :=
  (IPv4.decode_valid _ _ (UDP.decodeIPv4_layers _ _ checked.transport).1).2

theorem udp_checksum (checked : Check.Wire.Checked bytes) (present : checked.packet.datagram.checksum ≠ 0) :
    InternetChecksum.valid (UDP.pseudoHeader checked.packet.ip.packet.source checked.packet.ip.packet.destination
      checked.packet.datagram.lengthWord ++ checked.packet.ip.packet.payload) = true :=
  checked.udp_checksum_verified present

theorem checked_output_current_permission {input : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report input) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding input) (member : finding ∈ report.findings)
    (checked : Check.Wire.Checked bytes)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (tracker : ConntrackLifecycle.State) (packet : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step
      (SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes late lateDefault)
      tracker packet = .ok outcome) (forwarded : outcome.output = some wire)
    (stage : outcome.afterDestination = checked.header) :
    UDP.encode checked.packet.ip.packet.source checked.packet.ip.packet.destination checked.packet.datagram =
        .ok checked.packet.ip.packet.payload ∧
      ∃ requirement ∈ input.requirements, requirement.test.Holds checked.header ∧
        Session.Valid input.authentication.context
          (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
          (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).auth := by
  refine ⟨payload_bytes checked, ?_⟩
  have permission := SessionFirewallDeployment.checked_output_current_permission report compliant finding member
    routes late lateDefault tracker packet outcome wire accepted forwarded
  simpa only [stage] using permission

theorem checked_matching_scope_valid {input : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report input) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding input) (member : finding ∈ report.findings)
    (checked : Check.Wire.Checked bytes)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (tracker : ConntrackLifecycle.State) (packet : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step
      (SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes late lateDefault)
      tracker packet = .ok outcome) (forwarded : outcome.output = some wire)
    (stage : outcome.afterDestination = checked.header)
    (requirement : Compile.SessionFirewall.Intent) (belongs : requirement ∈ input.requirements)
    (matched : requirement.test.Holds checked.header) :
    Session.Valid input.authentication.context
        (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).auth := by
  apply SessionFirewallDeployment.output_matching_scope_valid finding.compiled
    (Check.SessionFirewall.stateAt_safe _ _) _
    (SessionFirewallDeployment.finding_forward_equivalent finding (report.finding_passed compliant finding member)
      routes late lateDefault) tracker packet outcome wire accepted forwarded requirement belongs
  simpa only [stage] using matched

end Netlib.Examples.WireSessionDeployment
