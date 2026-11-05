import Netlib.Check.Wire
import Netlib.Protocol.WireForwarding
import Netlib.Examples.SessionFirewallDeployment

/-!
# Checked bytes, tracked NAT, and current session permission

The input header comes from decoded capture bytes. The forwarding model computes
the post-destination-NAT class, translated output, and decremented TTL.
Tuple ownership, capture attribution, and current firewall installation remain
the session deployment's assumptions.
-/

namespace Netlib.Examples.WireNATDeployment

open Packet Protocol

def input (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry := none) :
    WireForwarding.Input := ⟨zone, checked.packet, candidate⟩

structure OutputFacts (original : UDP.DecodedIPv4) (emission : WireForwarding.Emission original) : Prop where
  decoded : UDP.decodeIPv4 emission.bytes = .ok emission.decoded
  header : emission.decoded.header = emission.target
  payload : emission.decoded.datagram.payload = original.datagram.payload
  ttl : emission.decoded.ip.packet.ttl.toNat = original.ip.packet.ttl.toNat - 1
  metadata : emission.decoded.ip.packet.tos = original.ip.packet.tos ∧
    emission.decoded.ip.packet.identification = original.ip.packet.identification ∧
    emission.decoded.ip.packet.dontFragment = original.ip.packet.dontFragment
  length : emission.bytes.length = emission.decoded.ip.packet.wireLength
  ipv4Checksum : InternetChecksum.valid (IPv4.headerBytes emission.decoded.ip.packet emission.decoded.ip.checksum) = true
  omitted : emission.decoded.datagram.checksum = 0 ↔ original.datagram.checksum = 0
  udpChecksum : original.datagram.checksum ≠ 0 →
    InternetChecksum.valid (UDP.pseudoHeader emission.decoded.ip.packet.source emission.decoded.ip.packet.destination
      emission.decoded.datagram.lengthWord ++ emission.decoded.ip.packet.payload) = true

theorem output_facts (emission : WireForwarding.Emission original) : OutputFacts original emission :=
  ⟨emission.decoded_eq, emission.header, emission.payload, emission.ttl, emission.metadata,
    emission.rewritten.bytes_length, emission.ipv4_checksum, emission.checksum_omitted_iff, emission.udp_checksum⟩

theorem output_current_permission {context : Context} {session : EAPSession.State}
    {requirements : List Compile.SessionFirewall.Intent}
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : ConntrackLifecycle.Pipeline) (installed : SessionFirewallDeployment.ForwardEquivalent active compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (tracker : ConntrackLifecycle.State) (outcome : WireForwarding.Outcome checked.packet)
    (accepted : WireForwarding.step active tracker (input checked zone candidate) = .ok outcome)
    (emission : WireForwarding.Emission checked.packet) (forwarded : outcome.output = some emission) :
    OutputFacts checked.packet emission ∧ 1 < checked.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨model, computed, output, destination, _, _, live⟩ :=
    WireForwarding.step_output active tracker (input checked zone candidate) outcome accepted emission forwarded
  have permission := SessionFirewallDeployment.output_current_permission compiled safe active installed tracker
    (input checked zone candidate).lifecycle model emission.target computed output
  rw [← destination] at permission
  exact ⟨output_facts emission, live, permission⟩

theorem checked_output_current_permission {bundle : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report bundle) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding bundle) (member : finding ∈ report.findings)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (tracker : ConntrackLifecycle.State) (outcome : WireForwarding.Outcome checked.packet)
    (accepted : WireForwarding.step
      (SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes late lateDefault)
      tracker (input checked zone candidate) = .ok outcome)
    (emission : WireForwarding.Emission checked.packet) (forwarded : outcome.output = some emission) :
    OutputFacts checked.packet emission ∧ 1 < checked.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ bundle.requirements, requirement.test.Holds outcome.afterDestination ∧
        Session.Valid bundle.authentication.context
          (Check.SessionFirewall.stateAt bundle.authentication finding.checkpoint.after).session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext bundle.authentication.context)
          (Check.SessionFirewall.stateAt bundle.authentication finding.checkpoint.after).auth :=
  output_current_permission finding.compiled (Check.SessionFirewall.stateAt_safe _ _) _
    (SessionFirewallDeployment.finding_forward_equivalent finding (report.finding_passed compliant finding member)
      routes late lateDefault) checked zone candidate tracker outcome accepted emission forwarded

theorem postlogoff_output_none {requirements : List Compile.SessionFirewall.Intent}
    (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : SessionFirewallDeployment.ForwardEquivalent active compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (tracker : ConntrackLifecycle.State) (outcome : WireForwarding.Outcome checked.packet)
    (accepted : WireForwarding.step active tracker (input checked zone candidate) = .ok outcome) : outcome.output = none := by
  cases forwarded : outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨model, computed, output, _⟩ :=
      WireForwarding.step_output active tracker (input checked zone candidate) outcome accepted emission forwarded
    have denied := SessionFirewallDeployment.postlogoff_output_none context before safe compiled active installed
      tracker (input checked zone candidate).lifecycle model computed
    simp [denied] at output

end Netlib.Examples.WireNATDeployment
