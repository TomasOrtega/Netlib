import Netlib.Protocol.MTUForwarding
import Netlib.Examples.WireNATDeployment

/-!
# Current session permission before fragmentation

Authorization concerns the complete post-DNAT datagram before fragmentation.
The selected effective MTU, exclusive hooks, and capture attribution remain supplied.
-/

namespace Netlib.Examples.MTUDeployment

open Packet Protocol

def input (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry := none) :
    WireForwarding.Input := WireNATDeployment.input checked zone candidate

structure OutputFacts (original : UDP.DecodedIPv4) (emission : MTUForwarding.Emission original) : Prop where
  transit : WireNATDeployment.OutputFacts original emission.transit
  nonempty : emission.fragments.fragments ≠ []
  fits : ∀ part ∈ emission.fragments.fragments, part.packet.wireLength ≤ emission.mtu.val
  payload : emission.fragments.fragments.flatMap (·.packet.payload) = emission.transit.decoded.ip.packet.payload
  transport : UDP.decode emission.transit.decoded.ip.packet.source emission.transit.decoded.ip.packet.destination
    (emission.fragments.fragments.flatMap (·.packet.payload)) = .ok emission.transit.decoded.datagram
  headers : ∀ part ∈ emission.fragments.fragments,
    part.packet.toPacket = { emission.transit.decoded.ip.packet with payload := part.packet.payload }
  reassembled : IPv4Fragmentation.reassemble emission.fragments.fragments = .ok emission.transit.decoded.ip.packet

theorem output_facts (emission : MTUForwarding.Emission original) : OutputFacts original emission :=
  ⟨WireNATDeployment.output_facts emission.transit, emission.nonempty, emission.fits, emission.payload,
    emission.datagram_reassembled, emission.fragment_header, emission.reassembled⟩

theorem output_current_permission {context : Context} {session : EAPSession.State}
    {requirements : List Compile.SessionFirewall.Intent}
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : MTUForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (tracker : ConntrackLifecycle.State) (outcome : MTUForwarding.Outcome checked.packet)
    (accepted : MTUForwarding.step active tracker (input checked zone candidate) = .ok outcome)
    (emission : MTUForwarding.Emission checked.packet) (forwarded : outcome.output = some emission) :
    OutputFacts checked.packet emission ∧ 1 < checked.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨parent, computed, output, destination, _, _, _, _⟩ :=
    MTUForwarding.step_output active tracker (input checked zone candidate) outcome accepted emission forwarded
  have permission := WireNATDeployment.output_current_permission compiled safe active.forwarding installed checked zone candidate
    tracker parent computed emission.transit output
  rw [← destination] at permission
  exact ⟨output_facts emission, permission.2⟩

theorem checked_output_current_permission {bundle : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report bundle) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding bundle) (member : finding ∈ report.findings)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (mtu : String → MTUForwarding.MTU) (tracker : ConntrackLifecycle.State) (outcome : MTUForwarding.Outcome checked.packet)
    (accepted : MTUForwarding.step
      ⟨SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes late lateDefault, mtu⟩
      tracker (input checked zone candidate) = .ok outcome)
    (emission : MTUForwarding.Emission checked.packet) (forwarded : outcome.output = some emission) :
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
    (active : MTUForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (tracker : ConntrackLifecycle.State) (outcome : MTUForwarding.Outcome checked.packet)
    (accepted : MTUForwarding.step active tracker (input checked zone candidate) = .ok outcome) : outcome.output = none := by
  cases forwarded : outcome.output with
  | none => rfl
  | some emission =>
    obtain ⟨parent, computed, output, _⟩ :=
      MTUForwarding.step_output active tracker (input checked zone candidate) outcome accepted emission forwarded
    have denied := WireNATDeployment.postlogoff_output_none context before safe compiled active.forwarding installed
      checked zone candidate tracker parent computed
    simp [denied] at output

end Netlib.Examples.MTUDeployment
