import Netlib.Protocol.ICMPForwardingFacts
import Netlib.Examples.MTUDeployment

/-!
# Transit permission and locally generated errors

Current-session authorization applies to UDP transit. TTL and DF errors arise before
that filter and use independent RELATED output and late policies. Their quotations
restore the checked ingress packet, while outer TTL comes from the supplied return route.
-/

namespace Netlib.Examples.ICMPDeployment

open Packet Protocol

def input (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry := none)
    (linkGroup : Bool := false) : ICMPForwarding.Input :=
  ⟨MTUDeployment.input checked zone candidate, linkGroup⟩

structure ControlFacts (original : UDP.DecodedIPv4) (emission : ICMPForwarding.Emission original) : Prop where
  encoded : IPv4.encode emission.packet = .ok emission.bytes
  decoded : IPv4.decode emission.bytes = .ok ⟨emission.packet, IPv4.computedChecksum emission.packet, []⟩
  control : ICMP.decode emission.packet.payload = .ok ⟨emission.message, ICMP.computedChecksum emission.message⟩
  quoted : IPv4Quote.decode emission.message.quote = .ok emission.quote
  restored : emission.quote.packet = (IPv4Quote.make original emission.length).packet
  header : IPv4Quote.header emission.quote = original.header
  source : emission.packet.source =
    if emission.attachment.entry.changesDestination emission.attachment.direction then original.ip.packet.destination
    else emission.path.source
  destination : emission.packet.destination = original.ip.packet.source
  ttl : emission.packet.ttl = emission.path.ttl
  quotedTTL : emission.quote.packet.ttl = original.ip.packet.ttl
  translatedChecksum : UDP.checksumAccepts emission.destinationTarget.source emission.destinationTarget.destination
    emission.destinationDatagram = true
  translatedPrefix : emission.destinationQuote.packet.payload =
    emission.destinationDatagram.encodeBytes.take (emission.length - 20)
  checksum : emission.quote.checksum = original.ip.checksum ∨
    emission.quote.checksum = 0 ∧ original.ip.checksum = 65535 ∨
    emission.quote.checksum = 65535 ∧ original.ip.checksum = 0
  fits : emission.packet.wireLength ≤ emission.path.mtu.val ∧ emission.packet.wireLength ≤ 576

theorem control_output_facts (active : ICMPForwarding.Pipeline) (tracker : ConntrackLifecycle.State)
    (input : ICMPForwarding.Input) (identification : InternetChecksum.Word)
    (outcome : ICMPForwarding.Outcome input.transit.packet)
    (accepted : ICMPForwarding.step active tracker input identification = .ok outcome)
    (emission : ICMPForwarding.Emission input.transit.packet) (sent : outcome.control.output = some emission) :
    ControlFacts input.transit.packet emission ∧
      ICMPForwarding.GenerationFacts active.control input outcome.transit identification emission := by
  have facts := ICMPForwarding.step_output active tracker input identification outcome accepted emission sent
  have attached : emission.attachment.entry.flow.input emission.attachment.direction = input.transit.packet.header := by
    rw [facts.attachment]
    exact (ICMPForwarding.step_attachment active tracker input identification outcome accepted).2
  have restored := ICMPForwarding.step_quote_restored active tracker input identification outcome accepted emission sent
  have addresses := emission.outer_addresses attached
  refine ⟨⟨emission.encoded, emission.decoded, emission.icmp_decoded, emission.quoted_decoded, restored,
    ?_, addresses.1, addresses.2, rfl, ?_, emission.destinationDatagram_accepts,
    emission.destinationQuote_payload, emission.quote_checksum attached, emission.fits⟩, facts⟩
  · rw [ICMPForwarding.Emission.quote, ICMPNAT.patch_header _ emission.destinationQuote_valid,
      ICMPForwarding.Emission.restoreTarget, attached]
    rfl
  · rw [restored]
    rfl

theorem output_current_permission {context : Context} {session : EAPSession.State}
    {requirements : List Compile.SessionFirewall.Intent}
    (compiled : Compile.SessionFirewall.Certified context session requirements) (safe : session.Safe context)
    (active : ICMPForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry) (linkGroup : Bool)
    (tracker : ConntrackLifecycle.State) (identification : InternetChecksum.Word)
    (outcome : ICMPForwarding.Outcome checked.packet)
    (accepted : ICMPForwarding.step active tracker (input checked zone candidate linkGroup) identification = .ok outcome)
    (emission : MTUForwarding.Emission checked.packet) (forwarded : outcome.transit.output = some emission) :
    MTUDeployment.OutputFacts checked.packet emission ∧ 1 < checked.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ requirements, requirement.test.Holds outcome.transit.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth :=
  MTUDeployment.output_current_permission compiled safe active.forwarding installed checked zone candidate tracker outcome.transit
    (ICMPForwarding.step_transit active tracker (input checked zone candidate linkGroup) identification outcome accepted) emission forwarded

theorem checked_output_current_permission {bundle : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report bundle) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding bundle) (member : finding ∈ report.findings)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry) (linkGroup : Bool)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (mtu : String → MTUForwarding.MTU) (control : ICMPForwarding.Context)
    (tracker : ConntrackLifecycle.State) (identification : InternetChecksum.Word)
    (outcome : ICMPForwarding.Outcome checked.packet)
    (accepted : ICMPForwarding.step
      ⟨⟨SessionFirewallDeployment.snapshotPipeline finding.checkpoint.firewall routes late lateDefault, mtu⟩, control⟩
      tracker (input checked zone candidate linkGroup) identification = .ok outcome)
    (emission : MTUForwarding.Emission checked.packet) (forwarded : outcome.transit.output = some emission) :
    MTUDeployment.OutputFacts checked.packet emission ∧ 1 < checked.packet.ip.packet.ttl.toNat ∧
      ∃ requirement ∈ bundle.requirements, requirement.test.Holds outcome.transit.afterDestination ∧
        Session.Valid bundle.authentication.context
          (Check.SessionFirewall.stateAt bundle.authentication finding.checkpoint.after).session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext bundle.authentication.context)
          (Check.SessionFirewall.stateAt bundle.authentication finding.checkpoint.after).auth :=
  output_current_permission finding.compiled (Check.SessionFirewall.stateAt_safe _ _) _
    (SessionFirewallDeployment.finding_forward_equivalent finding (report.finding_passed compliant finding member)
      routes late lateDefault) checked zone candidate linkGroup tracker identification outcome accepted emission forwarded

theorem postlogoff_transit_none {requirements : List Compile.SessionFirewall.Intent}
    (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (active : ICMPForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry) (linkGroup : Bool)
    (tracker : ConntrackLifecycle.State) (identification : InternetChecksum.Word)
    (outcome : ICMPForwarding.Outcome checked.packet)
    (accepted : ICMPForwarding.step active tracker (input checked zone candidate linkGroup) identification = .ok outcome) :
    outcome.transit.output = none :=
  MTUDeployment.postlogoff_output_none context before safe compiled active.forwarding installed checked zone candidate tracker
    outcome.transit (ICMPForwarding.step_transit active tracker (input checked zone candidate linkGroup) identification outcome accepted)

theorem postlogoff_control_no_scope {requirements : List Compile.SessionFirewall.Intent}
    (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (active : ICMPForwarding.Pipeline)
    (installed : SessionFirewallDeployment.ForwardEquivalent active.forwarding.forwarding compiled)
    (checked : Check.Wire.Checked bytes) (zone : Nat) (candidate : Option NetfilterNAT.Entry) (linkGroup : Bool)
    (tracker : ConntrackLifecycle.State) (identification : InternetChecksum.Word)
    (outcome : ICMPForwarding.Outcome checked.packet)
    (accepted : ICMPForwarding.step active tracker (input checked zone candidate linkGroup) identification = .ok outcome)
    (emission : ICMPForwarding.Emission checked.packet) (sent : outcome.control.output = some emission) :
    ControlFacts checked.packet emission ∧ outcome.transit.output = none ∧
      ∀ scope, ¬Session.Valid context (EAPSession.step context before (.authentication .logoff)).session scope := by
  refine ⟨(control_output_facts active tracker (input checked zone candidate linkGroup) identification outcome
    accepted emission sent).1, postlogoff_transit_none context before safe compiled active installed checked zone
      candidate linkGroup tracker identification outcome accepted, ?_⟩
  intro scope valid
  have denied := EAPSession.unauthorized_denied context (EAPSession.step context before (.authentication .logoff)) scope
    (EAPSession.step_safe context before (.authentication .logoff) safe).2.1 rfl
  have permitted := (Session.permits_iff _ _ _).mpr valid
  simp [denied] at permitted

end Netlib.Examples.ICMPDeployment
