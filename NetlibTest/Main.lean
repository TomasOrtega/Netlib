import NetlibTest.Core.Reasoning
import NetlibTest.Check.Compliance
import NetlibTest.Packet
import NetlibTest.Routing
import NetlibTest.ZeroTrust
import NetlibTest.DataPlane
import NetlibTest.Wifi
import NetlibTest.FiveG
import NetlibTest.FiveGAudit
import NetlibTest.Solver
import NetlibTest.LargePolicy
import NetlibTest.NetworkLaws
import NetlibTest.PacketPartition
import NetlibTest.Contracts
import NetlibTest.Transition
import NetlibTest.Campus
import NetlibTest.Traffic
import NetlibTest.StandardsComposition
import NetlibTest.Queue
import NetlibTest.ImportJson
import NetlibTest.ImportIPv4
import NetlibTest.Nftables
import NetlibTest.LinuxRoute
import NetlibTest.LinuxDeployment
import NetlibTest.ACLCompiler
import NetlibTest.NftablesCompiler
import NetlibTest.Rewrite
import NetlibTest.Conntrack
import NetlibTest.NAT
import NetlibTest.NATReuse
import NetlibTest.Transfer
import NetlibTest.NATTrace
import NetlibTest.PacketFields
import NetlibTest.Processor
import NetlibTest.Stateful
import NetlibTest.StatefulTrace
import NetlibTest.NATPipeline
import NetlibTest.CampusNAT
import NetlibTest.FlowNAT
import NetlibTest.NetfilterNAT
import NetlibTest.ConntrackImport
import NetlibTest.ConntrackNetlink
import NetlibTest.ConntrackAudit
import NetlibTest.StatefulACL
import NetlibTest.ConntrackLifecycle
import NetlibTest.NftablesStateful
import NetlibTest.NftablesNAT
import NetlibTest.StatefulRefinement
import NetlibTest.ConntrackLifecycleAudit
import NetlibTest.StatefulExclusion
import NetlibTest.Revocation
import NetlibTest.ConntrackRevocation
import NetlibTest.QueueDrain
import NetlibTest.BufferedLifecycle
import NetlibTest.BufferedReplay
import NetlibTest.EAP
import NetlibTest.EAPOL
import NetlibTest.EAPAuth
import NetlibTest.EAPSession
import NetlibTest.EAPCheck
import NetlibTest.SessionFirewall
import NetlibTest.SessionFirewallCheck
import NetlibTest.SessionFirewallDeployment
import NetlibTest.InternetChecksum
import NetlibTest.IPv4
import NetlibTest.UDP
import NetlibTest.EthernetIPv4
import NetlibTest.WireCheck
import NetlibTest.WireSessionDeployment
import NetlibTest.UDPRewrite
import NetlibTest.WireForwarding
import NetlibTest.WireForwardingCheck
import NetlibTest.Replay
import NetlibTest.IPv4Fragment
import NetlibTest.IPv4Fragmentation
import NetlibTest.MTUForwarding
import NetlibTest.MTUForwardingCheck
import NetlibTest.MTUDeployment
import NetlibTest.ChecksumRewrite
import NetlibTest.IPv4Quote
import NetlibTest.ICMP
import NetlibTest.ICMPNAT
import NetlibTest.ICMPForwarding
import NetlibTest.ICMPError
import NetlibTest.ICMPForwardingCheck
import NetlibTest.ICMPDeployment
import NetlibTest.IPv4QuotePrefix
import NetlibTest.ChecksumRewriteRaw
import NetlibTest.ICMPPrefixNAT
import NetlibTest.RelatedICMP
import NetlibTest.PMTU
import NetlibTest.RelatedICMPCheck
import NetlibTest.PMTUCheck
import NetlibTest.PMTUDeployment
import NetlibTest.IPv4InputFragment
import NetlibTest.IPv4Reassembly
import NetlibTest.IPv4ReassemblyTimeout
import NetlibTest.IPv4Refragmentation
import NetlibTest.ReassemblyForwarding
import NetlibTest.ReassemblyForwardingCheck
import NetlibTest.ReassemblyDeployment
import NetlibTest.ICMPControl
import NetlibTest.NftablesICMPControl
import NetlibTest.ReassemblyTimeoutCheck
import NetlibTest.WireNATDeployment
import NetlibTest.CampusEAP
import NetlibTest.IngressAttachment
import NetlibTest.IngressAttachmentCompiler
import NetlibTest.NftablesIngress
import NetlibTest.GuardedHandoff
import NetlibTest.IngressProbe
import NetlibTest.AttachmentCampus
import NetlibTest.IPv4Envelope
import NetlibTest.FragmentAttachment
import NetlibTest.FragmentAdmission
import NetlibTest.NftablesPredefrag
import NetlibTest.FragmentAdmissionCheck
import NetlibTest.TCPOptions
import NetlibTest.TCPSegment
import NetlibTest.TCPSequenceSpace
import NetlibTest.TCPIPv4
import NetlibTest.TCPRewrite
import NetlibTest.TCPReassembly
import NetlibTest.TCPReceiveWindow
import NetlibTest.TCPEstablishedReceive
import NetlibTest.TCPReceiveCheck
import NetlibTest.TCPOutput
import NetlibTest.TCPEndpoint
import NetlibTest.TCPEndpointCheck
import NetlibTest.TCPApplicationTrace
import NetlibTest.TCPHandshake
import NetlibTest.TCPMSS
import NetlibTest.TCPMSSCampus
import NetlibTest.TCPRecovery
import NetlibTest.TCPRecoveryEndpoint
import NetlibTest.TCPRecoveryCampus
import NetlibTest.TCPHandshakeExchange
import NetlibTest.TCPHandshakeCheck
import NetlibTest.TCPWireForwarding
import NetlibTest.TCPAdmission
import NetlibTest.TCPCheckpoint
import NetlibTest.CampusTCPService
import NetlibTest.CampusTCP
import NetlibTest.CampusTCPTransfer
import NetlibTest.EAPDeployment

import NetlibTest.ConntrackReplication
import NetlibTest.StatefulFailover

import NetlibTest.TrackedFlow
import NetlibTest.Outstanding

import NetlibTest.SafeHandoff
import NetlibTest.SafeHandoffDeployment
import NetlibTest.CampusWithdrawal
import NetlibTest.CampusDuplex
import NetlibTest.CampusDirect

open Netlib

def main : IO Unit := do
  NetlibTest.Compliance.run
  NetlibTest.DataPlane.run
  NetlibTest.Wifi.run
  NetlibTest.FiveG.run
  NetlibTest.Solver.run
  NetlibTest.Analysis.run
  NetlibTest.LargePolicy.run
  NetlibTest.NetworkLaws.run
  NetlibTest.PacketPartition.run
  NetlibTest.Transition.run
  NetlibTest.Campus.run
  NetlibTest.Traffic.run
  NetlibTest.StandardsComposition.run
  NetlibTest.Queue.run
  NetlibTest.ImportJson.run
  NetlibTest.ImportIPv4.run
  NetlibTest.Nftables.run
  NetlibTest.LinuxRoute.run
  NetlibTest.LinuxDeployment.run
  NetlibTest.ACLCompiler.run
  NetlibTest.NftablesCompiler.run
  NetlibTest.Rewrite.run
  NetlibTest.Conntrack.run
  NetlibTest.NAT.run
  NetlibTest.NATReuse.run
  NetlibTest.Transfer.run
  NetlibTest.NATTrace.run
  NetlibTest.PacketFields.run
  NetlibTest.Processor.run
  NetlibTest.Stateful.run
  NetlibTest.StatefulTrace.run
  NetlibTest.NATPipeline.run
  NetlibTest.CampusNAT.run
  NetlibTest.FlowNAT.run
  NetlibTest.NetfilterNAT.run
  NetlibTest.ConntrackImport.run
  NetlibTest.ConntrackNetlink.run
  NetlibTest.ConntrackAudit.run
  NetlibTest.StatefulACL.run
  NetlibTest.ConntrackLifecycle.run
  NetlibTest.NftablesStateful.run
  NetlibTest.NftablesNAT.run
  NetlibTest.StatefulRefinement.run
  NetlibTest.ConntrackLifecycleAudit.run
  NetlibTest.StatefulExclusion.run
  NetlibTest.Revocation.run
  NetlibTest.ConntrackRevocation.run
  NetlibTest.QueueDrain.run
  NetlibTest.BufferedLifecycle.run
  NetlibTest.BufferedReplay.run
  NetlibTest.EAP.run
  NetlibTest.EAPOL.run
  NetlibTest.EAPAuth.run
  NetlibTest.EAPSession.run
  NetlibTest.EAPCheck.run
  NetlibTest.CampusEAP.run
  NetlibTest.EAPDeployment.run
  NetlibTest.SessionFirewall.run
  NetlibTest.SessionFirewallCheck.run
  NetlibTest.SessionFirewallDeployment.run
  NetlibTest.InternetChecksum.run
  NetlibTest.IPv4.run
  NetlibTest.UDP.run
  NetlibTest.EthernetIPv4.run
  NetlibTest.WireCheck.run
  NetlibTest.WireSessionDeployment.run
  NetlibTest.UDPRewrite.run
  NetlibTest.WireForwarding.run
  NetlibTest.WireForwardingCheck.run
  NetlibTest.Replay.run
  NetlibTest.IPv4Fragment.run
  NetlibTest.IPv4Fragmentation.run
  NetlibTest.MTUForwarding.run
  NetlibTest.MTUForwardingCheck.run
  NetlibTest.MTUDeployment.run
  NetlibTest.ChecksumRewrite.run
  NetlibTest.IPv4Quote.run
  NetlibTest.ICMP.run
  NetlibTest.ICMPNAT.run
  NetlibTest.ICMPForwarding.run
  NetlibTest.ICMPError.run
  NetlibTest.ICMPForwardingCheck.run
  NetlibTest.ICMPDeployment.run
  NetlibTest.IPv4QuotePrefix.run
  NetlibTest.ChecksumRewriteRaw.run
  NetlibTest.ICMPPrefixNAT.run
  NetlibTest.RelatedICMP.tests
  NetlibTest.PMTU.run
  NetlibTest.RelatedICMPCheck.run
  NetlibTest.PMTUCheck.run
  NetlibTest.PMTUDeployment.run
  NetlibTest.IPv4InputFragment.run
  NetlibTest.IPv4Reassembly.run
  NetlibTest.IPv4ReassemblyTimeout.run
  NetlibTest.IPv4Refragmentation.run
  NetlibTest.ReassemblyForwarding.run
  NetlibTest.ReassemblyForwardingCheck.run
  NetlibTest.ReassemblyDeployment.run
  NetlibTest.ICMPControl.run
  NetlibTest.NftablesICMPControl.run
  NetlibTest.ReassemblyTimeoutCheck.run
  NetlibTest.WireNATDeployment.run
  NetlibTest.ConntrackReplication.run
  NetlibTest.StatefulFailover.run
  NetlibTest.TrackedFlow.run
  NetlibTest.Outstanding.run
  NetlibTest.SafeHandoff.run
  NetlibTest.SafeHandoffDeployment.run
  NetlibTest.CampusWithdrawal.run
  NetlibTest.CampusDuplex.run
  NetlibTest.CampusDirect.run
  NetlibTest.IngressAttachment.run
  NetlibTest.IngressAttachmentCompiler.run
  NetlibTest.NftablesIngress.run
  NetlibTest.GuardedHandoff.run
  NetlibTest.IngressProbe.run
  NetlibTest.AttachmentCampus.run
  NetlibTest.IPv4Envelope.run
  NetlibTest.FragmentAttachment.run
  NetlibTest.FragmentAdmission.run
  NetlibTest.NftablesPredefrag.run
  NetlibTest.FragmentAdmissionCheck.run
  NetlibTest.TCPOptions.run
  NetlibTest.TCPSegment.run
  NetlibTest.TCPSequenceSpace.run
  NetlibTest.TCPIPv4.run
  NetlibTest.TCPRewrite.run
  NetlibTest.TCPReassembly.run
  NetlibTest.TCPReceiveWindow.run
  NetlibTest.TCPEstablishedReceive.run
  NetlibTest.TCPReceiveCheck.run
  NetlibTest.TCPOutput.run
  NetlibTest.TCPEndpoint.run
  NetlibTest.TCPEndpointCheck.run
  NetlibTest.TCPHandshake.run
  NetlibTest.TCPMSS.run
  NetlibTest.TCPMSSCampus.run
  NetlibTest.TCPRecovery.run
  NetlibTest.TCPRecoveryEndpoint.run
  NetlibTest.TCPRecoveryCampus.run
  NetlibTest.TCPHandshakeCheck.run
  NetlibTest.TCPWireForwarding.run
  NetlibTest.TCPAdmission.run
  NetlibTest.TCPCheckpoint.run
  NetlibTest.CampusTCPService.run
  NetlibTest.CampusTCP.run
  NetlibTest.CampusTCPTransfer.run
  IO.println "Netlib tests passed."
