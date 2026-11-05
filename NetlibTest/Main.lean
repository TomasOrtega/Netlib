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
import NetlibTest.CampusEAP
import NetlibTest.EAPDeployment

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
  IO.println "Netlib tests passed."
