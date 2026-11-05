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
  IO.println "Netlib tests passed."
