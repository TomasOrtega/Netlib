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

open Netlib

def main : IO Unit := do
  NetlibTest.Compliance.run
  NetlibTest.DataPlane.run
  NetlibTest.Wifi.run
  NetlibTest.FiveG.run
  NetlibTest.Solver.run
  NetlibTest.Analysis.run
  NetlibTest.LargePolicy.run
  IO.println "Netlib tests passed."
