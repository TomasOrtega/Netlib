import NetlibTest.Core.Reasoning
import NetlibTest.Check.Compliance
import NetlibTest.Packet
import NetlibTest.Routing
import NetlibTest.ZeroTrust

open Netlib

def main : IO Unit := do
  NetlibTest.Compliance.run
  IO.println "Netlib tests passed."
