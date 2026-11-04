import Netlib.Protocol.Conntrack

namespace NetlibTest.Conntrack

open Netlib.Packet
open Netlib.Protocol.Conntrack

private def packet : Header := ⟨167772161, 3325256705, Protocol.udp, 40000, 53⟩

private def opened : State := (step {} (.outbound packet true 10)).state

example : (step {} (.outbound packet true 10)).output = some packet := by decide
example : (step {} (.outbound packet false 10)).output = none := by decide
example : (step {} (.outbound packet true 0)).output = none := by decide
example : (step opened (.inbound packet.reverse)).output = some packet.reverse := by decide
example : (step opened (.inbound { packet.reverse with sourcePort := 54 })).output = none := by decide
example : (step (step opened (.advance 10)).state (.inbound packet.reverse)).output = none := by decide
example : (step (step opened (.close packet)).state (.inbound packet.reverse)).output = none := by decide

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (permitsReply opened packet.reverse) "An installed live grant must permit its exact reverse."
  for changed in [{ packet.reverse with source := 3325256706 },
    { packet.reverse with sourcePort := 54 }, { packet.reverse with destinationPort := 40001 },
    { packet.reverse with protocol := Protocol.tcp }] do
    ensure (!(permitsReply opened changed)) "Changing any return-flow field must invalidate the grant."
  ensure (decide ((step opened (.outbound packet false 20)).state = opened))
    "A denied outbound request must not refresh its grant."
  ensure ((step {} (.outbound { packet with protocol := Protocol.icmp } true 10)).output.isNone)
    "The five-tuple model must reject unsupported transports."
  let expired := (step opened (.advance 10)).state
  ensure (expired.entries.isEmpty && !(permitsReply expired packet.reverse))
    "The expiration boundary must remove the grant."
  let backward := (step expired (.advance 2)).state
  ensure (backward.now == 10 && backward.entries.isEmpty) "Backward time must not revive grants."
  ensure (!(permitsReply (close opened packet) packet.reverse)) "Closing a flow must revoke its exact reverse."
  ensure ((flush opened).entries.isEmpty) "Flushing must remove every grant."
  let refreshed := (step opened (.outbound packet true 20)).state
  ensure (refreshed.entries.length == 1 && permitsReply (advance refreshed 15) packet.reverse)
    "A repeated authorized flow must replace its previous deadline."
  IO.println "Conntrack tests passed."

end NetlibTest.Conntrack
