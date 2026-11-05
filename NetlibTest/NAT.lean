import Netlib.Protocol.NAT

namespace NetlibTest.NAT

open Netlib.Packet
open Netlib.Protocol.NAT

private def packet : Header := ⟨167772161, 3325256705, Protocol.tcp, 40000, 443⟩
private def allocation : Endpoint := ⟨3405803777, 62000⟩
private def otherAllocation : Endpoint := ⟨3405803777, 62001⟩
private def wire : Header := (Rewrite.sourceEndpoint allocation).apply packet
private def opened : State := (step State.initial (.outbound packet allocation true 10)).state

example : (step State.initial (.outbound packet allocation true 10)).output = some wire := by decide
example : (step opened (.inbound wire.reverse)).output = some packet.reverse := by decide
example : (step opened (.inbound { wire.reverse with sourcePort := 444 })).output = none := by decide
example : (step opened (.outbound { packet with source := 167772162 } allocation true 10)).output = none := by decide
example : (step opened (.outbound packet otherAllocation true 10)).output = none := by decide

example (events : List Event) : (Netlib.Protocol.NAT.run State.initial events).Safe :=
  run_safe _ _ initial_safe

example (state : State) (output : Header)
    (accepted : (step state (.outbound packet allocation true 10)).output = some output) :
    (step (step state (.outbound packet allocation true 10)).state (.inbound output.reverse)).output =
      some packet.reverse := accepted_roundtrip _ _ _ _ _ _ accepted

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (decide ((step State.initial (.outbound packet allocation true 10)).output = some wire))
    "An outbound flow must rewrite its complete source endpoint."
  ensure (decide ((step opened (.inbound wire.reverse)).output = some packet.reverse))
    "The exact return flow must restore the complete private endpoint."
  for changed in [{ wire.reverse with source := 3325256706 },
    { wire.reverse with sourcePort := 444 }, { wire.reverse with destination := 3405803778 },
    { wire.reverse with destinationPort := 62001 }, { wire.reverse with protocol := Protocol.udp }] do
    let result := step opened (.inbound changed)
    ensure (result.output.isNone && decide (result.state = opened))
      "An unsolicited return flow must not produce output or change state."
  let collision := step opened (.outbound { packet with source := 167772162 } allocation true 10)
  ensure (collision.output.isNone && decide (collision.state = opened))
    "A public endpoint collision must reject the allocation without changing state."
  let denied := step opened (.outbound packet allocation false 100)
  ensure (denied.output.isNone && decide (denied.state = opened))
    "Denied traffic must not refresh a mapping or a grant."
  let remapped := step opened (.outbound packet otherAllocation true 20)
  ensure (remapped.output.isNone && decide (remapped.state = opened))
    "An existing internal endpoint must retain its public mapping."
  let peer : Header := { packet with destination := 3325256706, destinationPort := 80 }
  let reused := step opened (.outbound peer allocation true 20)
  ensure (reused.output.isSome && reused.state.bindings.length == 1 && reused.state.tracking.entries.length == 2)
    "Remote peers must share the endpoint mapping while retaining separate grants."
  let peerWire := (Rewrite.sourceEndpoint allocation).apply peer
  ensure (decide ((step reused.state (.inbound peerWire.reverse)).output = some peer.reverse) &&
    decide ((step reused.state (.inbound wire.reverse)).output = some packet.reverse))
    "Each authorized remote peer must retain its own exact return-flow grant."
  let atTen := (step reused.state (.advance 10)).state
  ensure (atTen.bindings.length == 1 && atTen.tracking.entries.length == 1 &&
    (step atTen (.inbound wire.reverse)).output.isNone &&
    (step atTen (.inbound peerWire.reverse)).output.isSome)
    "A live mapping must not preserve an expired remote-peer grant."
  let closed := (step reused.state (.close packet)).state
  ensure (closed.bindings.length == 1 && (step closed (.inbound wire.reverse)).output.isNone &&
    (step closed (.inbound peerWire.reverse)).output.isSome)
    "Closing one flow must revoke its grant while retaining the mapping and other grants."
  let expired := (step reused.state (.advance 20)).state
  ensure (expired.bindings.isEmpty && expired.tracking.entries.isEmpty)
    "The final expiration boundary must purge mappings and grants."
  let backward := (step expired (.advance 1)).state
  ensure (backward.tracking.now == 20 && backward.bindings.isEmpty)
    "Backward time must not restore an expired mapping."
  let reallocated := step expired (.outbound { packet with source := 167772162 } allocation true 30)
  ensure reallocated.output.isSome "An expired public allocation must become available again."
  let otherProtocol := step opened (.outbound { packet with protocol := Protocol.udp } allocation true 10)
  ensure (otherProtocol.output.isSome && otherProtocol.state.bindings.length == 2)
    "Different transport protocols may use the same public endpoint."
  let flushed := (step reused.state .flush).state
  ensure (flushed.bindings.isEmpty && flushed.tracking.entries.isEmpty &&
    (step flushed (.inbound wire.reverse)).output.isNone)
    "Flushing must remove every mapping and return-flow grant."
  ensure ((step State.initial (.outbound packet allocation true 0)).output.isNone)
    "An expired outbound deadline must not open a mapping."
  IO.println "NAT tests passed."

end NetlibTest.NAT
