import Netlib.Protocol.TrackedFlow

namespace NetlibTest.TrackedFlow

open Netlib Packet Protocol
open Netlib.Protocol.TrackedFlow

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unrelated : ConntrackLifecycle.Record :=
  ⟨⟨⟨{ original with sourcePort := 41001 }, { (wire.reverse) with destinationPort := 40001 }, 0, 0, 0⟩,
    true, true⟩, false⟩
private def payload : List UInt8 := [0, 255, 17, 0, 99]
private def routes : List (Routing.Entry String) :=
  [⟨⟨3325256706, 32⟩, some "server"⟩, ⟨⟨3221225986, 32⟩, some "client"⟩]
private def permit : ConntrackLifecycle.Pipeline := { routes, forward := [], forwardDefault := .permit }
private def deny : ConntrackLifecycle.Pipeline := { routes, forward := [] }
private def lateDeny : ConntrackLifecycle.Pipeline := { permit with lateDefault := .deny }
private def established : ConntrackLifecycle.Pipeline := { routes, forward := [ConntrackLifecycle.establishedPermit] }

example (state : ConntrackLifecycle.State) (flow : NetfilterNAT.Entry) : ready state flow = true ↔ Ready state flow :=
  ready_correct state flow

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (flow : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state flow)
    (udp : flow.flow.original.protocol = Packet.Protocol.udp) (selected : packet.header = flow.flow.input direction)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 packet = .ok bytes) :
    ∃ outcome, WireForwarding.step pipeline state (wireInput flow direction packet) = .ok outcome ∧
      outcome.attachment = ⟨flow, direction, classification state flow direction, false⟩ ∧
      outcome.state = afterReply state flow direction ∧ Ready outcome.state flow ∧ outcome.state.Valid :=
  step_completes pipeline state flow direction packet valid available udp selected bytes encoded

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def load (result : Except WireForwarding.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def packet (header : Header) (ttl : UInt8) : IO UDP.DecodedIPv4 := do
  let datagram := UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨32, 4321, true, ttl, Packet.Protocol.udp, header.source, header.destination, transport⟩
  unwrap (UDP.decodeIPv4 (← unwrap (IPv4.encode ip)))

private def packetTests : IO Unit := do
  for seen in [false, true] do
    for first in [false, true] do
      let record : ConntrackLifecycle.Record := ⟨entry, seen⟩
      let records := if first then [record, unrelated] else [unrelated, record]
      let state : ConntrackLifecycle.State := ⟨records⟩
      ensure (state.check && ready state entry) "Readiness must find the selected binding in either table position."
      for direction in [FlowNAT.Direction.original, .reply] do
        for ttl in ([0, 1, 2, 64, 255] : List UInt8) do
          let input ← packet (entry.flow.input direction) ttl
          let reply := direction == .reply
          let expectedRecords := if reply then
            if first then [⟨entry, true⟩, unrelated] else [unrelated, ⟨entry, true⟩]
            else records
          let expectedClass := if reply || seen then StatefulACL.CTState.established else .new
          for (pipeline, mode) in [(permit, 0), (deny, 1), (lateDeny, 2), ({ permit with routes := [] }, 3),
              (established, 4)] do
            let outcome ← load (WireForwarding.step pipeline state (wireInput entry direction input))
            let expectedDisposition := if mode == 3 then WireForwarding.Disposition.routeDrop
              else if ttl.toNat ≤ 1 then .ttlExpired
              else if mode == 1 || (mode == 4 && !(reply || seen)) then .forwardDrop
              else if mode == 2 then .lateDrop else .forwarded
            ensure (outcome.disposition == expectedDisposition && outcome.state.records == expectedRecords &&
              outcome.state.check && ready outcome.state entry && outcome.attachment.entry == entry &&
              outcome.attachment.direction == direction && outcome.attachment.classification == expectedClass &&
              !outcome.attachment.fresh)
              "Every selected packet must complete and preserve the binding, despite policy, route, or TTL drops."
            match outcome.output with
            | none => ensure (expectedDisposition != .forwarded) "An available permitted packet must produce an emission."
            | some emission =>
              let target := if reply then original.reverse else wire
              ensure (expectedDisposition == .forwarded && emission.target == target && emission.decoded.header == target &&
                emission.decoded.datagram.payload == payload && emission.decoded.ip.packet.ttl.toNat == ttl.toNat - 1 &&
                emission.decoded.ip.packet.tos == 32 && emission.decoded.ip.packet.identification == 4321 &&
                emission.decoded.ip.packet.dontFragment)
                "Service must restore the exact NAT target and preserve packet bytes except the permitted header changes."
              ensure ((← unwrap (UDP.decodeIPv4 emission.bytes)) == emission.decoded)
                "Every emitted packet must retain valid IPv4 and UDP checksums."

private def driftTests : IO Unit := do
  let before : ConntrackLifecycle.State := ⟨[unrelated, ⟨entry, false⟩]⟩
  let originalPacket ← packet original 64
  let replyPacket ← packet wire.reverse 64
  let queuedOriginal := wireInput entry .original originalPacket
  let denied ← load (WireForwarding.step established before queuedOriginal)
  ensure (denied.output.isNone && denied.attachment.classification == .new)
    "An unreplied current record must not inherit another gateway's established classification."
  let reply ← load (WireForwarding.step deny before (wireInput entry .reply replyPacket))
  ensure (reply.output.isNone && reply.state.records == [unrelated, ⟨entry, true⟩])
    "A denied reply must update only the local reply observation."
  let served ← load (WireForwarding.step established reply.state queuedOriginal)
  ensure (served.output.isSome && served.attachment.classification == .established)
    "Service must use current local classification even when the packet was prepared before another reply."
  let revoked ← load (WireForwarding.step deny reply.state queuedOriginal)
  ensure (revoked.output.isNone && revoked.disposition == .forwardDrop && ready revoked.state entry)
    "A ready established binding must not bypass current policy denial."
  ensure (!ready ConntrackLifecycle.State.initial entry) "An empty table must not satisfy readiness."
  let invalid : ConntrackLifecycle.State := ⟨[⟨entry, false⟩, ⟨entry, true⟩]⟩
  ensure (ready invalid entry && !invalid.check) "Readiness alone must not assert table validity."
  match WireForwarding.step permit invalid queuedOriginal with
  | .error (.lifecycle .invalidState) => pure ()
  | _ => throw (IO.userError "Invalid tables must not obtain the service theorem's validity premise.")
  let other ← packet { original with sourcePort := 41002 } 64
  match WireForwarding.step permit before (wireInput entry .original other) with
  | .error (.lifecycle .missingCandidate) => pure ()
  | _ => throw (IO.userError "Readiness must not invent an association for an unselected header.")
  let broken := { originalPacket with ip := { originalPacket.ip with checksum := originalPacket.ip.checksum + 1 } }
  match WireForwarding.step permit before (wireInput entry .original broken) with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "Malformed source bytes must not obtain the encoded-packet premise.")

def run : IO Unit := do
  packetTests
  driftTests

end NetlibTest.TrackedFlow
