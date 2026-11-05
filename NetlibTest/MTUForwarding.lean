import Netlib.Protocol.MTUForwarding

namespace NetlibTest.MTUForwarding

open Netlib Packet Protocol Protocol.MTUForwarding

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def smallMTU : MTU := ⟨68, by decide⟩
private def mediumMTU : MTU := ⟨76, by decide⟩
private def largeMTU : MTU := ⟨1500, by decide⟩
private def routes : List (Routing.Entry String) :=
  [⟨⟨wire.destination, 32⟩, some "outside"⟩, ⟨⟨original.source, 32⟩, some "inside"⟩]
private def backendMatch : Match := {
  destination := some ⟨wire.destination, 32⟩
  destinationPorts := some (PortRange.single wire.destinationPort) }
private def aliasMatch : Match := {
  source := some ⟨wire.source, 32⟩
  sourcePorts := some (PortRange.single wire.sourcePort) }
private def permit : ConntrackLifecycle.Pipeline :=
  ⟨routes, [⟨backendMatch, none, .permit⟩], .deny, [⟨aliasMatch, none, .permit⟩], .deny⟩
private def permitBoth : ConntrackLifecycle.Pipeline := ⟨routes, [], .permit, [], .permit⟩
private def configured (forwarding : ConntrackLifecycle.Pipeline) (mtu : MTU := smallMTU) : Pipeline :=
  ⟨forwarding, fun _ => mtu⟩

example (emission : Emission input) (part : IPv4Fragment.Decoded) (member : part ∈ emission.fragments.fragments) :
    part.packet.wireLength ≤ emission.mtu.val := emission.fits part member

example (emission : Emission input) :
    IPv4Fragmentation.reassemble emission.fragments.fragments = .ok emission.transit.decoded.ip.packet := emission.reassembled

example (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (dropped : outcome.disposition = .mtuExceeded) (fresh : outcome.attachment.fresh = true) :
    outcome.state = state ∧ outcome.output = none ∧ outcome.afterSource = none ∧ outcome.parent = none :=
  mtuExceeded_fresh pipeline state input outcome accepted dropped fresh

example (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input) (bytes : List UInt8)
    (encoded : UDP.encodeIPv4 input.packet = .ok bytes) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared) (model : ConntrackLifecycle.Outcome)
    (processed : ConntrackLifecycle.process pipeline.forwarding prepared = .ok model) :
    ∃ outcome, step pipeline state input = .ok outcome := step_completes pipeline state input bytes encoded prepared attached model processed

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def load (result : Except Error (Outcome input)) : IO (Outcome input) :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def packet (header : Header) (size : Nat) (df : Bool) (ttl : UInt8 := 64) (omitted : Bool := false) : IO UDP.DecodedIPv4 := do
  let payload : List UInt8 := List.replicate size 170
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨184, 65535, df, ttl, header.protocol, header.source, header.destination, transport⟩
  let bytes ← unwrap (IPv4.encode ip)
  unwrap (UDP.decodeIPv4 (bytes ++ [0, 255]))

private def output (outcome : Outcome input) : IO (Emission input) :=
  match outcome.output with
  | some emission => pure emission
  | none => throw (IO.userError "Expected a fragment-family output.")

private def fragmentedTests : IO Unit := do
  for omitted in [false, true] do
    for mtu in [smallMTU, mediumMTU, largeMTU] do
      let input : Input := ⟨0, ← packet original 100 false 64 omitted, some entry⟩
      let result ← load (step (configured permit mtu) ConntrackLifecycle.State.initial input)
      let emission ← output result
      ensure (result.disposition == .forwarded && result.state == unreplied && result.attachment.fresh &&
          result.selectedMTU.map (·.val) == some mtu.val && result.mtuNeeded.isNone && result.parent.isSome &&
          emission.transit.target == wire)
        "A complete datagram must undergo one NAT/filter/confirmation execution before its fragment family is emitted."
      let parts := emission.fragments.fragments
      ensure (!parts.isEmpty && emission.bytes.length == parts.length && parts.all (fun part => part.packet.wireLength ≤ mtu.val))
        "Every emitted fragment must fit the selected route MTU."
      for bytes in emission.bytes do
        let part ← unwrap (IPv4Fragment.decode bytes)
        ensure (bytes.length == part.packet.wireLength && part.packet.source == wire.source &&
            part.packet.destination == wire.destination && part.packet.protocol == Packet.Protocol.udp &&
            part.packet.ttl == 63 && part.packet.tos == 184 && part.packet.identification == 65535 && !part.packet.dontFragment)
          "Each actual fragment must carry the translated IP fields, metadata, decremented TTL, and a valid header checksum."
      let reconstructed ← unwrap (IPv4Fragmentation.reassemble parts.reverse)
      let datagram ← unwrap (UDP.decode reconstructed.source reconstructed.destination reconstructed.payload)
      ensure (reconstructed == emission.transit.decoded.ip.packet && datagram == emission.transit.decoded.datagram &&
          datagram.payload == input.packet.datagram.payload && (datagram.checksum == 0) == omitted)
        "Strict reassembly must recover the complete translated UDP datagram and preserve explicit checksum omission."
      if mtu.val == 68 then
        ensure (parts.map (·.packet.offset.val) == [0, 6, 12] &&
            parts.map (·.packet.payload.length) == [48, 48, 12] && parts.map (·.packet.moreFragments) == [true, true, false])
          "The minimum MTU must align nonfinal payloads in eight-byte units, including the one UDP header."
      if mtu.val == 76 then ensure (parts.length == 2) "A different selected MTU must change the fragmentation geometry."
      if mtu.val == 1500 then ensure (parts.length == 1) "A fitting datagram must remain one packet."
      let repeated : Input := { input with candidate := none }
      let cached ← load (step (configured permit mtu) result.state repeated)
      ensure (!cached.attachment.fresh && cached.state == result.state && (← output cached).bytes.length == parts.length)
        "Fragmentation must not create per-fragment conntrack records or replace the cached binding."

private def gateTests : IO Unit := do
  let fitting : Input := ⟨0, ← packet original 40 true, some entry⟩
  let exact ← load (step (configured permit) ConntrackLifecycle.State.initial fitting)
  let emission ← output exact
  ensure (emission.fragments.fragments.length == 1 && emission.fragments.fragments.all (fun part =>
      part.packet.dontFragment && !part.packet.moreFragments && part.packet.offset.val == 0))
    "A DF datagram exactly at the selected MTU must pass without splitting."
  let tooLarge : Input := ⟨0, ← packet original 41 true, some entry⟩
  for forwarding in [permit, { permit with forward := [] }, { permit with late := [] }] do
    let result ← load (step (configured forwarding) ConntrackLifecycle.State.initial tooLarge)
    ensure (result.disposition == .mtuExceeded && result.mtuNeeded == some 68 && result.selectedMTU.map (·.val) == some 68 &&
        result.state == ConntrackLifecycle.State.initial && result.output.isNone && result.afterSource.isNone && result.parent.isNone)
      "An oversized DF packet must stop before forward/late filtering, source NAT, and fresh confirmation."
  for ttl in ([0, 1] : List UInt8) do
    let low : Input := ⟨0, ← packet original 100 true ttl, some entry⟩
    let result ← load (step (configured permit) ConntrackLifecycle.State.initial low)
    ensure (result.disposition == .ttlExpired && result.selectedMTU.isNone && result.mtuNeeded.isNone &&
        result.state.records.isEmpty && result.parent.isSome && result.output.isNone)
      "TTL expiry must precede the oversized-DF gate."
    let missing ← load (step (configured { permit with routes := [] }) ConntrackLifecycle.State.initial low)
    ensure (missing.disposition == .routeDrop && missing.selectedMTU.isNone && missing.mtuNeeded.isNone)
      "Destination routing must precede TTL and route MTU selection."
  let large : Input := ⟨0, ← packet original 100 false 2, some entry⟩
  let forwarded ← load (step (configured permit) ConntrackLifecycle.State.initial large)
  ensure ((← output forwarded).fragments.fragments.all (fun part => part.packet.ttl == 1))
    "TTL must decrement once for the full datagram, not once per fragment."
  let blocked ← load (step (configured { permit with forward := [] }) ConntrackLifecycle.State.initial large)
  let late ← load (step (configured { permit with late := [] }) ConntrackLifecycle.State.initial large)
  ensure (blocked.disposition == .forwardDrop && late.disposition == .lateDrop &&
      blocked.output.isNone && late.output.isNone && blocked.state.records.isEmpty && late.state.records.isEmpty)
    "A non-DF oversized datagram must still pass both filters before confirmation or fragment output."

private def replyTests : IO Unit := do
  let active : Pipeline := ⟨permitBoth, fun hop => if hop == "outside" then largeMTU else smallMTU⟩
  let request : Input := ⟨0, ← packet original 100 true, some entry⟩
  let first ← load (step active ConntrackLifecycle.State.initial request)
  ensure ((← output first).mtu.val == 1500) "MTU selection must use the post-DNAT output route."
  let reply : Input := ⟨0, ← packet wire.reverse 100 true, none⟩
  let dropped ← load (step active first.state reply)
  ensure (dropped.disposition == .mtuExceeded && dropped.state == replied && dropped.output.isNone &&
      dropped.attachment.classification == .established && !dropped.attachment.fresh && dropped.nextHop == some "inside" &&
      dropped.mtuNeeded == some 68 && dropped.afterDestination.destination == original.source && dropped.afterSource.isNone)
    "An oversized cached DF reply must retain seen-reply and use the inverse-NAT route MTU before filtering or source translation."
  let established : Pipeline := { active with forwarding :=
    { permitBoth with forward := [ConntrackLifecycle.establishedPermit], forwardDefault := .deny } }
  let cached ← load (step established dropped.state { request with candidate := none })
  ensure (cached.attachment.classification == .established && cached.state == replied && cached.output.isSome)
    "A reply's DF drop must still affect later original-direction classification."

private def collisionTests : IO Unit := do
  let collision : NetfilterNAT.Entry := { entry with flow := { entry.flow with original := { original with sourcePort := 41001 } } }
  let blocked : Input := ⟨0, ← packet collision.flow.original 100 true, some collision⟩
  let dropped ← load (step (configured permit) unreplied blocked)
  ensure (dropped.disposition == .mtuExceeded && dropped.state == unreplied)
    "An MTU-rejected fresh candidate must not reach confirmation collision checks."
  let eligible : Input := ⟨0, ← packet collision.flow.original 100 false, some collision⟩
  match step (configured permit) unreplied eligible with
  | .error (.lifecycle .confirmationCollision) => pure ()
  | _ => throw (IO.userError "Confirmation must still precede fragmentation for a permitted non-DF datagram.")

def run : IO Unit := do
  fragmentedTests
  gateTests
  replyTests
  collisionTests
  IO.println "MTU-aware tracked forwarding tests passed."

end NetlibTest.MTUForwarding
