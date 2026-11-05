import Netlib.Protocol.ICMPForwardingFacts

namespace NetlibTest.ICMPForwarding

open Netlib Packet Protocol Protocol.ICMPForwarding

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩
private def minimum : MTUForwarding.MTU := ⟨68, by decide⟩
private def odd : MTUForwarding.MTU := ⟨69, by decide⟩
private def medium : MTUForwarding.MTU := ⟨600, by decide⟩
private def large : MTUForwarding.MTU := ⟨1500, by decide⟩
private def returnPath (mtu : MTUForwarding.MTU := large) : ReturnPath := ⟨"return", 3221225985, mtu, 32⟩
private def routes : List (Routing.Entry String) :=
  [⟨⟨wire.destination, 32⟩, some "outside"⟩, ⟨⟨original.source, 32⟩, some "inside"⟩]
private def related : StatefulACL.Rule := ⟨{}, some [.related], .permit⟩
private def context (mtu : MTUForwarding.MTU := large) : ICMPForwarding.Context :=
  ⟨fun _ => some (returnPath mtu), [], [related], .deny, [related], .deny⟩
private def active (mtu : MTUForwarding.MTU := medium) (control : ICMPForwarding.Context := context) : Pipeline :=
  ⟨⟨⟨routes, [], .permit, [], .permit⟩, fun _ => mtu⟩, control⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def load (result : Except MTUForwarding.Error (Outcome input)) : IO (Outcome input) :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def packet (header : Header) (size : Nat) (df : Bool) (ttl : UInt8 := 64)
    (omitted : Bool := false) (tos : UInt8 := 185) : IO UDP.DecodedIPv4 := do
  let payload : List UInt8 := (List.range size).map (fun value => UInt8.ofNat (value * 17))
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨tos, 65535, df, ttl, header.protocol, header.source, header.destination, transport⟩
  let bytes ← unwrap (IPv4.encode ip)
  unwrap (UDP.decodeIPv4 (bytes ++ [0, 255]))

private def emitted (outcome : Outcome input) : IO (Emission input) :=
  match outcome.control.output with
  | some emission => pure emission
  | none => throw (IO.userError "Expected a generated ICMP error.")

private def checkEmission (input : Input) (outcome : Outcome input.transit.packet) (expected : ICMP.Kind)
    (expectedLength : Nat) : IO Unit := do
  let emission ← emitted outcome
  let ip ← unwrap (IPv4.decode emission.bytes)
  let control ← unwrap (ICMP.decode ip.packet.payload)
  let quote ← unwrap (IPv4Quote.decode control.message.quote)
  let initial := IPv4Quote.make input.transit.packet expectedLength
  ensure (outcome.control.disposition == .sent && control.message.kind == expected &&
      emission.identification == 1234 && ip.packet.identification == 1234 && ip.packet.ttl == 32 &&
      ip.packet.tos == errorTos input.transit.packet.ip.packet.tos && !ip.packet.dontFragment &&
      ip.packet.protocol == Packet.Protocol.icmp && ip.packet.source == input.transit.packet.ip.packet.destination &&
      ip.packet.destination == input.transit.packet.ip.packet.source)
    "A RELATED error must use return-route metadata and inverse address NAT without inheriting transport ports."
  ensure (quote.packet == initial.packet && quote.declaredLength == initial.declaredLength &&
      control.message.quote.length == expectedLength && ip.packet.wireLength == expectedLength + 28 &&
      emission.bytes.length ≤ emission.path.mtu.val && emission.bytes.length ≤ 576)
    "The actual wire quotation must restore every original packet field, UDP checksum, and available payload prefix."
  ensure (InternetChecksum.valid ip.packet.payload && InternetChecksum.valid (IPv4Quote.headerBytes quote) &&
      quote.packet.payload.drop 8 == input.transit.packet.datagram.payload.take (expectedLength - 28) &&
      ICMPNAT.quotedChecksum quote.packet.payload == input.transit.packet.datagram.checksum &&
      quote.packet.ttl == input.transit.packet.ip.packet.ttl && outcome.transit.output.isNone && outcome.transit.afterSource.isNone)
    "ICMP and quoted IPv4 checksums must validate while the original UDP checksum and TTL are restored exactly."

private def quotationTests : IO Unit := do
  for omitted in [false, true] do
    for size in [0, 1, 2, 11, 12, 13, 600, 601] do
      let input : Input := ⟨⟨0, ← packet original size true 1 omitted, some entry⟩, false⟩
      let outcome ← load (step (active) ConntrackLifecycle.State.initial input 1234)
      checkEmission input outcome .timeExceeded (min (size + 28) 548)
      ensure (outcome.transit.state == ConntrackLifecycle.State.initial && outcome.transit.selectedMTU.isNone)
        "TTL expiry must precede MTU selection and fresh conntrack confirmation."
  let input : Input := ⟨⟨0, ← packet original 601 true, some entry⟩, false⟩
  for returnMTU in [minimum, odd, large] do
    let outcome ← load (step (active medium (context returnMTU)) ConntrackLifecycle.State.initial input 1234)
    let quoteLength := min (returnMTU.val - 28) 548
    checkEmission input outcome (.fragmentationNeeded 600) quoteLength
    ensure (outcome.transit.selectedMTU.map (·.val) == some 600 && outcome.transit.mtuNeeded == some 600 &&
        (← emitted outcome).bytes.length == quoteLength + 28 && outcome.transit.state == ConntrackLifecycle.State.initial &&
        (← emitted outcome).packet.tos == 216)
      "The forward MTU must remain 600 while the return route bounds odd/even partial quotes and error TOS selects precedence six."

private def suppressionTests : IO Unit := do
  let input : Input := ⟨⟨0, ← packet original 601 true, some entry⟩, false⟩
  let grouped ← load (step (active) ConntrackLifecycle.State.initial { input with linkGroup := true } 1234)
  ensure (grouped.control.disposition == .suppressed && grouped.control.output.isNone)
    "An Ethernet group destination must suppress a generated error."
  let identity (header : Header) : NetfilterNAT.Entry := ⟨⟨header, header.reverse, 0, 0, 0⟩, false, false⟩
  let routed : Pipeline := { active with forwarding :=
    { (active).forwarding with forwarding := ⟨[⟨⟨0, 0⟩, some "all"⟩], [], .permit, [], .permit⟩ } }
  for source in ([0, 16777215, 2130706433, 3758096385, 4294967295] : List Address) do
    let header := { original with source := source }
    let invalid : Input := ⟨⟨0, ← packet header 601 true, some (identity header)⟩, false⟩
    let outcome ← load (step routed ConntrackLifecycle.State.initial invalid 1234)
    ensure (outcome.control.disposition == .suppressed && outcome.control.output.isNone)
      "Zero-network, loopback, multicast, and reserved/broadcast sources must suppress errors."
  for destination in ([3758096385, 4294967295, 3221226239] : List Address) do
    let header := { original with destination := destination }
    let invalid : Input := ⟨⟨0, ← packet header 601 true, some (identity header)⟩, false⟩
    let outcome ← load (step { routed with control := { context with broadcasts := [3221226239] } }
      ConntrackLifecycle.State.initial invalid 1234)
    ensure (outcome.control.disposition == .suppressed && outcome.control.output.isNone)
      "Multicast, limited broadcast, and configured directed-broadcast destinations must suppress errors."
  let broadcast ← load (step { active with control := { context with broadcasts := [original.source] } }
    ConntrackLifecycle.State.initial input 1234)
  ensure (broadcast.control.disposition == .suppressed) "A configured broadcast source must suppress errors."
  let noRoute ← load (step { active with control := { context with returnPath := fun _ => none } }
    ConntrackLifecycle.State.initial input 1234)
  ensure (noRoute.control.disposition == .noReturnRoute && noRoute.control.output.isNone)
    "An error needs a route back to the original source."

private def policyTests : IO Unit := do
  let input : Input := ⟨⟨0, ← packet original 601 true, some entry⟩, false⟩
  let blocked ← load (step { active with control := { context with output := [] } }
    ConntrackLifecycle.State.initial input 1234)
  let late ← load (step { active with control := { context with late := [] } }
    ConntrackLifecycle.State.initial input 1234)
  ensure (blocked.control.disposition == .outputDrop && blocked.control.beforeSource.isSome &&
      blocked.control.afterSource.isNone && blocked.control.output.isNone &&
      late.control.disposition == .lateDrop && late.control.beforeSource.isSome &&
      late.control.afterSource.isSome && late.control.output.isNone)
    "RELATED output and late policy must independently gate an error at their respective address-NAT stages."
  let outputMatch : Match := {
    source := some ⟨(returnPath large).source, 32⟩
    destination := some ⟨original.source, 32⟩, sourcePorts := some (PortRange.single 0), destinationPorts := some (PortRange.single 0) }
  let lateMatch : Match := { outputMatch with source := some ⟨original.destination, 32⟩ }
  let staged := { context with output := [⟨outputMatch, some [.related], .permit⟩], late := [⟨lateMatch, some [.related], .permit⟩] }
  let permitted ← load (step (active medium staged) ConntrackLifecycle.State.initial input 1234)
  checkEmission input permitted (.fragmentationNeeded 600) 548
  for kind in [0, 1, 2, 3] do
    let transit : MTUForwarding.Input := ⟨0, ← packet original 10 false, some entry⟩
    let forward := (active).forwarding.forwarding
    let pipeline := match kind with
      | 0 => active
      | 1 => { active with forwarding := { (active).forwarding with forwarding := { forward with routes := [] } } }
      | 2 => { active with forwarding := { (active).forwarding with forwarding := { forward with forwardDefault := .deny } } }
      | _ => { active with forwarding := { (active).forwarding with forwarding := { forward with lateDefault := .deny } } }
    let outcome ← load (step pipeline ConntrackLifecycle.State.initial ⟨transit, false⟩ 1234)
    ensure (outcome.control.disposition == .notNeeded && outcome.control.output.isNone && outcome.control.reason.isNone)
      "Normal transit and route/forward/late drops must not create ICMP errors."

private def stateTests : IO Unit := do
  for ttl in ([1, 64] : List UInt8) do
    let request : Input := ⟨⟨0, ← packet original 601 true ttl, some entry⟩, false⟩
    let fresh ← load (step (active) ConntrackLifecycle.State.initial request 1234)
    let cached ← load (step (active) unreplied { request with transit := { request.transit with candidate := none } } 1234)
    ensure ((← emitted fresh).attachment.fresh && fresh.transit.state == ConntrackLifecycle.State.initial &&
        !(← emitted cached).attachment.fresh && cached.transit.state == unreplied)
      "Control output must neither confirm a fresh flow nor change a cached original-direction record."
    let reply : Input := ⟨⟨0, ← packet wire.reverse 601 true ttl, none⟩, false⟩
    let outcome ← load (step (active) unreplied reply 1234)
    checkEmission reply outcome (if ttl == 1 then .timeExceeded else .fragmentationNeeded 600) 548
    ensure (outcome.transit.state == replied && outcome.transit.attachment.direction == .reply &&
        outcome.transit.attachment.classification == .established && !outcome.transit.attachment.fresh)
      "TTL and DF reply errors must retain the parent's seen-reply update while inverse NAT restores the reply quotation."
  let noDNAT : NetfilterNAT.Entry := ⟨⟨original, original.reverse, 0, 0, 0⟩, false, false⟩
  let input : Input := ⟨⟨0, ← packet original 601 true, some noDNAT⟩, false⟩
  let pipeline := { active with forwarding := { (active).forwarding with forwarding :=
    ⟨[⟨⟨0, 0⟩, some "all"⟩], [], .permit, [], .permit⟩ } }
  let outcome ← load (step pipeline ConntrackLifecycle.State.initial input 1234)
  ensure ((← emitted outcome).packet.source == (returnPath large).source &&
      (← emitted outcome).packet.destination == original.source)
    "An error without destination NAT must retain its return-route source address."

private def zeroChecksumTests : IO Unit := do
  let base ← packet original 13 true 1
  let zeroId := { base.ip.packet with identification := 0 }
  let ip := { zeroId with identification := IPv4.computedChecksum zeroId }
  ensure (IPv4.computedChecksum ip == 0) "The fixture must exercise IPv4's two valid zero checksum representations."
  for checksum in ([0, 65535] : List InternetChecksum.Word) do
    let source : UDP.DecodedIPv4 := ⟨⟨ip, checksum, []⟩, base.datagram⟩
    let input : Input := ⟨⟨0, source, some entry⟩, false⟩
    let outcome ← load (step (active) ConntrackLifecycle.State.initial input 1234)
    checkEmission input outcome .timeExceeded 41
    ensure ((← emitted outcome).quote.checksum == 0)
      "Quotation restoration may normalize only the valid dual-zero IPv4 checksum field."

private def statusTests : IO Unit := do
  let routed := { active with forwarding := { (active).forwarding with forwarding :=
    ⟨[⟨⟨0, 0⟩, some "all"⟩], [], .permit, [], .permit⟩ } }
  for sourceNAT in [false, true] do
    for destinationNAT in [false, true] do
      let translated := { original with
        source := if sourceNAT then wire.source else original.source
        sourcePort := if sourceNAT then wire.sourcePort else original.sourcePort
        destination := if destinationNAT then wire.destination else original.destination
        destinationPort := if destinationNAT then wire.destinationPort else original.destinationPort }
      let candidate : NetfilterNAT.Entry := ⟨⟨original, translated.reverse, 0, 0, 0⟩, sourceNAT, destinationNAT⟩
      let state : ConntrackLifecycle.State := ⟨[⟨candidate, false⟩]⟩
      for reply in [false, true] do
        let header := if reply then translated.reverse else original
        let input : Input := ⟨⟨0, ← packet header 601 true, none⟩, false⟩
        let outcome ← load (step routed state input 1234)
        let emission ← emitted outcome
        let changesDestination := if reply then sourceNAT else destinationNAT
        ensure (emission.packet.source == (if changesDestination then header.destination else (returnPath large).source) &&
            emission.packet.destination == header.source &&
            emission.quote.packet == (IPv4Quote.make input.transit.packet emission.length).packet)
          "Every NAT status combination and direction must restore the tuple without translating ICMP port fields."
  let input : Input := ⟨⟨0, ← packet original 601 true, some entry⟩, false⟩
  let deniedTransit := { active with forwarding := { (active).forwarding with forwarding :=
    { (active).forwarding.forwarding with forwardDefault := .deny, lateDefault := .deny } } }
  let first ← load (step deniedTransit ConntrackLifecycle.State.initial input 1234)
  let second ← load (step deniedTransit first.transit.state input 1234)
  ensure ((← emitted first).bytes == (← emitted second).bytes && first.transit.output.isNone && second.transit.output.isNone)
    "The selected no-rate-limit profile may emit repeated DF errors before a denying transit filter without granting transit permission."

def run : IO Unit := do
  quotationTests
  suppressionTests
  policyTests
  stateTests
  zeroChecksumTests
  statusTests
  IO.println "Locally generated ICMP forwarding tests passed."

end NetlibTest.ICMPForwarding
