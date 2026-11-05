import Netlib.Protocol.RelatedICMP

namespace NetlibTest.RelatedICMP

open Netlib Packet Protocol Protocol.RelatedICMP

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def translated : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def router : Address := 3325256705
private def minimum : IPv4Fragmentation.MTU := ⟨68, by decide⟩
private def large : IPv4Fragmentation.MTU := ⟨1500, by decide⟩
private def related : StatefulACL.Rule := ⟨{}, some [.related], .permit⟩
private def active (mtu : IPv4Fragmentation.MTU := large) : Pipeline :=
  ⟨⟨[⟨⟨0, 0⟩, some "all"⟩], [related], .deny, [related], .deny⟩, fun _ => mtu⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def run (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input) : IO (Outcome before input) :=
  match step pipeline before input with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def entry (sourceNAT destinationNAT : Bool) : NetfilterNAT.Entry :=
  let wire := { original with
    source := if sourceNAT then translated.source else original.source
    sourcePort := if sourceNAT then translated.sourcePort else original.sourcePort
    destination := if destinationNAT then translated.destination else original.destination
    destinationPort := if destinationNAT then translated.destinationPort else original.destinationPort }
  ⟨⟨original, wire.reverse, 7, 9, 0⟩, sourceNAT, destinationNAT⟩

private def receive (quote : Header) (destination : Address) (size : Nat := 13) (quoteSize : Nat := 21)
    (omitted : Bool := false) (ttl : UInt8 := 64) (df : Bool := false)
    (source : Address := router) : IO Source := do
  let data := (List.range size).map (fun value => UInt8.ofNat (value * 17))
  let datagram : UDP.Datagram := if omitted then ⟨quote.sourcePort, quote.destinationPort, 0, data⟩
    else UDP.computed quote.source quote.destination quote.sourcePort quote.destinationPort data
  let transport ← unwrap (UDP.encode quote.source quote.destination datagram)
  let ip : IPv4.Packet := ⟨185, 1234, true, 63, quote.protocol, quote.source, quote.destination, transport⟩
  let quoteBytes := IPv4.headerBytes ip (IPv4.computedChecksum ip) ++ transport.take quoteSize
  let message : ICMP.Message := ⟨.fragmentationNeeded 600, quoteBytes⟩
  let outer : IPv4.Packet := ⟨192, 4321, df, ttl, Packet.Protocol.icmp, source, destination, ICMP.encode message⟩
  decode (← unwrap (IPv4.encode outer)) |> unwrap

private def rewrap (source : Source) (quote : IPv4QuotePrefix.Decoded) : IO Source := do
  let message := { source.icmp.message with quote := IPv4QuotePrefix.bytes quote }
  let outer := { source.ip.packet with payload := ICMP.encode message }
  decode (← unwrap (IPv4.encode outer)) |> unwrap

private def emission (outcome : Outcome before input) : IO (Emission before input) :=
  match outcome.output with
  | some value => pure value
  | none => throw (IO.userError "Expected RELATED forwarding.")

private def natTests : IO Unit := do
  for sourceNAT in [false, true] do
    for destinationNAT in [false, true] do
      let cached := entry sourceNAT destinationNAT
      for direction in [FlowNAT.Direction.original, .reply] do
        for seenReply in [false, true] do
          for omitted in [false, true] do
            for quoteSize in [8, 9, 20, 21] do
              let quoted := (cached.flow.input direction).reverse
              let source ← receive quoted (cached.flow.input direction).destination 13 quoteSize omitted
              let input : Input := ⟨cached.flow.zone direction, source⟩
              let before : ConntrackLifecycle.State := ⟨[⟨cached, seenReply⟩]⟩
              let outcome ← run active before input
              let output ← emission outcome
              let reassembled ← unwrap (IPv4Fragmentation.reassemble output.family.fragments)
              let control ← unwrap (ICMP.decode reassembled.payload)
              let restored ← unwrap (IPv4Quote.decode control.message.quote)
              let target := cached.flow.input (opposite direction)
              let initial := source.quote.packet
              ensure (outcome.disposition == .forwarded && outcome.state == before &&
                  output.association.direction == direction && restored.packet.ttl == 63 &&
                  IPv4Quote.header restored == target && restored.packet.payload.drop 8 == initial.payload.drop 8 &&
                  (ICMPNAT.quotedChecksum restored.packet.payload == 0) == omitted &&
                  restored.declaredLength == source.quote.declaredLength)
                "RELATED forwarding must restore both endpoints, preserve the quote prefix and frozen table, and retain quoted TTL."
              ensure (reassembled.ttl == 63 && reassembled.tos == 192 && reassembled.identification == 4321 &&
                  control.message.kind == .fragmentationNeeded 600 && reassembled.destination == target.source &&
                  reassembled.source == (if cached.changesSource direction then target.destination else router) &&
                  InternetChecksum.valid reassembled.payload && InternetChecksum.valid (IPv4Quote.headerBytes restored))
                "Outer address NAT must follow status bits while preserving ICMP metadata and valid checksums."
              let completePayload := restored.packet.payload.take 8 ++
                (List.range 13).map (fun value => UInt8.ofNat (value * 17))
              let datagram ← unwrap (UDP.decode target.source target.destination completePayload)
              ensure (datagram.sourcePort == target.sourcePort && datagram.destinationPort == target.destinationPort &&
                  (datagram.checksum == 0) == omitted)
                "Every quote prefix must retain the checksum of the complete translated UDP datagram."
              ensure (outcome.afterDestination == some output.association.beforeSource &&
                  output.association.destinationQuote.packet.destination == initial.destination &&
                  (IPv4QuotePrefix.header output.association.destinationQuote).destinationEndpoint == quoted.destinationEndpoint &&
                  output.association.destinationQuote.packet.source == target.source &&
                  output.association.destinationQuote.packet.payload.drop 8 == initial.payload.drop 8)
                "Before routing, destination NAT must patch only the quotation's source endpoint."

private def associationTests : IO Unit := do
  let cached := entry true true
  let quoted := cached.flow.reply.reverse
  let source ← receive quoted cached.flow.reply.destination
  let before : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
  let input : Input := ⟨9, source⟩
  let accepted ← run active before input
  ensure (accepted.disposition == .forwarded && accepted.state == before)
    "An unreplied connection must accept RELATED without marking SEEN_REPLY."
  for badZone in [0, 7, 10] do
    let outcome ← run active before { input with zone := badZone }
    ensure (outcome.disposition == .unrelated && outcome.output.isNone && outcome.state == before)
      "A quote in the wrong zone cannot associate or create a flow."
  for outerSource in ([0, 1, router, 4294967295] : List Address) do
    let source ← receive quoted cached.flow.reply.destination 13 21 false 64 false outerSource
    let outcome ← run active before ⟨9, source⟩
    ensure (outcome.disposition == .forwarded && outcome.state == before)
      "Association does not authenticate the outer ICMP source."
  for header in [{ quoted with sourcePort := 1 }, { quoted with destinationPort := 1 },
      { quoted with protocol := Packet.Protocol.tcp }] do
    let source ← receive header cached.flow.reply.destination
    let outcome ← run active before ⟨9, source⟩
    ensure (outcome.disposition == .unrelated && outcome.output.isNone && outcome.state == before)
      "Unmatched quoted ports and protocols cannot invent an association."
  let wrongDestination ← receive quoted original.source
  let rejected ← run active before ⟨9, wrongDestination⟩
  ensure (rejected.disposition == .unrelated && rejected.output.isNone && rejected.state == before)
    "A matching reverse quote requires the native outer-destination consistency guard."
  let missing ← run active ConntrackLifecycle.State.initial input
  ensure (missing.disposition == .unrelated && missing.state == ConntrackLifecycle.State.initial)
    "An absent or expired record cannot be resurrected by an ICMP error."
  let second := { cached with flow := { cached.flow with
    original := { original with sourcePort := 41001 },
    reply := { cached.flow.reply with destinationPort := 40001 } } }
  let shared : ConntrackLifecycle.State := ⟨[⟨cached, false⟩, ⟨second, false⟩]⟩
  let unique ← run active shared input
  ensure ((← emission unique).association.entry == cached && unique.state == shared)
    "Connections sharing a public address must remain distinct by their zone and port keys."

private def policyTests : IO Unit := do
  let cached := entry true true
  let before : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
  for status in [StatefulACL.CTState.new, .established, .related, .untracked, .invalid] do
    let source ← receive cached.flow.reply.reverse cached.flow.reply.destination
    let input : Input := ⟨9, source⟩
    let rule : StatefulACL.Rule := ⟨{}, some [status], .permit⟩
    let pipeline := { active with forwarding := { active.forwarding with forward := [rule] } }
    let outcome ← run pipeline before input
    ensure (outcome.disposition == (if status == .related then .forwarded else .forwardDrop) && outcome.state == before)
      "Received errors must be classified RELATED regardless of the parent's ordinary CT state."
  let source ← receive cached.flow.reply.reverse cached.flow.reply.destination
  let input : Input := ⟨9, source⟩
  let noRoute ← run { active with forwarding := { active.forwarding with routes := [] } } before input
  let denied ← run { active with forwarding := { active.forwarding with late := [] } } before input
  ensure (noRoute.disposition == .routeDrop && noRoute.output.isNone &&
      denied.disposition == .lateDrop && denied.output.isNone && denied.afterSource.isSome &&
      denied.state == before && noRoute.state == before)
    "Route and late-policy drops must keep the confirmed table frozen."
  let postDNAT : Match := {
    source := some ⟨router, 32⟩, destination := some ⟨original.source, 32⟩,
    protocol := some Packet.Protocol.icmp, sourcePorts := some (PortRange.single 0), destinationPorts := some (PortRange.single 0) }
  let postSNAT := { postDNAT with source := some ⟨original.destination, 32⟩ }
  let staged := { active with forwarding := { active.forwarding with
    routes := [⟨⟨original.source, 32⟩, some "inside"⟩],
    forward := [⟨postDNAT, some [.related], .permit⟩], late := [⟨postSNAT, some [.related], .permit⟩] } }
  let routed ← run staged before input
  ensure (routed.disposition == .forwarded && routed.nextHop == some "inside")
    "Routing and forward policy must see destination NAT, and late policy must see source NAT."

private def ttlAndMTUTests : IO Unit := do
  let cached := entry true true
  let before : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
  for ttl in ([0, 1] : List UInt8) do
    let source ← receive cached.flow.reply.reverse cached.flow.reply.destination 100 108 false ttl
    let outcome ← run (active minimum) before ⟨9, source⟩
    ensure (outcome.disposition == .ttlExpired && outcome.output.isNone && outcome.afterSource.isNone && outcome.state == before)
      "An expired ICMP error must drop without generating another error or updating conntrack."
  for df in [false, true] do
    let source ← receive cached.flow.reply.reverse cached.flow.reply.destination 100 108 false 64 df
    let outcome ← run (active minimum) before ⟨9, source⟩
    if df then
      ensure (outcome.disposition == .mtuExceeded && outcome.output.isNone && outcome.afterSource.isNone && outcome.state == before)
        "An oversized DF ICMP error must drop before source NAT without generating another control packet."
      let denied := { active minimum with forwarding := { (active minimum).forwarding with forward := [] } }
      let early ← run denied before ⟨9, source⟩
      ensure (early.disposition == .mtuExceeded && early.afterSource.isNone)
        "The DF-MTU guard must precede forward filtering and source NAT."
    else
      let output ← emission outcome
      ensure (output.family.fragments.length > 1 && output.family.fragments.all (fun part => decide (part.packet.wireLength ≤ 68)))
        "A legal minimum egress MTU must fragment a large ICMP error."
      let reassembled ← unwrap (IPv4Fragmentation.reassemble output.family.fragments.reverse)
      let control ← unwrap (ICMP.decode reassembled.payload)
      let quote ← unwrap (IPv4Quote.decode control.message.quote)
      ensure (quote.packet.payload.drop 8 == source.quote.packet.payload.drop 8 && reassembled.ttl == 63 && outcome.state == before)
        "Fragment reassembly must recover the complete translated ICMP error and its quoted application prefix."

private def untrustedQuoteTests : IO Unit := do
  let cached := entry true true
  let before : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
  let source ← receive cached.flow.reply.reverse cached.flow.reply.destination
  let corruptChecksum : InternetChecksum.Word :=
    ⟨(source.quote.checksum.val + 1) % 65536, Nat.mod_lt _ (by decide)⟩
  let corruptUDP := { source.quote with packet := { source.quote.packet with
    payload := source.quote.packet.payload.set 6 (source.quote.packet.payload[6]! + 1) } }
  let corruptLength := { source.quote with packet := { source.quote.packet with
    payload := (source.quote.packet.payload.set 4 0).set 5 0 } }
  for quote in [{ source.quote with checksum := corruptChecksum },
      { source.quote with declaredLength := 0 }, corruptUDP, corruptLength] do
    let received ← rewrap source quote
    let outcome ← run active before ⟨9, received⟩
    let output ← emission outcome
    let outer ← unwrap (IPv4Fragmentation.reassemble output.family.fragments)
    let control ← unwrap (ICMP.decode outer.payload)
    let restored ← unwrap (IPv4QuotePrefix.decode control.message.quote)
    ensure (outcome.disposition == .forwarded && outcome.state == before &&
        restored.declaredLength == quote.declaredLength && restored.flags == quote.flags &&
        restored.packet.payload.drop 8 == quote.packet.payload.drop 8 &&
        InternetChecksum.valid (IPv4QuotePrefix.headerBytes restored) ==
          InternetChecksum.valid (IPv4QuotePrefix.headerBytes quote))
      "Native association must accept untrusted inner checksums and lengths, preserving their checksum validity and metadata."
  let received ← rewrap source corruptUDP
  let output ← emission (← run active before ⟨9, received⟩)
  let restored := output.association.quote
  ensure ((match UDP.decode restored.packet.source restored.packet.destination restored.packet.payload with | .error _ => true | .ok _ => false))
    "RELATED NAT must not silently repair a corrupt quoted UDP checksum."
  for flags in ([16384, 24576, 49152, 57344] : List InternetChecksum.Word) do
    let quote := { source.quote with flags }
    let received ← rewrap source quote
    let outcome ← run active before ⟨9, received⟩
    ensure (outcome.disposition == .forwarded && (← emission outcome).association.quote.flags == flags)
      "Initial fragments, MF, and reserved flag bits must be preserved through related NAT."
  let received ← rewrap source { source.quote with flags := 16385 }
  let outcome ← run active before ⟨9, received⟩
  ensure (outcome.disposition == .unrelated && outcome.output.isNone && outcome.state == before)
    "A noninitial quotation fragment cannot be associated from its apparent port bytes."

private def inactiveNATTests : IO Unit := do
  let cached := entry false false
  let before : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
  let source ← receive cached.flow.reply.reverse cached.flow.reply.destination
  let source ← rewrap source { source.quote with checksum := 0 }
  let output ← emission (← run active before ⟨9, source⟩)
  ensure (IPv4QuotePrefix.bytes output.association.quote == IPv4QuotePrefix.bytes source.quote)
    "Inactive NAT status bits must preserve every quoted byte, including the raw zero IPv4 checksum representation."

def tests : IO Unit := do
  natTests
  associationTests
  policyTests
  ttlAndMTUTests
  untrustedQuoteTests
  inactiveNATTests

end NetlibTest.RelatedICMP
