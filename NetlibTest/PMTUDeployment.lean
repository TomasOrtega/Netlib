import Netlib.Examples.PMTUDeployment

namespace NetlibTest.PMTUDeployment

open Netlib Packet Protocol Examples.PMTUDeployment

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 41000, 8080⟩
private def wire : Header := ⟨3405803777, 3325256706, Packet.Protocol.udp, 40000, 9000⟩
private def router : Address := 3325256705
private def attacker : Address := 3405803779
private def cached : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 7, 9, 0⟩, true, true⟩
private def tracker : ConntrackLifecycle.State := ⟨[⟨cached, false⟩]⟩
private def related : StatefulACL.Rule := ⟨{}, some [.related], .permit⟩
private def active : RelatedICMP.Pipeline :=
  ⟨⟨[⟨⟨0, 0⟩, some "inside"⟩], [related], .deny, [related], .deny⟩,
    fun _ => ⟨68, by decide⟩⟩
private def policy : PMTU.Policy := ⟨⟨552, by decide⟩, 600⟩
private def route : PMTU.Route := ⟨⟨4096, by decide⟩, false⟩
private def empty : PMTU.State := ⟨none⟩

example (input : RelatedICMP.Input) (outcome : RelatedICMP.Outcome tracker input)
    (accepted : RelatedICMP.step active tracker input = .ok outcome)
    (emission : RelatedICMP.Emission tracker input) (emitted : outcome.output = some emission)
    (socket : Header)
    (selected : socket = emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction))
    (kind : input.source.icmp.message.kind = .fragmentationNeeded 600) :
    outcome.state = tracker ∧ ∃ result,
      receive policy route socket empty 100 (deliveredSource emission) = some result ∧
      result.state.Valid route ∧ (result.state.current route 100).val = 600 ∧
      (result.state.current route 100).val < (empty.current route 100).val :=
  step_delivers_reduction _ _ _ _ accepted _ emitted _ _ _ _ _ _ selected kind
    (PMTU.State.valid_initial route) (by decide) (by decide) (by decide) (by decide)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def source (quoteSize : Nat) (badIP badUDP : Bool) (advertised : InternetChecksum.Word := 600)
    (reporter : Address := router) (kind : Option ICMP.Kind := none) : IO RelatedICMP.Source := do
  let payload := (List.range 100).map (fun value => UInt8.ofNat (value * 17))
  let datagram := UDP.computed wire.source wire.destination wire.sourcePort wire.destinationPort payload
  let transport ← unwrap (UDP.encode wire.source wire.destination datagram)
  let quoted := if badUDP then transport.set 6 (transport[6]! + 1) else transport
  let ip : IPv4.Packet := ⟨185, 1234, true, 63, Packet.Protocol.udp, wire.source, wire.destination, quoted⟩
  let checksum := IPv4.computedChecksum ip
  let corrupt : InternetChecksum.Word := ⟨(checksum.val + 1) % 65536, Nat.mod_lt _ (by decide)⟩
  let quote := IPv4.headerBytes ip (if badIP then corrupt else checksum) ++ quoted.take quoteSize
  let message : ICMP.Message := ⟨kind.getD (.fragmentationNeeded advertised), quote⟩
  let outer : IPv4.Packet := ⟨192, 4321, false, 64, Packet.Protocol.icmp, reporter, wire.source, ICMP.encode message⟩
  RelatedICMP.decode (← unwrap (IPv4.encode outer)) |> unwrap

private def transit (input : RelatedICMP.Input) : IO (RelatedICMP.Outcome tracker input) :=
  match RelatedICMP.step active tracker input with
  | .ok value => pure value
  | .error error => throw (IO.userError error.describe)

private def output (outcome : RelatedICMP.Outcome tracker input) : IO (RelatedICMP.Emission tracker input) :=
  match outcome.output with
  | some emission => pure emission
  | none => throw (IO.userError "Expected a RELATED gateway emission.")

private def hostUpdate (before : PMTU.State) (now : Nat) (source : RelatedICMP.Source) : IO PMTU.Result :=
  match receive policy route original before now source with
  | some result => pure result
  | none => throw (IO.userError "Expected translated feedback for the connected UDP sender.")

private def compositionTests : IO Unit := do
  for quoteSize in [8, 9, 107, 108] do
    for badIP in [false, true] do
      for badUDP in [false, true] do
        let incoming ← source quoteSize badIP badUDP
        ensure (IPv4QuotePrefix.header incoming.quote == wire && incoming.quote.packet.ttl == 63 &&
            InternetChecksum.valid (IPv4QuotePrefix.headerBytes incoming.quote) == !badIP)
          "The received quote must contain the wire tuple and the already decremented TTL."
        let input : RelatedICMP.Input := ⟨9, incoming⟩
        let outcome ← transit input
        let emission ← output outcome
        let reassembled ← unwrap (IPv4Fragmentation.reassemble emission.family.fragments.reverse)
        let bytes ← unwrap (IPv4.encode reassembled)
        let delivered ← unwrap (RelatedICMP.decode bytes)
        ensure (outcome.disposition == .forwarded && outcome.state == tracker &&
            emission.association.direction == .reply && !emission.association.record.seenReply &&
            delivered.bytes == (deliveredSource emission).bytes &&
            IPv4QuotePrefix.header delivered.quote == original && delivered.quote.packet.ttl == 63 &&
            reassembled.ttl == 63 && reassembled.destination == original.source &&
            reassembled.source == original.destination)
          "Actual RELATED NAT and reassembly must restore the sender tuple while leaving conntrack and quoted TTL unchanged."
        ensure (emission.family.fragments.all (fun part => decide (part.packet.wireLength ≤ 68)) &&
            (emission.family.fragments.length > 1) == (quoteSize > 20) &&
            delivered.quote.packet.payload.drop 8 == incoming.quote.packet.payload.drop 8 &&
            InternetChecksum.valid (IPv4QuotePrefix.headerBytes delivered.quote) == !badIP)
          "Fragmentation must preserve the untrusted quote prefix and its IP checksum validity."
        if quoteSize == 108 then
          ensure ((match UDP.decode delivered.quote.packet.source delivered.quote.packet.destination
              delivered.quote.packet.payload with | .ok _ => true | .error _ => false) == !badUDP)
            "A complete corrupt UDP quote must remain corrupt after NAT."
        let updated ← hostUpdate empty 100 delivered
        ensure (updated.disposition == .updated && (updated.state.current route 100).val == 600 &&
            PMTU.send route updated.state 101 true 1200 == .messageSize &&
            PMTU.send route updated.state 101 true 500 == .accepted)
          "The delivered wire error must update the sender cache and govern subsequent drained-error DF sends."

private def forgeryTests : IO Unit := do
  let first ← source 108 false false
  let firstOutcome ← transit ⟨9, first⟩
  let firstEmission ← output firstOutcome
  let firstState ← hostUpdate empty 100 (deliveredSource firstEmission)
  let forged ← source 9 true true 576 attacker
  let forgedOutcome ← transit ⟨9, forged⟩
  let forgedEmission ← output forgedOutcome
  let reassembled ← unwrap (IPv4Fragmentation.reassemble forgedEmission.family.fragments)
  let delivered ← unwrap (RelatedICMP.decode (← unwrap (IPv4.encode reassembled)))
  let reduced ← hostUpdate firstState.state 101 delivered
  ensure (forged.ip.packet.source == attacker && forgedOutcome.state == tracker &&
      reduced.disposition == .updated && (reduced.state.current route 101).val == 576 &&
      PMTU.send route reduced.state 102 true 548 == .accepted &&
      PMTU.send route reduced.state 102 true 549 == .messageSize)
    "A forged matching quote can traverse RELATED NAT and reduce an existing sender cache."
  let ordinary ← source 9 true true 576 router
  let ordinaryEmission ← output (← transit ⟨9, ordinary⟩)
  let same ← hostUpdate firstState.state 101 (deliveredSource ordinaryEmission)
  ensure (same == reduced)
    "Changing the incoming reporter cannot authenticate otherwise identical matching feedback."

private def guardTests : IO Unit := do
  let exceeded ← source 9 false false 600 router (some .timeExceeded)
  let emitted ← output (← transit ⟨9, exceeded⟩)
  ensure ((receive policy route original empty 100 (deliveredSource emitted)).isNone)
    "RELATED Time Exceeded forwarding must not alter the host PMTU cache."
  let incoming ← source 9 false false
  let unrelated ← transit ⟨7, incoming⟩
  ensure (unrelated.disposition == .unrelated && unrelated.output.isNone && unrelated.state == tracker)
    "The wrong conntrack zone must prevent delivery of a translated host quote."
  let emission ← output (← transit ⟨9, incoming⟩)
  ensure ((receive policy route { original with sourcePort := 41001 } empty 100
      (deliveredSource emission)).isNone)
    "A delivered quotation for another socket must not update this sender's PMTU."

def run : IO Unit := do
  compositionTests
  forgeryTests
  guardTests
  IO.println "RELATED gateway to host PMTU deployment tests passed."

end NetlibTest.PMTUDeployment
