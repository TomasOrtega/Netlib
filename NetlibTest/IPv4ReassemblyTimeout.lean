import Netlib.Protocol.IPv4ReassemblyTimeout

namespace NetlibTest.IPv4ReassemblyTimeout

open Netlib Packet Protocol
open Protocol.IPv4Reassembly Protocol.IPv4ReassemblyTimeout

private def domain : Domain := ⟨65536, 0⟩
private def first (size : Nat := 576) (df : Bool := false) : IPv4Fragment.Decoded :=
  let payload := (List.range size).map UInt8.ofNat
  let packet : IPv4Fragment.Packet :=
    ⟨⟨0, 41229, df, 64, Packet.Protocol.udp, 3221225986, 3405803778, payload⟩, true, 0⟩
  ⟨packet, IPv4Fragment.computedChecksum packet, []⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def queued (fragment : IPv4Fragment.Decoded) : IO State :=
  match arrive ⟨30⟩ State.initial 10 domain fragment with
  | .ok result => pure result.state
  | .error error => throw (IO.userError error.describe)

private def emission (queue : Queue) (mtu : IPv4Fragmentation.MTU) : IO (Emission queue) := do
  let some selected := source queue | throw (IO.userError "Expected a stored offset-zero UDP fragment.")
  pure ⟨selected, ⟨"peer", selected.piece.fragment.packet.destination, mtu, 64⟩, 73⟩

example (state : State) (now : Nat) (queue : Queue) (expired : queue ∈ expiredQueues state now) :
    queue ∉ (state.age now).queues := expiredQueues_removed _ _ _ expired

example (output : Emission queue) :
    IPv4QuotePrefix.decode output.message.quote = .ok output.quote := output.quoted_decoded

example (output : Emission queue) :
    output.packet.wireLength ≤ output.path.mtu.val ∧ output.packet.wireLength ≤ 576 := output.fits

example (selected : IPv4ReassemblyTimeout.Context) (tracker : ConntrackLifecycle.State) (before : State)
    (now : Nat) (identification : Queue → InternetChecksum.Word) (result : IPv4ReassemblyTimeout.Result)
    (computed : expire selected tracker before now identification = .ok result)
    (valid : before.Valid) (layout : before.LayoutValid) :
    result.state.Valid ∧ result.state.LayoutValid ∧ expiredQueues result.state now = [] :=
  ⟨expire_valid _ _ _ _ _ _ computed valid, expire_layout _ _ _ _ _ _ computed layout,
    expire_no_repeat _ _ _ _ _ _ computed⟩

private def quotationTests : IO Unit := do
  for size in [8, 11, 48, 576, 1200] do
    for df in [false, true] do
      let fragment := first size df
      let state ← queued fragment
      ensure ((expiredQueues state 39).isEmpty && (expiredQueues state 40).length == 1 &&
          (state.age 40).queues.isEmpty)
        "Only an expired queue may be selected, and expiry must remove it at its deadline."
      for queue in expiredQueues state 40 do
        for mtu in ([⟨68, by decide⟩, ⟨600, by decide⟩, ⟨4096, by decide⟩] : List IPv4Fragmentation.MTU) do
          let output ← emission queue mtu
          let decoded ← unwrap (IPv4.decode output.bytes)
          let control ← unwrap (ICMP.decode decoded.packet.payload)
          let quote ← unwrap (IPv4QuotePrefix.decode control.message.quote)
          ensure ((match IPv4Quote.decode control.message.quote with | .error _ => true | .ok _ => false))
            "A timeout quote with MF set must use the permissive prefix parser rather than a complete-datagram quotation parser."
          let retained :=  IPv4Fragment.headerBytes fragment.packet fragment.checksum ++
            fragment.packet.payload.take (size / 8 * 8)
          ensure (control.message.kind == .reassemblyTimeout && control.message.quote == retained.take output.length &&
              quote.flags == IPv4Fragment.flagsWord fragment.packet &&
              quote.declaredLength == IPv4Fragment.lengthWord fragment.packet && quote.packet.ttl == 64 &&
              quote.checksum == fragment.checksum && quote.packet.payload.length ≤ size / 8 * 8)
            "Timeout quotations must retain the original first-fragment header while exposing only normalized stored data."
          ensure (decoded.packet.source == fragment.packet.destination && decoded.packet.destination == fragment.packet.source &&
              decoded.packet.ttl == 64 && decoded.packet.tos == 192 && !decoded.packet.dontFragment &&
              decoded.packet.wireLength ≤ mtu.val && decoded.packet.wireLength ≤ 576 &&
              InternetChecksum.valid decoded.packet.payload && InternetChecksum.valid (IPv4QuotePrefix.headerBytes quote))
            "The selected local return path must produce valid bounded IPv4 and ICMP code-one output."
          if size == 576 && mtu.val == 4096 then
            ensure (output.packet.wireLength == 576 && control.message.quote.length == 548 &&
                quote.declaredLength.val == 596 && quote.flags.val == (if df then 24576 else 8192))
              "The native-sized case must quote 548 of the original 596-byte MF fragment."
          if size == 11 then
            ensure (quote.packet.payload == fragment.packet.payload.take 8 && output.packet.wireLength == 56)
              "Odd MF bytes trimmed on ingress must never reappear in a timeout quotation."

private def missingFirstTests : IO Unit := do
  let packet := (first 8).packet
  let noninitial := { packet with offset := 1 }
  let state ← queued ⟨noninitial, IPv4Fragment.computedChecksum noninitial, []⟩
  for queue in expiredQueues state 40 do
    ensure ((firstPiece queue).isNone && (source queue).isNone)
      "An expired queue without its offset-zero fragment must not supply a timeout quotation."

private def context : IPv4ReassemblyTimeout.Context := {
  inputRouteLocal := fun _ => some true
  requiresLocal := fun _ => true
  returnPath := fun packet => some ⟨"peer", packet.destination, ⟨4096, by decide⟩, 64⟩
  zone := fun _ => 0
  output := [⟨{ protocol := some Packet.Protocol.icmp }, some [.invalid], .permit⟩] }

private def expiration (context : IPv4ReassemblyTimeout.Context) (tracker : ConntrackLifecycle.State)
    (state : State) (now : Nat) : IO IPv4ReassemblyTimeout.Result :=
  match expire context tracker state now (fun queue => queue.key.identification) with
  | .ok result => pure result
  | .error error => throw (IO.userError error.describe)

private def generationTests : IO Unit := do
  let fragment := first
  let state ← queued fragment
  let some queue := state.queues.head? | throw (IO.userError "Expected an incomplete queue.")
  let before ← expiration context .initial state 39
  ensure (before.findings.isEmpty && before.state.queues == state.queues)
    "A wait before the deadline must retain its queue and emit no timeout."
  let completed ← expiration context .initial state 40
  let some finding := completed.findings.head? | throw (IO.userError "Expected an expired queue finding.")
  ensure (completed.state.queues.isEmpty && completed.conntrack == ConntrackLifecycle.State.initial &&
      finding.control.disposition == .sent && finding.control.classification == some .invalid && finding.control.output.isSome)
    "A local conntrack-input expiry with a reverse-quote miss must use the explicit INVALID output policy."
  ensure ((← expiration context completed.conntrack completed.state 41).findings.isEmpty)
    "An expired queue must not emit a second timeout after removal."
  for (changed, disposition) in [
      ({ context with inputRouteLocal := fun _ => none }, Disposition.noInputRoute),
      ({ context with inputRouteLocal := fun _ => some false }, .suppressed),
      ({ context with returnPath := fun _ => none }, .noReturnRoute),
      ({ context with linkGroup := fun _ => true }, .suppressed),
      ({ context with output := [] }, .outputDrop),
      ({ context with output := [⟨{}, some [.related], .permit⟩] }, .outputDrop),
      ({ context with lateDefault := .deny }, .lateDrop),
      ({ context with zone := fun _ => 65536 }, .unsupportedZone)] do
    let result := generate changed ConntrackLifecycle.State.initial queue 40 73
    ensure (result.disposition == disposition && result.output.isNone)
      "Timeout output must obey input routing, locality, return routing, address, zone, and explicit INVALID policy guards."
  let nonlocalUser := { context with inputRouteLocal := fun _ => some false, requiresLocal := fun _ => false }
  ensure ((generate nonlocalUser .initial queue 40 73).output.isSome)
    "The local-destination restriction must follow the selected defragmentation user policy."
  let packet ← emission queue ⟨4096, by decide⟩
  let original := IPv4QuotePrefix.header packet.quote
  let wire := { original with source := 3405803777, destination := 3325256706, sourcePort := 40000, destinationPort := 9000 }
  let nated : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
  let tracker : ConntrackLifecycle.State := ⟨[⟨nated, true⟩]⟩
  let retained ← expiration context tracker state 40
  ensure (retained.conntrack == tracker && retained.findings.all (fun row => row.control.disposition == .sent))
    "An existing NATed UDP flow must remain unchanged when the pre-DNAT timeout quote has no reverse-key association."
  let unmodified : NetfilterNAT.Entry := ⟨⟨original, original.reverse, 0, 0, 0⟩, false, false⟩
  let associated : ConntrackLifecycle.State := ⟨[⟨unmodified, false⟩]⟩
  let unsupported := generate context associated queue 40 73
  ensure (unsupported.disposition == .unsupportedAssociation && unsupported.output.isNone)
    "A reverse-quote hit must leave the selected unassociated timeout profile instead of assuming no NAT."
  let altered := { fragment.packet with identification := 41230 }
  let second := ⟨altered, IPv4Fragment.computedChecksum altered, []⟩
  let both ← match arrive ⟨30⟩ state 10 domain second with
    | .ok result => pure result.state
    | .error error => throw (IO.userError error.describe)
  let expired ← expiration context tracker both 40
  ensure (expired.findings.length == 2 && expired.state.queues.isEmpty && expired.conntrack == tracker &&
      expired.findings.all (fun row => row.control.output.isSome))
    "Each expired key must produce its own guarded timeout without creating fragment or UDP tracking records."
  match expire context tracker state 9 (fun _ => 73) with
  | .error .backwardsClock => pure ()
  | _ => throw (IO.userError "Backwards expiry clocks must be rejected.")

def run : IO Unit := do
  quotationTests
  missingFirstTests
  generationTests
  IO.println "IPv4 reassembly timeout quotation tests passed."

end NetlibTest.IPv4ReassemblyTimeout
