import Netlib.Protocol.WireForwarding

namespace NetlibTest.WireForwarding

open Netlib Packet Protocol Protocol.WireForwarding

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 32000, 8080⟩
private def aliasEndpoint : Endpoint := ⟨3405803777, 40000⟩
private def backend : Endpoint := ⟨3325256706, 9000⟩
private def wire : Header :=
  (Rewrite.sourceEndpoint aliasEndpoint).apply ((Rewrite.destinationEndpoint backend).apply original)
private def translatedDestination : Header := (Rewrite.destinationEndpoint backend).apply original
private def entry : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
private def unreplied : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
private def replied : ConntrackLifecycle.State := ⟨[⟨entry, true⟩]⟩

private def routes : List (Routing.Entry String) :=
  [⟨⟨backend.address, 32⟩, some "outside"⟩, ⟨⟨original.source, 32⟩, some "inside"⟩]

private def backendMatch : Match := {
  destination := some ⟨backend.address, 32⟩
  destinationPorts := some (PortRange.single backend.port) }

private def aliasMatch : Match := {
  source := some ⟨aliasEndpoint.address, 32⟩
  sourcePorts := some (PortRange.single aliasEndpoint.port) }

private def permit : ConntrackLifecycle.Pipeline :=
  ⟨routes, [⟨backendMatch, none, .permit⟩], .deny, [⟨aliasMatch, none, .permit⟩], .deny⟩

private def permitBoth : ConntrackLifecycle.Pipeline := {
  routes, forward := [], forwardDefault := .permit, late := [], lateDefault := .permit }

private def payload : List UInt8 := [0, 255, 0, 1, 17, 255, 69]

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (emission : Emission input.packet) (forwarded : outcome.output = some emission) :
    ∃ model, ConntrackLifecycle.step pipeline state input.lifecycle = .ok model ∧ model.output = some emission.target ∧
      outcome.afterDestination = model.afterDestination ∧ outcome.state = model.state ∧ outcome.lifecycle = some model ∧
        1 < input.packet.ip.packet.ttl.toNat := step_output pipeline state input outcome accepted emission forwarded

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (low : outcome.disposition = .ttlExpired) (fresh : outcome.attachment.fresh = true) :
    outcome.state = state ∧ outcome.output = none ∧ outcome.afterSource = none ∧ outcome.lifecycle = none :=
  ttlExpired_fresh pipeline state input outcome accepted low fresh

example (input : UDP.DecodedIPv4) (emission : Emission input) :
    emission.decoded.datagram.payload = input.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = input.ip.packet.ttl.toNat - 1 ∧
      UDP.decodeIPv4 emission.bytes = .ok emission.decoded := ⟨emission.payload, emission.ttl, emission.decoded_eq⟩

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 input.packet = .ok bytes)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    ∃ outcome, step pipeline state input = .ok outcome := step_completes pipeline state input bytes encoded prepared attached model processed

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (existing : outcome.attachment.fresh = false) : outcome.state.model = state.model :=
  step_existing_model pipeline state input outcome accepted existing

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

private def packet (header : Header) (ttl : UInt8) (omitted : Bool := false) : IO UDP.DecodedIPv4 := do
  let datagram : UDP.Datagram := if omitted then ⟨header.sourcePort, header.destinationPort, 0, payload⟩
    else UDP.computed header.source header.destination header.sourcePort header.destinationPort payload
  let transport ← unwrap (UDP.encode header.source header.destination datagram)
  let ip : IPv4.Packet := ⟨184, 65535, true, ttl, header.protocol, header.source, header.destination, transport⟩
  let bytes ← unwrap (IPv4.encode ip)
  unwrap (UDP.decodeIPv4 (bytes ++ [170, 187]))

private def output (outcome : Outcome input) : IO (Emission input) :=
  match outcome.output with
  | some emission => pure emission
  | none => throw (IO.userError "Expected a forwarded wire packet.")

private def forwardedTests : IO Unit := do
  for ttl in ([2, 64, 255] : List UInt8) do
    for omitted in [false, true] do
      let input : Input := ⟨0, ← packet original ttl omitted, some entry⟩
      let result ← load (step permit ConntrackLifecycle.State.initial input)
      let emission ← output result
      ensure (result.disposition == .forwarded && result.state == unreplied && result.attachment.fresh &&
          result.afterDestination == translatedDestination && result.afterSource == some wire &&
          result.nextHop == some "outside" && result.lifecycle.isSome)
        "A fresh accepted packet must use DNAT before routing and SNAT before confirmation."
      ensure (emission.target == wire && emission.decoded.header == wire &&
          emission.decoded.datagram.payload == payload && emission.decoded.ip.packet.ttl.toNat == ttl.toNat - 1 &&
          emission.decoded.ip.packet.tos == 184 && emission.decoded.ip.packet.identification == 65535 &&
          emission.decoded.ip.packet.dontFragment && emission.decoded.ip.padding.isEmpty)
        "Rewriting must preserve the complete binary payload and IP metadata, decrement TTL once, and omit link padding."
      ensure ((emission.decoded.datagram.checksum == 0) == omitted &&
          (← unwrap (UDP.decodeIPv4 emission.bytes)) == emission.decoded &&
          (← unwrap (UDP.encodeIPv4 emission.decoded)) == emission.bytes)
        "Emitted bytes must carry coherent checksums while preserving explicit UDP checksum omission."
      let cached : Input := { input with candidate := none }
      let repeated ← load (step permit result.state cached)
      ensure (!repeated.attachment.fresh && repeated.attachment.classification == .new &&
          repeated.state == result.state && (← output repeated).target == wire)
        "A cached unreplied original remains NEW and reuses its stored NAT translation."

private def expiryTests : IO Unit := do
  for ttl in ([0, 1] : List UInt8) do
    let input : Input := ⟨0, ← packet original ttl, some entry⟩
    for pipeline in [permit, { permit with forward := [], forwardDefault := .deny },
        { permit with late := [], lateDefault := .deny }] do
      let result ← load (step pipeline ConntrackLifecycle.State.initial input)
      ensure (result.disposition == .ttlExpired && result.state == ConntrackLifecycle.State.initial &&
          result.output.isNone && result.lifecycle.isNone && result.afterSource.isNone &&
          result.afterDestination == translatedDestination && result.nextHop == some "outside" && result.attachment.fresh)
        "Routed TTL0/1 must expire after destination NAT and before filters, source NAT, or fresh confirmation."
    let noRoute ← load (step { permit with routes := [] } ConntrackLifecycle.State.initial input)
    ensure (noRoute.disposition == .routeDrop && noRoute.lifecycle.isSome && noRoute.state == ConntrackLifecycle.State.initial)
      "Route failure must precede TTL expiry and retain the actual lifecycle route-drop outcome."
    let replyInput : Input := ⟨0, ← packet wire.reverse ttl, none⟩
    let reply ← load (step { permitBoth with forwardDefault := .deny } unreplied replyInput)
    ensure (reply.disposition == .ttlExpired && reply.state == replied && reply.output.isNone &&
        reply.attachment.direction == .reply && reply.attachment.classification == .established &&
        !reply.attachment.fresh && reply.afterSource.isNone && reply.nextHop == some "inside")
      "A valid first reply must retain seen-reply even when it expires before forward filtering."
    let originalInput : Input := ⟨0, ← packet original 64, none⟩
    let retained ← load (step { permitBoth with forward := [ConntrackLifecycle.establishedPermit], forwardDefault := .deny }
      reply.state originalInput)
    ensure (retained.attachment.classification == .established && (← output retained).target == wire)
      "TTL-expired reply observation must affect later classification without emitting its payload."

private def dropTests : IO Unit := do
  let input : Input := ⟨0, ← packet original 64, some entry⟩
  let blocked ← load (step { permit with forward := [] } ConntrackLifecycle.State.initial input)
  ensure (blocked.disposition == .forwardDrop && blocked.state == ConntrackLifecycle.State.initial &&
      blocked.output.isNone && blocked.afterSource.isNone && blocked.lifecycle.isSome)
    "Forward-filter denial must remain an actual lifecycle drop with no fresh confirmation."
  let late ← load (step { permit with late := [] } ConntrackLifecycle.State.initial input)
  ensure (late.disposition == .lateDrop && late.state == ConntrackLifecycle.State.initial &&
      late.output.isNone && late.afterSource == some wire && late.lifecycle.isSome)
    "A late denial must expose translated header evidence without producing wire bytes."
  let replyInput : Input := ⟨0, ← packet wire.reverse 64, none⟩
  let reply ← load (step permitBoth unreplied replyInput)
  ensure (reply.state == replied && (← output reply).target == original.reverse && reply.nextHop == some "inside")
    "Reply NAT must restore endpoints before serializing the actual reply payload."
  let droppedReply ← load (step { permitBoth with routes := [] } unreplied replyInput)
  ensure (droppedReply.disposition == .routeDrop && droppedReply.state == replied && droppedReply.output.isNone)
    "Seen-reply attachment updates must also survive route failure."

private def errorTests : IO Unit := do
  let source ← packet original 1
  let missing : Input := ⟨0, source, none⟩
  match step permit ConntrackLifecycle.State.initial missing with
  | .error (.lifecycle .missingCandidate) => pure ()
  | _ => throw (IO.userError "TTL expiry must not bypass conntrack attachment or candidate validation.")
  let input : Input := ⟨0, source, some entry⟩
  let broken := { source with datagram := { source.datagram with destinationPort := 9001 } }
  match step permit ConntrackLifecycle.State.initial { input with packet := broken } with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "A fabricated Header/datagram disagreement must fail before lifecycle processing.")
  let corrupted := { source with ip := { source.ip with checksum := source.ip.checksum + 1 } }
  match step permit ConntrackLifecycle.State.initial { input with packet := corrupted } with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "An invalid input IPv4 checksum must not enter the tracked lifecycle.")
  let collision : NetfilterNAT.Entry := { entry with flow := { entry.flow with
    original := { original with sourcePort := 32001 } } }
  let low : Input := ⟨0, ← packet collision.flow.original 1, some collision⟩
  let expired ← load (step permit unreplied low)
  ensure (expired.disposition == .ttlExpired && expired.state == unreplied && expired.output.isNone)
    "A TTL-expired unconfirmed candidate must not reach the confirmation collision check."
  let high : Input := { low with packet := ← packet collision.flow.original 2 }
  match step permit unreplied high with
  | .error (.lifecycle .confirmationCollision) => pure ()
  | _ => throw (IO.userError "A forwarded candidate must still undergo ordinary confirmation collision checks.")
  match step permit unreplied { input with candidate := some entry } with
  | .error (.lifecycle .unexpectedCandidate) => pure ()
  | _ => throw (IO.userError "Low TTL cannot replace an existing cached binding.")

def run : IO Unit := do
  forwardedTests
  expiryTests
  dropTests
  errorTests
  IO.println "Tracked UDP wire forwarding tests passed."

end NetlibTest.WireForwarding
