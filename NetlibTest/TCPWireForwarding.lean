import Netlib.Protocol.TCP.WireForwarding

namespace NetlibTest.TCPWireForwarding

open Netlib Packet Protocol TCP.WireForwarding

private def original : Header := ⟨3221225986, 3405803778, Packet.Protocol.tcp, 32000, 8080⟩
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

example (input : TCP.DecodedIPv4) (emission : Emission input) :
    emission.decoded.segment.payload = input.segment.payload ∧
      emission.decoded.ip.packet.ttl.toNat = input.ip.packet.ttl.toNat - 1 ∧
      TCP.decodeIPv4 emission.bytes = .ok emission.decoded := ⟨emission.payload, emission.ttl, emission.decoded_eq⟩

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : TCP.encodeIPv4 input.packet = .ok bytes)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    ∃ outcome, step pipeline state input = .ok outcome := step_completes pipeline state input bytes encoded prepared attached model processed

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (existing : outcome.attachment.fresh = false) : outcome.state.model = state.model :=
  step_existing_model pipeline state input outcome accepted existing


example (source : Source) (emission : Emission source.packet) :
    TCP.ApplicationTrace.BytePath source.asInput emission.asInput := emission.bytePath source

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (source : Source)
    (zone : Nat) (candidate : Option NetfilterNAT.Entry)
    (value : Forwarded pipeline state source zone candidate) :
    value.emission.target = value.outcome.attachment.entry.flow.output value.outcome.attachment.direction := value.facts.1

example (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (source : Source) (same : input.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared) (outcome : Outcome input.packet)
    (computed : process pipeline input (by rw [same]; exact source.valid) prepared = .ok outcome) :
    step pipeline state input = .ok outcome :=
  step_of_process pipeline state input source.bytes (by rw [same]; exact source.encoded)
    (by rw [same]; exact source.valid) prepared attached outcome computed

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

private def packet (header : Header) (ttl : UInt8) (options : List UInt8 := []) : IO TCP.DecodedIPv4 := do
  let segment : TCP.Segment := TCP.rechecksum header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort
    sequence := TCP.Seq.ofNat 4294967295, acknowledgment := TCP.Seq.ofNat 12345
    reserved := 15, flags := 24, window := 65535, checksum := 0, urgentPointer := 77
    options := options, payload := payload }
  let ip : IPv4.Packet := ⟨184, 65535, true, ttl, header.protocol, header.source, header.destination, segment.encodeBytes⟩
  let bytes ← unwrap (IPv4.encode ip)
  unwrap (TCP.decodeIPv4 (bytes ++ [170, 187]))

private def output (outcome : Outcome input) : IO (Emission input) :=
  match outcome.output with
  | some emission => pure emission
  | none => throw (IO.userError "Expected a forwarded wire packet.")

private def forwardedTests : IO Unit := do
  for ttl in ([2, 64, 255] : List UInt8) do
    for options in [[], [253, 4, 170, 187]] do
      let input : Input := ⟨0, ← packet original ttl options, some entry⟩
      let result ← load (step permit ConntrackLifecycle.State.initial input)
      let emission ← output result
      ensure (result.disposition == .forwarded && result.state == unreplied && result.attachment.fresh &&
          result.afterDestination == translatedDestination && result.afterSource == some wire &&
          result.nextHop == some "outside" && result.lifecycle.isSome)
        "A fresh accepted packet must use DNAT before routing and SNAT before confirmation."
      ensure (emission.target == wire && emission.decoded.header == wire &&
          emission.decoded.segment.payload == payload && emission.decoded.ip.packet.ttl.toNat == ttl.toNat - 1 &&
          emission.decoded.ip.packet.tos == 184 && emission.decoded.ip.packet.identification == 65535 &&
          emission.decoded.ip.packet.dontFragment && emission.decoded.ip.padding.isEmpty)
        "The rewrite must preserve all payload bytes and IP metadata, decrease TTL once, and remove link padding."
      ensure (TCP.checksumAccepts emission.decoded.ip.packet.source emission.decoded.ip.packet.destination emission.decoded.segment &&
          (← unwrap (TCP.decodeIPv4 emission.bytes)) == emission.decoded &&
          (← unwrap (TCP.encodeIPv4 emission.decoded)) == emission.bytes)
        "The emitted TCP and IPv4 bytes must pass their mandatory checksum tests and exact codec round trips."
      ensure (emission.decoded.segment.sequence == input.packet.segment.sequence &&
          emission.decoded.segment.acknowledgment == input.packet.segment.acknowledgment &&
          emission.decoded.segment.flags == 24 && emission.decoded.segment.reserved == 15 &&
          emission.decoded.segment.window == 65535 && emission.decoded.segment.urgentPointer == 77 &&
          emission.decoded.segment.options == options)
        "The tuple rewrite must preserve the supplied TCP control fields and options."
      let checked ← unwrap (TCP.WireForwarding.source (← unwrap (TCP.encodeIPv4 input.packet)))
      ensure (checked.packet == input.packet && checked.asInput.bytes == checked.bytes &&
          emission.asInput.bytes == emission.bytes && emission.asSource.packet == emission.decoded)
        "The immutable source and endpoint adapters must retain their checked packet bytes."
      let cached : Input := { input with candidate := none }
      let repeated ← load (step permit result.state cached)
      ensure (!repeated.attachment.fresh && repeated.attachment.classification == .new &&
          repeated.state == result.state && (← output repeated).target == wire)
        "A cached unreplied original remains NEW and uses its stored NAT translation."

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
  let broken := { source with segment := { source.segment with destinationPort := 9001 } }
  match step permit ConntrackLifecycle.State.initial { input with packet := broken } with
  | .error (.input _) => pure ()
  | _ => throw (IO.userError "A fabricated TCP segment disagreement must fail before lifecycle processing.")
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


private def mandatoryZeroTests : IO Unit := do
  let header : Header := ⟨3221225985, 3325256706, Packet.Protocol.tcp, 12345, 80⟩
  let zeroSegment : TCP.Segment := TCP.rechecksum header.source header.destination {
    sourcePort := 12345, destinationPort := 80, sequence := TCP.Seq.ofNat 0, acknowledgment := TCP.Seq.ofNat 0
    reserved := 0, flags := 16, window := 4096, checksum := 0, urgentPointer := 0, options := [], payload := [131, 18] }
  ensure (zeroSegment.checksum == 0) "The selected TCP segment must have a computed checksum of zero."
  let identity : NetfilterNAT.Entry := ⟨⟨header, header.reverse, 0, 0, 0⟩, false, false⟩
  let pipeline : ConntrackLifecycle.Pipeline := {
    routes := [⟨⟨header.destination, 32⟩, some "outside"⟩]
    forward := [], forwardDefault := .permit, late := [], lateDefault := .permit }
  for checksum in ([0, 65535] : List InternetChecksum.Word) do
    let received := { zeroSegment with checksum := checksum }
    let ip : IPv4.Packet := ⟨0, 0, true, 64, Packet.Protocol.tcp, header.source, header.destination, received.encodeBytes⟩
    let bytes ← unwrap (IPv4.encode ip)
    let checked ← unwrap (TCP.WireForwarding.source bytes)
    ensure (checked.packet.segment.checksum == checksum)
      "The checked source must preserve the received checksum representation."
    let outcome ← load (step pipeline ConntrackLifecycle.State.initial ⟨0, checked.packet, some identity⟩)
    let emission ← output outcome
    ensure (emission.decoded.segment.checksum == 0 &&
        TCP.checksumAccepts emission.decoded.ip.packet.source emission.decoded.ip.packet.destination emission.decoded.segment)
      "A mandatory TCP checksum of zero must remain valid after forwarding."
    let corrupt := { checked.packet with segment := { checked.packet.segment with payload := [] } }
    match step pipeline ConntrackLifecycle.State.initial ⟨0, corrupt, some identity⟩ with
    | .error (.input _) => pure ()
    | _ => throw (IO.userError "A zero TCP checksum cannot permit unchecked replacement payload bytes.")

def run : IO Unit := do
  forwardedTests
  expiryTests
  dropTests
  errorTests
  mandatoryZeroTests
  IO.println "Tracked TCP wire forwarding tests passed."

end NetlibTest.TCPWireForwarding
