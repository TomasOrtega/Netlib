import Netlib.Protocol.TCP.HandshakeExchange

namespace NetlibTest.TCPHandshake

open Netlib Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def transition : Except Handshake.Failure α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def failure (result : Except Handshake.Failure α) (expected : Handshake.Failure) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError "The startup operation must fail.")
  | .error reason => ensure (reason == expected) "The startup failure reason is incorrect."

private def config (address : Packet.Address) (port : Packet.Port) (iss capacity : Nat)
    (ipLimit : Nat := 1500) : Handshake.Local :=
  ⟨⟨address, port⟩, Seq.ofNat iss, capacity, 8, ipLimit, none⟩

private def checked (header : Packet.Header) (sequence acknowledgment : Seq) (flags : UInt8)
    (window : InternetChecksum.Word := 65535) (options payload : List UInt8 := []) : IO EstablishedReceive.Input := do
  let segment := computed header.source header.destination {
    sourcePort := header.sourcePort, destinationPort := header.destinationPort,
    sequence, acknowledgment, reserved := 0, flags, window, checksum := 0, urgentPointer := 0, options, payload }
  let bytes ← load (IPv4.encode ⟨0, 42, true, 64, Packet.Protocol.tcp,
    header.source, header.destination, segment.encodeBytes⟩)
  load (EstablishedReceive.input bytes)

private def exchange (activeISS passiveISS activeCapacity passiveCapacity ipLimit : Nat) : IO Unit := do
  let active := config 3221225985 41000 activeISS activeCapacity ipLimit
  let passive := config 3325256706 8080 passiveISS passiveCapacity ipLimit
  let pendingActive ← transition (Handshake.activeOpen active passive.socket true)
  ensure (pendingActive.output.packet.header == Handshake.outbound active passive.socket &&
      pendingActive.output.packet.segment.sequence == active.iss &&
      pendingActive.output.packet.segment.flags == 2 && pendingActive.output.packet.segment.payload.isEmpty &&
      pendingActive.output.packet.segment.window.val == active.capacity)
    "Active OPEN must produce the actual local SYN and its control position."
  let pendingPassive ← transition (Handshake.listenSyn passive pendingActive.output true)
  ensure (pendingPassive.input.packet.segment.sequence == active.iss &&
      pendingPassive.output.packet.segment.sequence == passive.iss &&
      pendingPassive.output.packet.segment.acknowledgment == active.iss.add 1 &&
      pendingPassive.output.packet.segment.flags == 18)
    "The passive pending phase must retain the received SYN and generated SYN,ACK."
  let activeResult ← transition (Handshake.synSentSynAck pendingActive pendingPassive.output true)
  ensure (activeResult.seed.core.receiveNext == passive.iss.add 1 &&
      activeResult.seed.core.sendUna == active.iss.add 1 && activeResult.seed.core.sendNext == active.iss.add 1 &&
      activeResult.seed.sendWindow == passive.capacity && activeResult.seed.sendWL1 == passive.iss &&
      activeResult.seed.sendWL2 == active.iss.add 1 && activeResult.seed.core.capacity == active.capacity &&
      activeResult.seed.core.sent.isEmpty && activeResult.seed.core.received.isEmpty && activeResult.seed.pending.isEmpty &&
      decide activeResult.seed.Valid)
    "Active establishment must derive empty application storage, cursors, and peer history from the checked SYN,ACK."
  ensure (activeResult.seed.effectiveMSS == min 536 (ipLimit - 40) &&
      activeResult.output.packet.segment.sequence == active.iss.add 1 &&
      activeResult.output.packet.segment.acknowledgment == passive.iss.add 1 &&
      activeResult.output.packet.segment.window.val == activeCapacity && activeResult.output.packet.segment.flags == 16)
    "The final ACK must use the newly derived active seed."
  let passiveResult ← transition (Handshake.synReceivedAck pendingPassive activeResult.output)
  ensure (passiveResult.seed.core.receiveNext == active.iss.add 1 &&
      passiveResult.seed.core.sendUna == passive.iss.add 1 && passiveResult.seed.core.sendNext == passive.iss.add 1 &&
      passiveResult.seed.sendWindow == active.capacity && passiveResult.seed.sendWL1 == active.iss.add 1 &&
      passiveResult.seed.sendWL2 == passive.iss.add 1 && passiveResult.seed.effectiveMSS == min 536 (ipLimit - 40) &&
      passiveResult.seed.core.capacity == passive.capacity && passiveResult.seed.core.sent.isEmpty &&
      passiveResult.seed.core.received.isEmpty && passiveResult.seed.pending.isEmpty && decide passiveResult.seed.Valid)
    "Only final ACK receipt must derive the passive application seed and current peer window."
  for output in [pendingActive.output, pendingPassive.output, activeResult.output] do
    let decoded ← load (EstablishedReceive.input output.bytes)
    ensure (decoded.packet == output.packet && output.bytes.length == 40 && output.packet.segment.options.isEmpty &&
      output.packet.segment.payload.isEmpty && checksumAccepts output.packet.ip.packet.source
        output.packet.ip.packet.destination output.packet.segment)
      "Each startup output must decode with its exact fields and mandatory checksum."

private def rejectedInputs : IO Unit := do
  let active := config 3221225985 41000 4294967295 0 576
  let passive := config 3325256706 8080 4294967295 0 576
  failure (Handshake.activeOpen { active with ipSendLimit := 40 } passive.socket true) (.reject .invalidConfig)
  failure (Handshake.activeOpen { active with capacity := 65536 } passive.socket true) (.reject .invalidConfig)
  failure (Handshake.activeOpen active passive.socket false) (.reject .policy)
  let pendingActive ← transition (Handshake.activeOpen active passive.socket true)
  failure (Handshake.listenSyn passive pendingActive.output false) (.reject .policy)
  let pendingPassive ← transition (Handshake.listenSyn passive pendingActive.output true)
  failure (Handshake.synSentSynAck pendingActive pendingPassive.output false) (.reject .policy)
  let inbound := Handshake.inbound active passive.socket
  let badAck ← checked inbound passive.iss active.iss 18 0
  failure (Handshake.synSentSynAck pendingActive badAck true) (.unsupported .acknowledgment)
  let wrongTuple ← checked { inbound with destinationPort := 41001 } passive.iss (active.iss.add 1) 18 0
  failure (Handshake.synSentSynAck pendingActive wrongTuple true) (.reject .tuple)
  let wrongDestination ← checked { (Handshake.outbound active passive.socket) with destinationPort := 8081 }
    active.iss (Seq.ofNat 0) 2
  failure (Handshake.listenSyn passive wrongDestination true) (.reject .tuple)
  for (flags, options, payload, reason) in [
      (4, [], [], Handshake.Unsupported.flags),
      (2, [], [], .flags),
      (18, [30, 4, 5, 180], [], .options),
      (18, [], [42], .data)] do
    let packet ← checked inbound passive.iss (active.iss.add 1) flags 0 options payload
    failure (Handshake.synSentSynAck pendingActive packet true) (.unsupported reason)
  for options in [[2, 4, 3, 32], [1, 1, 1, 1], [0, 0, 0, 0]] do
    let withData ← checked inbound passive.iss (active.iss.add 1) 18 0 options [42]
    failure (Handshake.synSentSynAck pendingActive withData true) (.unsupported .data)
    let wrongFlags ← checked inbound passive.iss (active.iss.add 1) 2 0 options
    failure (Handshake.synSentSynAck pendingActive wrongFlags true) (.unsupported .flags)
  let synData ← checked (Handshake.outbound active passive.socket) active.iss (Seq.ofNat 0) 2 0 [] [42]
  failure (Handshake.listenSyn passive synData true) (.unsupported .data)
  let activeResult ← transition (Handshake.synSentSynAck pendingActive pendingPassive.output true)
  let wrongSequence ← checked (Handshake.outbound active passive.socket) active.iss (passive.iss.add 1) 16 0
  failure (Handshake.synReceivedAck pendingPassive wrongSequence) (.unsupported .sequence)
  let wrongFinalAck ← checked (Handshake.outbound active passive.socket) (active.iss.add 1) passive.iss 16 0
  failure (Handshake.synReceivedAck pendingPassive wrongFinalAck) (.unsupported .acknowledgment)
  let passiveResult ← transition (Handshake.synReceivedAck pendingPassive activeResult.output)
  ensure (passiveResult.seed.sendWindow == 0 && passiveResult.seed.core.receiveNext.val == 0)
    "A correct final ACK must establish the passive endpoint with a zero window across sequence wrap."
  let corrupt := match pendingActive.output.bytes with | _ :: tail => (68 : UInt8) :: tail | [] => []
  match EstablishedReceive.input corrupt with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Corrupted startup bytes must fail before a handshake transition.")

private def passiveWindowSource : IO Unit := do
  let active := config 3221225985 41000 100 8
  let passive := config 3325256706 8080 200 4
  let pendingActive ← transition (Handshake.activeOpen active passive.socket true)
  let pendingPassive ← transition (Handshake.listenSyn passive pendingActive.output true)
  let finalAck ← checked (Handshake.outbound active passive.socket) (active.iss.add 1) (passive.iss.add 1) 16 3
  let result ← transition (Handshake.synReceivedAck pendingPassive finalAck)
  ensure (pendingPassive.input.packet.segment.window.val == 8 && result.seed.sendWindow == 3 &&
      result.seed.sendWL1 == active.iss.add 1 && result.seed.sendWL2 == passive.iss.add 1 &&
      result.seed.core.capacity == 4 && result.seed.effectiveMSS == 536)
    "The passive peer window must come from the final ACK. The startup MSS source remains the initial SYN."
  let optionAck ← checked (Handshake.outbound active passive.socket) (active.iss.add 1) (passive.iss.add 1) 16 3 [2, 4, 5, 180]
  failure (Handshake.synReceivedAck pendingPassive optionAck) (.unsupported .options)

private def advertisement (receiveLimit value : Nat) : IO MSS.Advertisement := do
  let value ← match MSS.Value.ofNat value with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason.message)
  match MSS.Advertisement.make receiveLimit value with
  | .ok evidence => pure evidence
  | .error reason => throw (IO.userError reason.message)

private def directionalMSS : IO Unit := do
  let clientReceive ← advertisement 1240 1200
  let serverReceive ← advertisement 840 800
  let active := { config 3221225985 41000 99 0 1000 with receiveMSS := some clientReceive }
  let passive := { config 3325256706 8080 199 0 1500 with receiveMSS := some serverReceive }
  let opened ← transition (Handshake.activeOpen active passive.socket true)
  let listened ← transition (Handshake.listenSyn passive opened.output true)
  let established ← transition (Handshake.synSentSynAck opened listened.output true)
  let accepted ← transition (Handshake.synReceivedAck listened established.output)
  ensure (opened.output.bytes.length == 44 && listened.output.bytes.length == 44 && established.output.bytes.length == 40 &&
    established.output.packet.segment.options.isEmpty &&
    established.seed.effectiveMSS == 800 && accepted.seed.effectiveMSS == 1200 &&
    established.peerMSS.limit == 800 && listened.peerMSS.limit == 1200 &&
    established.seed.core.capacity == 0 && accepted.seed.core.capacity == 0)
    "Each endpoint must send at the peer's actual MSS, independent of its own receive capability and window."
  let finalAck ← checked (Handshake.outbound active passive.socket) (active.iss.add 1) (passive.iss.add 1) 16 3
  let passiveUpdated ← transition (Handshake.synReceivedAck listened finalAck)
  ensure (passiveUpdated.seed.sendWindow == 3 && passiveUpdated.seed.effectiveMSS == 1200)
    "The final ACK must update the passive peer window while retaining MSS from the initial SYN."
  let forward : Packet.Header := { (Handshake.outbound active passive.socket) with source := 3405803777, sourcePort := 40000 }
  let syn := HandshakeExchange.Delivery.rewritten opened.output forward 63 rfl
  let rewrittenPassive ← transition (Handshake.listenSyn passive syn.input true)
  let synAck := HandshakeExchange.Delivery.rewritten rewrittenPassive.output (Handshake.inbound active passive.socket) 63 rfl
  let rewrittenActive ← transition (Handshake.synSentSynAck opened synAck.input true)
  let ack := HandshakeExchange.Delivery.rewritten rewrittenActive.output forward 63 rfl
  let input : HandshakeExchange.Input := {
    active, remote := passive.socket, passive, openPolicy := true, synPolicy := true, synAckPolicy := true
    syn := ⟨syn.input.bytes, [⟨forward, 63⟩]⟩
    synAck := ⟨synAck.input.bytes, [⟨Handshake.inbound active passive.socket, 63⟩]⟩
    ack := ⟨ack.input.bytes, [⟨forward, 63⟩]⟩
    times := ⟨0, 1, 2, 3⟩ }
  let complete ← load input.check
  let _ := complete.directional_mss
  ensure (complete.activeSeed.effectiveMSS == 800 && complete.passiveSeed.effectiveMSS == 1200 &&
    complete.activeSeed.Valid && complete.passiveSeed.Valid)
    "The actual rewritten exchange must derive directional MSS and valid endpoint seeds from its earlier outputs."
  failure (Handshake.activeOpen { active with ipSendLimit := 43 } passive.socket true) (.reject .invalidConfig)
  let exact ← transition (Handshake.activeOpen { active with ipSendLimit := 44 } passive.socket true)
  ensure (exact.output.bytes.length == 44) "The complete MSS-bearing startup packet must fit the local IP send limit."
  for packet in [opened.output, listened.output] do
    ensure (checksumAccepts packet.packet.ip.packet.source packet.packet.ip.packet.destination packet.packet.segment)
      "MSS-bearing startup output must have a valid TCP checksum."
  for (clientOffer, serverOffer, activeLimit, passiveLimit) in
      [(none, some serverReceive, 800, 536), (some clientReceive, none, 536, 1200)] do
    let client := { active with receiveMSS := clientOffer }
    let server := { passive with receiveMSS := serverOffer }
    let first ← transition (Handshake.activeOpen client server.socket true)
    let second ← transition (Handshake.listenSyn server first.output true)
    let third ← transition (Handshake.synSentSynAck first second.output true)
    let fourth ← transition (Handshake.synReceivedAck second third.output)
    ensure (third.seed.effectiveMSS == activeLimit && fourth.seed.effectiveMSS == passiveLimit)
      "An absent offer must select 536 only for the endpoint that received that absent offer."
  let silent := config 3221225985 41000 99 8
  let silentOpen ← transition (Handshake.activeOpen silent passive.socket true)
  for (options, limit) in [([2, 4, 3, 32], 800), ([1, 1, 2, 4, 3, 32, 0, 0], 800), ([1, 1, 1, 1], 536)] do
    let input ← checked (Handshake.inbound silent passive.socket) passive.iss (silent.iss.add 1) 18 0 options
    let result ← transition (Handshake.synSentSynAck silentOpen input true)
    ensure (result.seed.effectiveMSS == limit)
      "Incoming positive MSS and selected padding must work without a local advertisement."
  for options in [[2, 4, 0, 0], [2, 4, 3, 32, 2, 4, 3, 32]] do
    let input ← checked (Handshake.inbound silent passive.socket) passive.iss (silent.iss.add 1) 18 0 options
    failure (Handshake.synSentSynAck silentOpen input true) (.unsupported .options)
    let syn ← checked (Handshake.outbound silent passive.socket) silent.iss (Seq.ofNat 0) 2 0 options
    failure (Handshake.listenSyn passive syn true) (.unsupported .options)

def run : IO Unit := do
  for (activeISS, passiveISS) in [(0, 0), (4294967295, 0), (0, 4294967295), (4294967295, 4294967295)] do
    for (activeCapacity, passiveCapacity, ipLimit) in [(0, 0, 41), (8, 4, 576), (65535, 65535, 65535)] do
      exchange activeISS passiveISS activeCapacity passiveCapacity ipLimit
  rejectedInputs
  passiveWindowSource
  directionalMSS
  IO.println "Checked TCP startup tests passed."

end NetlibTest.TCPHandshake
