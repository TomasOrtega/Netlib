import Netlib.Protocol.TCP.EstablishedReceive

namespace NetlibTest.TCPEstablishedReceive

open Netlib Protocol TCP
namespace Endpoint
export Netlib.Protocol.TCP.EstablishedReceive
  (State Input input receive Decision Block Unsupported Reject Result AckKind)
end Endpoint

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def source : Packet.Address := 3221225986
private def destination : Packet.Address := 3405803778
private def tuple : Packet.Header := ⟨source, destination, Packet.Protocol.tcp, 41000, 8080⟩

private def seed (capacity : Nat := 8) : Endpoint.State :=
  ⟨tuple, Seq.ofNat 100, capacity, [], Seq.ofNat 200, Seq.ofNat 203, [10, 11, 12]⟩

private def checked (segment : Segment) (src : Packet.Address := source)
    (dst : Packet.Address := destination) : IO Endpoint.Input := do
  let ip : IPv4.Packet := ⟨0, 42, true, 64, Packet.Protocol.tcp, src, dst, segment.encodeBytes⟩
  let bytes ← load (IPv4.encode ip)
  load (Endpoint.input bytes)

private def packet (sequence acknowledgment : Nat) (flags : UInt8) (payload : List UInt8)
    (window : InternetChecksum.Word := 65535) (options : List UInt8 := []) : IO Endpoint.Input :=
  checked (TCP.rechecksum source destination {
    sourcePort := 41000, destinationPort := 8080, sequence := Seq.ofNat sequence,
    acknowledgment := Seq.ofNat acknowledgment, reserved := 15, flags := flags,
    window := window, checksum := 0, urgentPointer := 0, options := options, payload := payload })

private def test (state : Endpoint.State) (value : Endpoint.Input) (expected : Endpoint.Decision)
    (ack : Option Endpoint.AckKind) : IO Endpoint.Result := do
  let result := Endpoint.receive state value
  ensure (result.decision == expected && result.ack.map (·.kind) == ack)
    s!"Unexpected receive result: {repr result.decision}."
  match expected with
  | .blocked _ => ensure (result.state == state) "A blocked result must keep the full state."
  | .accepted count size =>
    ensure (result.state.received == state.received ++ value.packet.segment.payload &&
      result.state.receiveNext == state.receiveNext.add size &&
      result.state.sent == state.sent.drop count && result.state.sendUna == state.sendUna.add count &&
      result.state.sendNext == state.sendNext) "Data and ACK progress must use the exact byte spans."
  if decide state.Valid then
    ensure (decide result.state.Valid) "A receive step must keep the state bounds."
  if let some intent := result.ack then
    ensure (intent.sequence == result.state.sendNext && intent.acknowledgment == result.state.receiveNext &&
      intent.window == result.state.window) "An ACK request must use the resulting cursors and local free space."
  pure result

private def nat (state : Endpoint.State) (value : Endpoint.Input) : IO Unit := do
  let target : Packet.Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
  let rewritten := value.rewrite target 63 rfl
  let before := Endpoint.receive state value
  let after := Endpoint.receive (state.rebind target) rewritten
  ensure (after == before.rebind target) "A certified tuple change must keep the receive decision and state effects."
  let unchanged := Endpoint.receive state rewritten
  ensure (unchanged.decision == .blocked (.reject .tuple)) "The endpoint must bind the actual checked tuple."

private def zeroWindowControls : IO Unit := do
  let state := seed 0
  ensure (decide state.Valid) "The seed must meet the profile bounds."
  for (flags, reason) in [(20, EstablishedReceive.Unsupported.reset), (48, EstablishedReceive.Unsupported.urgent)] do
    let value ← packet 100 200 flags [1]
    let _ ← test state value (.blocked (.unsupported reason)) none
  let option ← packet 999 200 16 [1] 65535 [253, 4, 170, 187]
  let _ ← test state option (.blocked (.unsupported .options)) none
  pure ()

private def dataAndAcks : IO Unit := do
  let state := seed
  let first ← packet 100 201 24 [1, 2] 0
  let result ← test state first (.accepted 1 2) (some .data)
  ensure (result.state.sent == [11, 12] && result.state.window == 6)
    "The ACK removes one sent byte. A peer window of zero does not close local receive space."
  nat state first
  let second ← packet 102 203 16 [3]
  let complete ← test result.state second (.accepted 2 1) (some .data)
  ensure (complete.state.sent.isEmpty && complete.state.sendUna == complete.state.sendNext)
    "An ACK at SND.NXT must remove the full remaining prefix."
  let old ← packet 103 202 16 [4]
  let _ ← test complete.state old (.accepted 0 1) (some .data)
  let duplicate ← packet 100 200 16 [5]
  let _ ← test state duplicate (.accepted 0 1) (some .data)
  let lower := (Seq.ofNat 200).add (Seq.modulus - EstablishedReceive.maxSendWindow)
  let atLower ← packet 100 lower.val 16 [6]
  let _ ← test state atLower (.accepted 0 1) (some .data)
  nat state atLower
  let tooOld ← packet 100 ((Seq.ofNat 200).add (Seq.modulus - 65536)).val 16 [7]
  let _ ← test state tooOld (.blocked (.reject .acknowledgment)) (some .challenge)
  nat state tooOld
  let future ← packet 100 204 16 [8]
  let _ ← test state future (.blocked (.reject .acknowledgment)) (some .challenge)
  let opposite ← packet 100 ((Seq.ofNat 200).add Seq.halfSpace).val 16 []
  let _ ← test state opposite (.blocked (.reject .acknowledgment)) (some .challenge)
  let pureAck ← packet 105 202 16 []
  let _ ← test state pureAck (.accepted 2 0) none
  let absent ← packet 100 201 0 [1]
  let _ ← test state absent (.blocked (.reject .missingAck)) none
  pure ()

private def receiveLimits : IO Unit := do
  let state := seed 4
  let occupied := { state with received := [90] }
  let fitting ← packet 100 201 16 [1, 2, 3]
  let full ← test occupied fitting (.accepted 1 3) (some .data)
  ensure (full.state.received == [90, 1, 2, 3] && full.state.window == 0)
    "The local buffer must fill to its exact capacity."
  let overflow ← packet 100 201 16 [1, 2, 3, 4]
  let _ ← test occupied overflow (.blocked (.unsupported .trimming)) none
  nat occupied overflow
  let early ← packet 99 201 16 [1, 2]
  let _ ← test state early (.blocked (.unsupported .trimming)) none
  let later ← packet 101 201 16 [1]
  let _ ← test state later (.blocked (.unsupported .outOfOrder)) none
  nat state later
  let outside ← packet 104 4294967295 16 []
  let _ ← test state outside (.blocked (.reject .sequence)) (some .sequence)
  let contains ← packet 99 201 16 [1, 2, 3, 4, 5, 6]
  let _ ← test state contains (.blocked (.reject .sequence)) (some .sequence)
  let closed := seed 0
  let empty ← packet 100 202 16 []
  let _ ← test closed empty (.accepted 2 0) none
  let data ← packet 100 202 16 [1]
  let _ ← test closed data (.blocked (.reject .sequence)) (some .sequence)
  let displaced ← packet 101 202 16 []
  let _ ← test closed displaced (.blocked (.reject .sequence)) (some .sequence)
  pure ()

private def controlsAndSeed : IO Unit := do
  let state := seed
  for (flags, reason) in [(20, EstablishedReceive.Unsupported.reset), (18, EstablishedReceive.Unsupported.synchronize),
      (17, EstablishedReceive.Unsupported.finish), (48, EstablishedReceive.Unsupported.urgent),
      (80, EstablishedReceive.Unsupported.congestion), (144, EstablishedReceive.Unsupported.congestion)] do
    let value ← packet 999 201 flags [1]
    let _ ← test state value (.blocked (.unsupported reason)) none
    nat state value
  for options in [[0, 0, 0, 0], [2, 4, 5, 180], [253, 4, 170, 187]] do
    let value ← packet 100 201 16 [1] 65535 options
    let _ ← test state value (.blocked (.unsupported .options)) none
  let value ← packet 100 201 16 [1]
  for invalid in [{ state with capacity := 65536 }, { state with received := List.replicate 9 0 },
      { state with sendNext := Seq.ofNat 204 },
      { state with sent := List.replicate 65536 0, sendNext := state.sendUna.add 65536 }] do
    let _ ← test invalid value (.blocked (.reject .invalidSeed)) none
  let foreign := { state with inbound := tuple.reverse }
  let _ ← test foreign value (.blocked (.reject .tuple)) none
  pure ()

private def wrapAndChecksum : IO Unit := do
  let state : Endpoint.State := { seed 8 with
    receiveNext := Seq.ofNat 4294967295
    sendUna := Seq.ofNat 4294967294
    sendNext := Seq.ofNat 1 }
  let value ← packet 4294967295 0 16 [1, 2]
  let result ← test state value (.accepted 2 2) (some .data)
  ensure (result.state.receiveNext == Seq.ofNat 1 && result.state.sendUna == Seq.ofNat 0)
    "The cursors must advance across the sequence boundary."
  nat state value
  let zero : Segment := ⟨0, 0, Seq.ofNat 0, Seq.ofNat 0, 0, 16, 0, 0, 0, [], [175, 211]⟩
  ensure (TCP.checksumAccepts 0 0 zero) "A TCP checksum word of zero must pass the normal checksum test."
  let verified ← checked zero 0 0
  let zeroState : Endpoint.State := ⟨⟨0, 0, Packet.Protocol.tcp, 0, 0⟩, Seq.ofNat 0, 2, [],
    Seq.ofNat 0, Seq.ofNat 0, []⟩
  let _ ← test zeroState verified (.accepted 0 2) (some .data)
  let bad := { zero with payload := [175, 210] }
  let ip : IPv4.Packet := ⟨0, 42, true, 64, Packet.Protocol.tcp, 0, 0, bad.encodeBytes⟩
  let bytes ← load (IPv4.encode ip)
  reject (Endpoint.input bytes) "A checksum word of zero must not disable the TCP checksum test."
  let wrongProtocol := { ip with protocol := Packet.Protocol.udp, payload := zero.encodeBytes }
  let other ← load (IPv4.encode wrongProtocol)
  reject (Endpoint.input other) "The endpoint input must come from checked TCP bytes."

def run : IO Unit := do
  zeroWindowControls
  dataAndAcks
  receiveLimits
  controlsAndSeed
  wrapAndChecksum

end NetlibTest.TCPEstablishedReceive
