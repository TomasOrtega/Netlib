import Netlib.Protocol.TCP.Reassembly
import Netlib.Protocol.IPv4Fragmentation

namespace NetlibTest.TCPReassembly

open Netlib Protocol InternetChecksum
namespace Adapter
export Netlib.Protocol.TCP.Reassembly (Source source)
end Adapter

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def reject (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def sourceAddress : Packet.Address := 3221225986
private def destinationAddress : Packet.Address := 3405803778
private def policy : IPv4Reassembly.Policy := ⟨30⟩
private def domain : IPv4Reassembly.Domain := ⟨2, 0⟩

private def original : TCP.Segment := TCP.rechecksum sourceAddress destinationAddress {
  sourcePort := 41000, destinationPort := 8080, sequence := TCP.Seq.ofNat 4294967295,
  acknowledgment := TCP.Seq.ofNat 2147483648, reserved := 15, flags := 255,
  window := 65535, checksum := 0, urgentPointer := 65535,
  options := [1, 2, 4, 5, 180, 0, 0, 0], payload := (List.range 17).map UInt8.ofNat }

private def packet (segment : TCP.Segment := original) (source : Packet.Address := sourceAddress)
    (destination : Packet.Address := destinationAddress)
    : IPv4.Packet :=
  ⟨42, 4197, false, 64, Packet.Protocol.tcp, source, destination, segment.encodeBytes⟩

private def part (base : IPv4.Packet) (start size : Nat) (more : Bool) : IPv4Fragment.Decoded :=
  let fragment := IPv4Fragmentation.fragmentPacket base ⟨start, base.payload.drop start |>.take size, more⟩
  ⟨fragment, IPv4Fragment.computedChecksum fragment, []⟩

private def complete (fragments : List IPv4Fragment.Decoded) : IO IPv4Reassembly.Output := do
  let mut state := IPv4Reassembly.State.initial
  let mut outputs := []
  for (fragment, index) in fragments.zipIdx do
    match IPv4Reassembly.arrive policy state index domain fragment with
    | .error reason => throw (IO.userError reason.describe)
    | .ok result =>
      state := result.state
      if let some output := result.output then outputs := output :: outputs
  ensure (outputs.length == 1 && state.queues.isEmpty) "A complete TCP fragment family must emit once and remove its queue."
  let some output := outputs.head? | throw (IO.userError "Missing completed TCP family.")
  pure output

private def check (output : IPv4Reassembly.Output) (expected : TCP.Segment) : IO (Adapter.Source output) := do
  let value ← load (Adapter.source output)
  ensure (value.packet.segment == expected && value.packet.ip.packet == output.packet &&
    value.packet.segment.encodeBytes == output.packet.payload && value.packet.ip.padding.isEmpty)
    "The TCP byte adapter must preserve exact completed bytes, control metadata, and payload boundaries."
  ensure (InternetChecksum.valid (TCP.pseudoHeader output.packet.source output.packet.destination
    value.packet.segment.lengthWord ++ output.packet.payload))
    "The completed TCP checksum remains mandatory, including an ordinary zero word."
  pure value

private def flowRewrite (value : Adapter.Source output) : IO Unit := do
  let target : Packet.Header := ⟨3405803777, 3325256706, Packet.Protocol.tcp, 40000, 9000⟩
  let entry : FlowNAT.Entry := ⟨value.packet.header, target.reverse, 0, 0, 100⟩
  if wellFormed : entry.WellFormed then
    let result := value.rewriteFlow entry .original 63 wellFormed rfl
    let decoded ← load (TCP.decodeIPv4 result.bytes)
    ensure (decoded == result.packet && decoded.header == target &&
      decoded.segment.sequence == value.packet.segment.sequence &&
      decoded.segment.acknowledgment == value.packet.segment.acknowledgment &&
      decoded.segment.reserved == value.packet.segment.reserved &&
      decoded.segment.flags == value.packet.segment.flags && decoded.segment.window == value.packet.segment.window &&
      decoded.segment.urgentPointer == value.packet.segment.urgentPointer &&
      decoded.segment.options == value.packet.segment.options && decoded.segment.payload == value.packet.segment.payload)
      "Certified tuple rewriting after reassembly must retain transport controls and recompute both checksums."
  else throw (IO.userError "The selected pure tuple projection must be well formed.")

def run : IO Unit := do
  let base := packet
  let first := part base 0 16 true
  let middle := part base 16 16 true
  let last := part base 32 (base.payload.length - 32) false
  for fragments in [[first, middle, last], [first, last, middle], [middle, first, last],
      [middle, last, first], [last, first, middle], [last, middle, first]] do
    let output ← complete fragments
    ensure (output.reassembled && output.packet.payload == base.payload && output.pieces.length == 3)
      "Existing IPv4 reassembly must order the actual TCP fragment bytes in every arrival permutation."
    let checked ← check output original
    flowRewrite checked
  let whole ← complete [part base 0 base.payload.length false]
  ensure (!whole.reassembled) "Whole TCP input must retain the existing IPv4 queue bypass."
  let _ ← check whole original
  let unknown := TCP.rechecksum sourceAddress destinationAddress
    { original with options := [253, 4, 170, 187], payload := [1, 2, 3] }
  let unknownPacket := packet unknown
  let unknownOutput ← complete [part unknownPacket 16 (unknownPacket.payload.length - 16) false,
    part unknownPacket 0 16 true]
  let _ ← check unknownOutput unknown
  let zero : TCP.Segment := ⟨0, 0, TCP.Seq.ofNat 0, TCP.Seq.ofNat 0, 0, 0, 0, 0, 0, [], [175, 227]⟩
  let zeroPacket : IPv4.Packet := ⟨0, 42, false, 64, Packet.Protocol.tcp, 0, 0, zero.encodeBytes⟩
  for fragments in [[part zeroPacket 0 16 true, part zeroPacket 16 6 false],
      [part zeroPacket 16 6 false, part zeroPacket 0 16 true]] do
    let output ← complete fragments
    let checked ← check output zero
    ensure (checked.packet.segment.checksum == 0) "Verified TCP checksum zero must survive the byte adapter unchanged."
  let corrupted := { zeroPacket with payload := zeroPacket.payload.take 21 ++ [226] }
  let corruptedOutput ← complete [part corrupted 16 6 false, part corrupted 0 16 true]
  reject (Adapter.source corruptedOutput) "Reassembly cannot turn checksum zero into TCP checksum omission."
  let wrongProtocol := { base with protocol := Packet.Protocol.udp }
  let protocolOutput ← complete [part wrongProtocol 0 16 true, part wrongProtocol 16 16 true,
    part wrongProtocol 32 (wrongProtocol.payload.length - 32) false]
  reject (Adapter.source protocolOutput) "A non-TCP IPv4 output cannot be cast into the TCP byte adapter."
  let malformed := TCP.rechecksum sourceAddress destinationAddress { original with options := [2, 3, 0, 0] }
  let malformedPacket := packet malformed
  let malformedOutput ← complete [part malformedPacket 0 16 true,
    part malformedPacket 16 (malformedPacket.payload.length - 16) false]
  reject (Adapter.source malformedOutput) "A valid checksum cannot hide malformed completed TCP option framing."

end NetlibTest.TCPReassembly
