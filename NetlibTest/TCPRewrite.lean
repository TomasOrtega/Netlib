import Netlib.Protocol.TCP.Rewrite

namespace NetlibTest.TCPRewrite

open Netlib Packet Protocol InternetChecksum

private def original : Header := ⟨3221225985, 3325256706, Packet.Protocol.tcp, 12345, 80⟩
private def translated : Header := ⟨3405803777, 3405803785, Packet.Protocol.tcp, 40000, 8443⟩
private def entry : FlowNAT.Entry := ⟨original, translated.reverse, 0, 0, 300⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private structure Prepared where
  bytes : List UInt8
  packet : TCP.DecodedIPv4
  decoded : TCP.decodeIPv4 bytes = .ok packet

private theorem Prepared.valid (input : Prepared) : Protocol.TCPRewrite.SourceValid input.packet :=
  Protocol.TCPRewrite.sourceValid_of_decoded input.bytes input.packet input.decoded

private def read (bytes : List UInt8) : IO Prepared :=
  match decoded : TCP.decodeIPv4 bytes with
  | .error message => throw (IO.userError message)
  | .ok packet => pure ⟨bytes, packet, decoded⟩

private def seed (header : Header) (payload options : List UInt8) : TCP.Segment := {
  sourcePort := header.sourcePort, destinationPort := header.destinationPort,
  sequence := TCP.Seq.ofNat 4294967295, acknowledgment := TCP.Seq.ofNat 2147483648,
  reserved := 15, flags := 255, window := 65535, checksum := 0, urgentPointer := 65535,
  options, payload }

private def make (header : Header) (payload : List UInt8) (options : List UInt8 := [])
    (identification : Word := 0x4321) : IO Prepared := do
  let segment := TCP.rechecksum header.source header.destination (seed header payload options)
  let tcp ← unwrap (TCP.encode header.source header.destination segment)
  let packet : IPv4.Packet := ⟨0x28, identification, true, 64, header.protocol, header.source, header.destination, tcp⟩
  read (← unwrap (IPv4.encode packet))

private def inspect (input : Prepared) (target : Header) (ttl : UInt8)
    (result : Protocol.TCPRewrite.Certified input.packet target ttl) : IO Unit := do
  let decoded ← unwrap (TCP.decodeIPv4 result.bytes)
  let before := input.packet.segment
  let after := decoded.segment
  ensure (decoded == result.packet && decoded.header == target && after.payload == before.payload &&
      after.sequence == before.sequence && after.acknowledgment == before.acknowledgment &&
      after.reserved == before.reserved && after.flags == before.flags && after.window == before.window &&
      after.urgentPointer == before.urgentPointer && after.options == before.options)
    "Certified rewriting must preserve payload and every transport field outside the translated endpoints and checksum."
  ensure (decoded.ip.packet.ttl == ttl && decoded.ip.packet.tos == input.packet.ip.packet.tos &&
      decoded.ip.packet.identification == input.packet.ip.packet.identification &&
      decoded.ip.packet.dontFragment == input.packet.ip.packet.dontFragment && decoded.ip.padding.isEmpty &&
      decoded.ip.packet.wireLength == input.packet.ip.packet.wireLength &&
      result.bytes.length == decoded.ip.packet.wireLength)
    "Rewriting must retain IPv4 metadata and length, apply caller TTL, and omit external padding."
  ensure (InternetChecksum.valid (IPv4.headerBytes decoded.ip.packet decoded.ip.checksum) &&
      InternetChecksum.valid (TCP.pseudoHeader target.source target.destination after.lengthWord ++ decoded.ip.packet.payload))
    "Both output checksums must verify the actual translated fields, including a TCP checksum word zero."

private def translationTests : IO Unit := do
  for payload in [[], [1], [1, 2], [1, 2, 3], [255, 0, 128, 42]] do
    for options in [[], [1, 2, 4, 5, 180, 254, 2, 0], List.replicate 40 1] do
      let input ← make original payload options
      let unchanged := Protocol.TCPRewrite.rewrite input.packet original 64 input.valid rfl
      inspect input original 64 unchanged
      ensure (unchanged.bytes == input.bytes) "An unchanged canonical TCP packet must retain its exact bytes."
      let ttlOnly := Protocol.TCPRewrite.rewrite input.packet original 63 input.valid rfl
      inspect input original 63 ttlOnly
      ensure (ttlOnly.packet.segment.checksum == input.packet.segment.checksum &&
          ttlOnly.packet.ip.checksum != input.packet.ip.checksum)
        "A TTL-only change must update the IPv4 checksum without changing the TCP checksum."
      for ttl in [63, 0] do
        let result := Protocol.TCPRewrite.rewrite input.packet translated ttl input.valid rfl
        inspect input translated ttl result
      let reply ← make translated.reverse (payload ++ [42]) options
      let restored := Protocol.TCPRewrite.rewrite reply.packet original.reverse 63 reply.valid rfl
      inspect reply original.reverse 63 restored
      ensure (restored.packet.segment.payload == payload ++ [42])
        "Reverse translation retains the reply's own payload without assuming transport handshake state."
  ensure (entry.check && entry.output .original == translated && entry.output .reply == original.reverse)
    "Flow tuple projection must select the corresponding endpoint translation in both directions."

private def zeroAndBoundsTests : IO Unit := do
  let zero : TCP.Segment := ⟨12345, 80, TCP.Seq.ofNat 0, TCP.Seq.ofNat 0, 0, 16, 4096, 0, 0, [], [0x83, 0x12]⟩
  let ip : IPv4.Packet := ⟨0x28, 0x4321, true, 64, original.protocol, original.source, original.destination, zero.encodeBytes⟩
  let input ← read (← unwrap (IPv4.encode ip))
  ensure (input.packet.segment.checksum == 0) "The independent source fixture must contain an ordinary valid TCP checksum zero."
  let alternateSegment := { zero with checksum := 65535 }
  let alternate ← read (← unwrap (IPv4.encode { ip with payload := alternateSegment.encodeBytes }))
  let canonical := Protocol.TCPRewrite.rewrite alternate.packet original 64 alternate.valid rfl
  inspect alternate original 64 canonical
  ensure (alternate.packet.segment.checksum == 65535 && canonical.packet.segment.checksum == 0 &&
      canonical.bytes == input.bytes && alternate.packet.segment.reserved == 0)
    "Both valid TCP checksum zero representations must decode while certified recomputation emits canonical zero."
  let changed := Protocol.TCPRewrite.rewrite input.packet translated 63 input.valid rfl
  inspect input translated 63 changed
  ensure (changed.packet.segment.checksum != 0)
    "A zero input checksum must be recomputed after endpoint translation rather than treated as omitted."
  let zeroTarget := Protocol.TCPRewrite.rewrite changed.packet original 62
    (Protocol.TCPRewrite.sourceValid_of_decoded changed.bytes changed.packet changed.decoded) rfl
  let zeroPrepared : Prepared := ⟨changed.bytes, changed.packet, changed.decoded⟩
  inspect zeroPrepared original 62 zeroTarget
  ensure (zeroTarget.packet.segment.checksum == 0)
    "A translated tuple whose computed TCP checksum is zero must retain zero instead of UDP substitution."
  let padded ← read (input.bytes ++ [0, 255, 0])
  let stripped := Protocol.TCPRewrite.rewrite padded.packet translated 63 padded.valid rfl
  inspect padded translated 63 stripped
  ensure (padded.packet.ip.padding == [0, 255, 0] && stripped.packet.ip.padding.isEmpty)
    "External link padding must not enter the transport payload or canonical rewritten IPv4 output."
  let largest ← make original (List.replicate 65495 0)
  let maximum := Protocol.TCPRewrite.rewrite largest.packet translated 63 largest.valid rfl
  inspect largest translated 63 maximum
  ensure (maximum.bytes.length == 65535 && maximum.packet.segment.payload.length == 65495)
    "The maximal IPv4 TCP packet must remain encodable without changing payload length."

private def flowTests : IO Unit := do
  for direction in [FlowNAT.Direction.original, .reply] do
    let input ← make (entry.input direction) [0, 255, 17] [1, 2, 4, 5, 180, 254, 2, 0]
    if selected : input.packet.header = entry.input direction then
      let result := Protocol.TCPRewrite.rewriteFlow input.packet entry direction 63 input.valid
        (by decide) selected
      inspect input (entry.output direction) 63 result
      ensure (result.packet.header == (entry.rewrite direction).apply input.packet.header)
        "Certified TCP rewriting must realize the selected flow tuple projection in each direction."
    else throw (IO.userError "The static flow fixture must decode to its selected input tuple.")

example (result : Protocol.TCPRewrite.Certified input target ttl) :
    TCP.decodeIPv4 result.bytes = .ok result.packet := result.decoded

example (result : Protocol.TCPRewrite.Certified input target ttl) :
    result.packet.segment.payload = input.segment.payload ∧ result.packet.ip.packet.ttl = ttl :=
  ⟨result.payload, result.ttl⟩

def run : IO Unit := do
  translationTests
  zeroAndBoundsTests
  flowTests
  IO.println "Static payload-preserving TCP rewrite tests passed."

end NetlibTest.TCPRewrite
