import Netlib.Protocol.IPv4

namespace NetlibTest.IPv4

open Netlib.Protocol.IPv4 Netlib.Protocol.InternetChecksum

example (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, computedChecksum packet, []⟩ := decode_encode packet bytes encoded

example (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := encode_decode bytes value accepted

example (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    value.packet.Encodable ∧ valid (headerBytes value.packet value.checksum) = true := decode_valid bytes value accepted

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def sample : Packet := ⟨184, 65535, true, 64, 17, 3221225986, 3325256706, [0, 1, 2]⟩

private def roundtrips : IO Unit := do
  for df in [false, true] do
    for ttl in ([0, 1, 64, 255] : List UInt8) do
      for protocol in ([0, 1, 6, 17, 253, 255] : List Netlib.Packet.Protocol) do
        for payload in [[], [0], [0, 255, 17], List.replicate 256 170] do
          let packet := { sample with dontFragment := df, ttl := ttl, protocol := protocol, payload := payload }
          let bytes ← unwrap (encode packet)
          ensure (bytes.length == payload.length + 20 && valid (bytes.take 20))
            "Canonical IPv4 encoding must checksum exactly its twenty-byte header."
          for padding in [[], [0, 255, 69, 0]] do
            let decoded ← unwrap (decode (bytes ++ padding))
            ensure (decoded.packet == packet && decoded.padding == padding &&
                (← unwrap (encodeDecoded decoded)) == bytes ++ padding)
              "Every selected header field, payload, original checksum, and link padding must round-trip."
  for address in ([0, 1, 65535, 65536, 2147483648, 4294967295] : List Netlib.Packet.Address) do
    let bytes := addressBytes address
    ensure (bytes.length == 4 && readAddress bytes[0]! bytes[1]! bytes[2]! bytes[3]! == address)
      "IPv4 addresses must retain all four network-order bytes."

private def malformed : IO Unit := do
  let bytes ← unwrap (encode sample)
  for count in List.range 20 do
    reject (decode (bytes.take count)) "An IPv4 header cannot be truncated."
  for version in ([0, 4, 64, 68, 70, 96, 255] : List UInt8) do
    reject (decode (bytes.set 0 version)) "Reject unsupported version and IHL independently of checksum."
  for (high, low) in ([(0, 0), (0, 19), (0, 24), (255, 255)] : List (UInt8 × UInt8)) do
    reject (decode ((bytes.set 2 high).set 3 low)) "Reject short or truncated declared total length."
  for (high, low) in ([(128, 0), (32, 0), (0, 1), (64, 1), (96, 0), (255, 255)] : List (UInt8 × UInt8)) do
    reject (decode ((bytes.set 6 high).set 7 low)) "Reject reserved flags, MF, and every nonzero fragment offset."
  reject (decode (bytes.set 8 63)) "A modified TTL must invalidate the header checksum."
  reject (decode (bytes.set 11 (bytes[11]! + 1))) "A corrupted checksum word must fail validation."
  let decoded ← unwrap (decode bytes)
  reject (encodeDecoded { decoded with checksum := decoded.checksum + 1 })
    "The preserving encoder must reject an invalid supplied checksum."
  let corruptedPayload := bytes.set 20 255
  ensure ((← unwrap (decode corruptedPayload)).packet.payload == [255, 1, 2])
    "IPv4 checksums cover the header; payload integrity belongs to the transport layer."

private def boundaries : IO Unit := do
  let base := { sample with identification := 0, dontFragment := false, payload := [] }
  let correction := computedChecksum base
  let zeroPacket := { base with identification := correction }
  ensure (computedChecksum zeroPacket == 0) "The dual-zero fixture must have a zero canonical checksum."
  for checksum in ([0, 65535] : List Word) do
    let raw := headerBytes zeroPacket checksum ++ [255, 0, 255]
    let decoded ← unwrap (decode raw)
    ensure (decoded.checksum == checksum && decoded.padding == [255, 0, 255] && decoded.packet.payload.isEmpty &&
        (← unwrap (encodeDecoded decoded)) == raw)
      "Both valid one's-complement zero words must survive arbitrary accepted-byte re-encoding."
  let large := { sample with payload := List.replicate 65515 170 }
  let bytes ← unwrap (encode large)
  ensure (bytes.length == 65535 && bytes[2]! == 255 && bytes[3]! == 255)
    "The maximum total length must retain both length octets."
  let decoded ← unwrap (decode bytes)
  ensure (decoded.packet == large && (← unwrap (encodeDecoded decoded)) == bytes)
    "The largest selected IPv4 packet must decode and re-encode completely."
  reject (encode { sample with payload := List.replicate 65516 0 }) "Oversized IPv4 payloads must not wrap total length."

def run : IO Unit := do
  roundtrips
  malformed
  boundaries
  IO.println "IPv4 wire codec tests passed."

end NetlibTest.IPv4
