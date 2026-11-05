import Netlib.Protocol.IPv4Quote

namespace NetlibTest.IPv4Quote

open Netlib Netlib.Protocol Netlib.Protocol.IPv4Quote

example (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    encodeDecoded value = .ok wire := encode_decode wire value accepted

example (source : UDP.DecodedIPv4) (valid : SourceValid source) (n : Nat)
    (minimum : 28 ≤ n) (maximum : n ≤ source.ip.packet.wireLength) :
    (make source n).Valid := make_valid source valid n minimum maximum

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def reject (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def source : Packet.Address := 3221225985
private def destination : Packet.Address := 3325256706

private def packet (payload : List UInt8) (df : Bool) : IPv4.Packet :=
  ⟨167, 4321, df, 37, Packet.Protocol.udp, source, destination, payload⟩

private def repairChecksum (wire : List UInt8) : List UInt8 :=
  let blank := wire.take 10 ++ [0, 0] ++ (wire.drop 12).take 8
  wire.take 10 ++ InternetChecksum.wordBytes (InternetChecksum.checksum blank) ++ wire.drop 12

def run : IO Unit := do
  for df in [false, true] do
    let udp ← unwrap (UDP.encodeComputed source destination 12345 53 [1, 2, 3, 4, 5])
    let original ← unwrap (IPv4.encode (packet udp df))
    let input ← unwrap (UDP.decodeIPv4 (original ++ [0, 255, 0]))
    for length in [28, 29, 30, 32, 33] do
      let quote := make input length
      let wire ← unwrap (encodeDecoded quote)
      let decoded ← unwrap (decode wire)
      ensure (wire == original.take length && decoded == quote && decoded.declaredLength.val == original.length &&
          decoded.packet.payload == udp.take (length - 20) && header decoded == input.header &&
          decoded.packet.tos == 167 && decoded.packet.identification == 4321 && decoded.packet.ttl == 37 &&
          decoded.packet.dontFragment == df && decoded.checksum == input.ip.checksum &&
          udpLength? decoded.packet.payload == some udp.length && (← unwrap (encodeDecoded decoded)) == wire)
        "A quote must preserve the exact checked source prefix and original declared lengths and metadata."
      if length < original.length then
        reject (IPv4.decode wire) "A truncated quote must retain the original total length."
      if length == 28 then
        reject (UDP.decode source destination decoded.packet.payload)
          "A partial quote is not a complete UDP datagram and must not be checksum-validated as one."
    let full ← unwrap (decode original)
    ensure ((← unwrap (UDP.decode source destination full.packet.payload)).payload == [1, 2, 3, 4, 5])
      "A full quotation permits separate complete UDP validation."
    let quote := original.take 28
    reject (decode (quote.take 27)) "A quoted UDP header needs all eight bytes."
    reject (decode (quote.take 19)) "A quoted IPv4 header needs twenty bytes."
    reject (decode ((quote.toArray.modify 10 (· + 1)).toList)) "A corrupted quoted IPv4 checksum must fail."
    for position in [0, 6, 7, 9, 24, 25] do
      let bad := repairChecksum ((quote.toArray.modify position (· + 1)).toList)
      reject (decode bad) "Quoted options, fragmentation, protocol, and mismatched UDP lengths must fail."
    let tooShort := repairChecksum ((quote.toArray.set! 3 27).toList)
    reject (decode tooShort) "The original total length must contain the complete UDP header."
    reject (decode (original ++ [0])) "Quote bytes cannot exceed the original declared IPv4 length."
    let changedUDP := (quote.toArray.modify 26 (· + 1)).toList
    ensure ((← unwrap (decode changedUDP)).packet.payload == changedUDP.drop 20)
      "A partial quotation preserves UDP checksum bytes without checking them against missing payload."
  let udp ← unwrap (UDP.encode source destination ⟨0, 65535, 0, List.replicate 65507 0⟩)
  let maximum ← unwrap (IPv4.encode (packet udp true))
  let value ← unwrap (decode maximum)
  ensure (maximum.length == 65535 && value.declaredLength.val == 65535 &&
      (← unwrap (encodeDecoded value)) == maximum)
    "Quoted original IPv4 packets may use the full sixteen-bit length range."
  IO.println "IPv4 quotation codec tests passed."

end NetlibTest.IPv4Quote
