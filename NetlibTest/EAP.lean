import Netlib.Protocol.EAP

namespace NetlibTest.EAP

open Netlib.Protocol.EAP

example (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, []⟩ := decode_encode packet bytes encoded

example (value : Decoded) (bytes : List UInt8) (encoded : encodeDecoded value = .ok bytes) :
    decode bytes = .ok value := decode_encodeDecoded value bytes encoded

example (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := encode_decode bytes value accepted

example (packet : Packet) (padding : List UInt8) (bounded : packet.Encodable) :
    decode (encodeBytes packet ++ padding) = .ok ⟨packet, padding⟩ := decode_encodeBytes packet padding bounded

example (identifier kind : UInt8) (data : List UInt8) :
    (Packet.request identifier kind data).identifier = identifier := rfl

example (identifier : UInt8) : (Packet.success identifier).kind? = none := rfl

set_option maxRecDepth 2048 in
example : decode [3, 255, 0, 4, 170, 187] = .ok ⟨.success 255, [170, 187]⟩ := rfl

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def run : IO Unit := do
  let request : Packet := .request 42 1 [97, 108, 105, 99, 101]
  ensure ((← unwrap (encode request)) == [1, 42, 0, 10, 1, 97, 108, 105, 99, 101])
    "EAP length includes the four-byte header and request Type."
  for identifier in ([0, 1, 42, 255] : List UInt8) do
    for packet in [Packet.success identifier, .failure identifier] do
      ensure ((← unwrap (encode packet)).length == 4)
        "Terminal EAP packets must have exactly four declared bytes."
      let decoded ← unwrap (decode (← unwrap (encode packet)))
      ensure (decoded.packet == packet && decoded.padding.isEmpty)
        "Terminal packet code and identifier must survive framing."
    for kind in ([0, 1, 13, 200, 254, 255] : List UInt8) do
      for data in [[], [0, 255, 1, 128]] do
        for packet in [Packet.request identifier kind data, .response identifier kind data] do
          for padding in [[], [0, 3, 255]] do
            let source : Decoded := ⟨packet, padding⟩
            let decoded ← unwrap (decode (← unwrap (encodeDecoded source)))
            ensure (decoded == source && decoded.packet.identifier == identifier &&
                decoded.packet.kind? == some kind)
              "Opaque method bytes and arbitrary padding must survive without interpreting authentication."
  let response ← unwrap (decode [2, 255, 0, 6, 200, 0, 99, 88])
  ensure (response.packet == .response 255 200 [0] && response.padding == [99, 88])
    "The declared EAP length must separate opaque method data from padding."
  for raw in ([[1, 0, 0, 5, 255, 0, 255], [2, 255, 0, 6, 200, 0, 99, 88],
      [3, 255, 0, 4, 3, 255, 0, 4], [4, 0, 0, 4, 170],
      [1, 128, 1, 0, 13] ++ List.replicate 251 170 ++ [255, 0]] : List (List UInt8)) do
    let value ← unwrap (decode raw)
    ensure ((← unwrap (encodeDecoded value)) == raw)
      "Every accepted EAP byte, including padding and both length octets, must re-encode exactly."
  for bytes in ([[], [1], [1, 2], [1, 2, 0], [1, 2, 0, 3], [1, 2, 0, 4],
      [2, 2, 0, 4], [1, 2, 0, 6, 13], [3, 2, 0, 5, 0], [4, 2, 0, 5, 0],
      [0, 2, 0, 4], [5, 2, 0, 4], [6, 2, 0, 4], [255, 2, 0, 4]] : List (List UInt8)) do
    reject (decode bytes) "Malformed or unsupported EAP structure must not decode."
  reject (decode [1, 9, 0, 4, 13])
    "An out-of-length padding byte cannot supply a missing Request Type."
  let terminal ← unwrap (decode [3, 9, 0, 4, 1, 2, 3])
  ensure (terminal.packet == .success 9 && terminal.padding == [1, 2, 3])
    "Allowed terminal padding must be retained rather than rejected as declared data."
  let large : Packet := .request 255 13 (List.replicate 65530 170)
  let largeBytes ← unwrap (encode large)
  ensure (largeBytes.length == 65535 && largeBytes.take 5 == [1, 255, 255, 255, 13])
    "The largest EAP packet must encode its full 16-bit length without truncation."
  let largeDecoded ← unwrap (decode largeBytes)
  ensure (largeDecoded.packet == large && largeDecoded.padding.isEmpty)
    "The maximum-length method data must decode completely."
  ensure ((← unwrap (encodeDecoded largeDecoded)) == largeBytes)
    "Accepted maximum-length EAP must re-encode without changing any byte."
  reject (encode (.response 1 13 (List.replicate 65531 0)))
    "Oversized method data must fail before wrapping the length field."
  IO.println "EAP wire codec tests passed."

end NetlibTest.EAP
