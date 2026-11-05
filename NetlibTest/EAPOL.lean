import Netlib.Import.EAPOL

namespace NetlibTest.EAPOL

open Netlib.Protocol
open Netlib.Import.EAPOL

private def peer : MAC := ⟨2, 0, 0, 0, 0, 1⟩
private def authenticator : MAC := ⟨2, 0, 0, 0, 0, 2⟩
private def group : MAC := ⟨1, 128, 194, 0, 0, 3⟩

example (frame : EthernetFrame) (bytes : List UInt8) (encoded : encodeEthernet frame = .ok bytes) :
    decodeEthernet bytes = .ok frame := decodeEthernet_encodeEthernet frame bytes encoded

example (value : Decoded) (bytes : List UInt8) (encoded : encodeDecoded value = .ok bytes) :
    decode bytes = .ok value := decode_encodeDecoded value bytes encoded

example (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := encode_decode bytes value accepted

example (bytes : List UInt8) (frame : EthernetFrame) (accepted : decodeEthernet bytes = .ok frame) :
    encodeEthernet frame = .ok bytes := encodeEthernet_decodeEthernet bytes frame accepted

example (address : MAC) (rest : List UInt8) : MAC.read (address.bytes ++ rest) = .ok (address, rest) :=
  MAC.read_bytes address rest

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
  let mac ← unwrap (MAC.parse "AA:bB:cC:01:02:ff")
  ensure (mac.render == "aa:bb:cc:01:02:ff" && (← unwrap (MAC.parse mac.render)) == mac)
    "MAC addresses must accept mixed hex case and render canonically."
  for text in ["", "aa:bb:cc:dd:ee", "aa:bb:cc:dd:ee:ff:00", "a:bb:cc:dd:ee:ff",
      "ag:bb:cc:dd:ee:ff", "aabbccddeeff", "aa:bb:cc:dd:ee:ff "] do
    reject (MAC.parse text) "Malformed MAC text must be rejected."
  let identity : EAP.Decoded := ⟨.request 255 1 [97], [170, 187]⟩
  let tls : EAP.Decoded := ⟨.response 0 13 [192, 0, 0, 0, 3, 1, 2, 3], []⟩
  for version in [Version.v1, .v2, .v3] do
    for body in [Body.start, .logoff, .eap identity, .eap tls, .eap ⟨.success 42, []⟩] do
      for padding in [[], [0, 255, 136, 142]] do
        let value : EthernetFrame := ⟨group, peer, ⟨version, body⟩, padding⟩
        let bytes ← unwrap (encodeEthernet value)
        let decoded ← unwrap (decodeEthernet bytes)
        ensure (decoded == value && (← unwrap (parseHex (bytesToHex bytes))) == value)
          "Ethernet addresses, versions, EAP data, and both padding layers must round-trip."
  let padded : EthernetFrame := ⟨authenticator, peer, ⟨.v2, .eap identity⟩, List.replicate 34 0⟩
  let bytes ← unwrap (encodeEthernet padded)
  ensure (bytes.length == 60 && (bytes.drop 12).take 6 == [136, 142, 2, 0, 0, 8])
    "EAPOL must count inner EAP padding while excluding outer Ethernet padding."
  let decoded ← unwrap (parseHex (bytesToHex bytes))
  ensure (decoded.padding.length == 34)
    "Outer Ethernet padding must remain separate from the EAPOL body."
  match decoded.frame.body with
  | .eap value =>
    ensure (value.packet == identity.packet && value.padding == [170, 187])
      "RFC EAP padding inside the EAPOL body must remain distinct."
  | _ => throw (IO.userError "Expected the padded Identity request.")
  for text in ["0", "0x00", "00 00", "00\n00", "gg", "０0"] do
    reject (bytesFromHex text) "Hex bytes must reject odd, nonhex, prefixed, or spaced input."
  reject (parseHex "") "Empty hexadecimal input is not an Ethernet frame."
  for bytes in ([[], [2], [2, 0, 0], [0, 1, 0, 0], [4, 1, 0, 0], [2, 3, 0, 0],
      [2, 4, 0, 0], [2, 5, 0, 0], [2, 1, 0, 1, 0], [2, 2, 0, 1, 0],
      [2, 0, 0, 5, 3, 7, 0, 4], [2, 0, 0, 0]] : List (List UInt8)) do
    reject (decode bytes) "Malformed, unsupported, or truncated EAPOL structure must not decode."
  reject (decode [2, 0, 0, 4, 1, 7, 0, 5, 13])
    "Ethernet padding cannot supply EAP bytes omitted from the enclosing EAPOL body."
  reject (decode [2, 0, 0, 5, 1, 7, 0, 6, 13, 99])
    "An inner EAP length cannot read beyond the declared outer EAPOL body."
  let bare := group.bytes ++ peer.bytes
  for raw in ([[1, 1, 0, 0, 255, 170], [3, 2, 0, 0, 0],
      [2, 0, 0, 8, 1, 255, 0, 6, 200, 0, 170, 187, 136, 142],
      [3, 0, 1, 2, 2, 128, 1, 0, 13] ++ List.replicate 251 170 ++ [0, 255, 136]] :
      List (List UInt8)) do
    let value ← unwrap (decode raw)
    ensure ((← unwrap (encodeDecoded value)) == raw)
      "Accepted EAPOL bytes must re-encode exactly across both padding boundaries."
    let wire := bare ++ [136, 142] ++ raw
    let value ← unwrap (decodeEthernet wire)
    ensure ((← unwrap (encodeEthernet value)) == wire)
      "Accepted Ethernet bytes must preserve MACs, EtherType, nested lengths, and padding exactly."
  reject (decodeEthernet (bare ++ [8, 0, 2, 1, 0, 0])) "IPv4 EtherType cannot be decoded as EAPOL."
  reject (decodeEthernet (bare ++ [129, 0, 0, 1, 136, 142, 2, 1, 0, 0]))
    "VLAN encapsulation requires a separate supported profile."
  reject (decodeEthernet (bare ++ [136])) "A missing EtherType byte must be rejected."
  let start ← unwrap (decode [3, 1, 0, 0, 0, 0, 0])
  ensure (start.frame.body == .start && start.padding == [0, 0, 0])
    "Start padding outside its zero-length body must remain accepted."
  let huge : Frame := ⟨.v2, .eap ⟨.request 1 13 (List.replicate 65530 0), [0]⟩⟩
  reject (encode huge) "Inner EAP padding must also count toward the outer 16-bit body limit."
  IO.println "Ethernet EAPOL codec tests passed."

end NetlibTest.EAPOL
