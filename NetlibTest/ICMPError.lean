import Netlib.Check.ICMPError

namespace NetlibTest.ICMPError

open Netlib Netlib.Protocol

example (checked : Check.ICMPError.Checked bytes) : checked.encode = .ok bytes := checked.encode_eq

example (checked : Check.ICMPError.Checked bytes) : checked.quote.Valid := checked.quote_valid

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError message)
  | .error _ => pure ()

private def source : Packet.Address := 3221225985
private def destination : Packet.Address := 3325256706

private def frame (quote : List UInt8) (kind : ICMP.Kind := .timeExceeded)
    (protocol : Packet.Protocol := Packet.Protocol.icmp) : Except String (List UInt8) := do
  let payload := ICMP.encode ⟨kind, quote⟩
  let outer ← IPv4.encode ⟨222, 987, false, 64, protocol, destination, source, payload⟩
  return Import.EthernetIPv4.encode ⟨⟨2, 0, 0, 0, 0, 1⟩, ⟨2, 0, 0, 0, 0, 2⟩, outer⟩

private def repairHeader (wire : List UInt8) : List UInt8 :=
  let blank := wire.take 10 ++ [0, 0] ++ (wire.drop 12).take 8
  wire.take 10 ++ InternetChecksum.wordBytes (InternetChecksum.checksum blank) ++ wire.drop 12

def run : IO Unit := do
  let udp ← unwrap (UDP.encodeComputed source destination 12345 53 [1, 2, 3, 4, 5])
  let original ← unwrap (IPv4.encode ⟨167, 4321, true, 1, Packet.Protocol.udp, source, destination, udp⟩)
  for kind in [ICMP.Kind.timeExceeded, .fragmentationNeeded 1280] do
    for length in [28, 29, 32, 33] do
      let wire ← unwrap (frame (original.take length) kind)
      let checked ← unwrap (Check.ICMPError.checkBytes wire)
      ensure (checked.icmp.message.kind == kind && checked.quote.declaredLength.val == original.length &&
          checked.quote.packet.payload == udp.take (length - 20) && checked.complete == (length == original.length) &&
          (← unwrap checked.encode) == wire)
        "Checked ICMP errors must preserve kind, exact quote prefix, completeness, and original declared lengths."
      let rendered := checked.renderJson
      ensure ((← unwrap (rendered.getObjVal? "quotedUDPChecksumVerified" >>= Lean.Json.getBool?)) ==
          (length == original.length))
        "Only complete nonzero-checksum UDP quotations may report complete checksum verification."
      let padded ← unwrap (Check.ICMPError.checkBytes (wire ++ [0, 255, 0]))
      ensure (padded.value == checked.value && (← unwrap padded.encode) == wire ++ [0, 255, 0])
        "Ethernet padding must be preserved without changing semantic ICMP comparison."
      reject (Check.ICMPError.checkBytes ((wire.toArray.modify 36 (· + 1)).toList))
        "A corrupted ICMP checksum must fail."
      reject (Check.ICMPError.checkBytes ((wire.toArray.modify 44 (· + 1)).toList))
        "A corrupted quoted IPv4 checksum must fail."
      reject (Check.ICMPError.checkBytes (wire.take (wire.length - 1)))
        "A truncated outer ICMP datagram must fail."
  let changedUDP := (original.toArray.modify 26 (· + 1)).toList
  let limited ← unwrap (Check.ICMPError.checkBytes (← unwrap (frame (changedUDP.take 28))))
  ensure (!limited.complete && ICMPNAT.quotedChecksum limited.quote.packet.payload != 0)
    "A partial quote preserves unvalidated UDP checksum bytes."
  reject (Check.ICMPError.checkBytes (← unwrap (frame changedUDP)))
    "A complete quoted UDP datagram must pass its pseudoheader checksum."
  for position in [0, 6, 7, 9, 24, 25] do
    let quote := repairHeader ((original.toArray.modify position (· + 1)).toList)
    reject (Check.ICMPError.checkBytes (← unwrap (frame quote)))
      "Unsupported quote versions, flags, protocols, and lengths must fail despite repaired outer checksums."
  reject (Check.ICMPError.checkBytes (← unwrap (frame (original.take 27))))
    "A quote must contain its complete IPv4 and UDP headers."
  reject (Check.ICMPError.checkBytes (← unwrap (frame original .timeExceeded Packet.Protocol.udp)))
    "The outer IPv4 protocol must identify ICMP."
  let omitted ← unwrap (UDP.encode source destination ⟨12345, 53, 0, [1, 2, 3]⟩)
  let omittedIP ← unwrap (IPv4.encode ⟨0, 0, false, 1, Packet.Protocol.udp, source, destination, omitted⟩)
  let checked ← unwrap (Check.ICMPError.checkBytes (← unwrap (frame omittedIP)))
  ensure (checked.complete && !(← unwrap (checked.renderJson.getObjVal? "quotedUDPChecksumVerified" >>= Lean.Json.getBool?)))
    "A complete quotation with an omitted UDP checksum must keep omission distinct from validation."
  IO.println "Checked ICMP error bytes tests passed."

end NetlibTest.ICMPError
