import Netlib.Check.Wire
import Netlib.Protocol.ICMP
import Netlib.Protocol.ICMPNAT

namespace Netlib.Check.ICMPError

open Protocol

structure Checked (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  ip : IPv4.Decoded
  icmp : ICMP.Decoded
  quote : IPv4Quote.Decoded
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  network : IPv4.decode envelope.payload = .ok ip
  protocol : ip.packet.protocol = Packet.Protocol.icmp
  transport : ICMP.decode ip.packet.payload = .ok icmp
  quotation : IPv4Quote.decode icmp.message.quote = .ok quote
  completeUDP : quote.declaredLength.val = quote.packet.wireLength →
    ∃ datagram, UDP.decode quote.packet.source quote.packet.destination quote.packet.payload = .ok datagram

def checkBytes (bytes : List UInt8) : Except String (Checked bytes) :=
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => .error error
  | .ok envelope =>
    match network : IPv4.decode envelope.payload with
    | .error error => .error error
    | .ok ip =>
      if protocol : ip.packet.protocol = Packet.Protocol.icmp then
        match transport : ICMP.decode ip.packet.payload with
        | .error error => .error error
        | .ok icmp =>
          match quotation : IPv4Quote.decode icmp.message.quote with
          | .error error => .error error
          | .ok quote =>
            if complete : quote.declaredLength.val = quote.packet.wireLength then
              match datagram : UDP.decode quote.packet.source quote.packet.destination quote.packet.payload with
              | .error error => .error error
              | .ok value => .ok ⟨envelope, ip, icmp, quote, ethernet, network, protocol, transport, quotation,
                  fun _ => ⟨value, datagram⟩⟩
            else .ok ⟨envelope, ip, icmp, quote, ethernet, network, protocol, transport, quotation,
              fun equality => False.elim (complete equality)⟩
      else .error "Require outer IPv4 protocol ICMP."

abbrev Value := IPv4.Packet × ICMP.Kind × IPv4.Packet × InternetChecksum.Word

def Checked.value (checked : Checked bytes) : Value :=
  ({ checked.ip.packet with payload := [] }, checked.icmp.message.kind,
    checked.quote.packet, checked.quote.declaredLength)

def Checked.complete (checked : Checked bytes) : Bool :=
  decide (checked.quote.declaredLength.val = checked.quote.packet.wireLength)

def Checked.encode (checked : Checked bytes) : Except String (List UInt8) := do
  let payload ← IPv4.encodeDecoded checked.ip
  return Import.EthernetIPv4.encode { checked.envelope with payload }

theorem Checked.encode_eq (checked : Checked bytes) : checked.encode = .ok bytes := by
  simp only [Checked.encode, IPv4.encode_decode _ _ checked.network, bind, Except.bind]
  simpa only [pure, Except.pure] using
    congrArg Except.ok (Import.EthernetIPv4.encode_decode bytes checked.envelope checked.ethernet)

theorem Checked.quote_valid (checked : Checked bytes) : checked.quote.Valid :=
  (IPv4Quote.decode_fields _ _ checked.quotation).1

theorem Checked.udp_checksum_verified (checked : Checked bytes)
    (complete : checked.quote.declaredLength.val = checked.quote.packet.wireLength)
    (present : ICMPNAT.quotedChecksum checked.quote.packet.payload ≠ 0) :
    ∃ datagram, UDP.decode checked.quote.packet.source checked.quote.packet.destination
      checked.quote.packet.payload = .ok datagram ∧
      InternetChecksum.valid (UDP.pseudoHeader checked.quote.packet.source checked.quote.packet.destination
        datagram.lengthWord ++ checked.quote.packet.payload) = true := by
  obtain ⟨datagram, decoded⟩ := checked.completeUDP complete
  have fields := UDP.decode_fields _ _ _ _ decoded
  have checksum : datagram.checksum ≠ 0 := by
    intro zero
    apply present
    rw [← fields.2.2]
    simpa [UDP.Datagram.encodeBytes, InternetChecksum.wordBytes, ICMPNAT.quotedChecksum,
      InternetChecksum.read16_bytes] using zero
  exact ⟨datagram, decoded, UDP.decode_verified _ _ _ _ decoded checksum⟩

def Checked.renderJson (checked : Checked bytes) : Lean.Json := Lean.Json.mkObj [
  ("source", Lean.toJson checked.ip.packet.source.val),
  ("destination", Lean.toJson checked.ip.packet.destination.val),
  ("ttl", Lean.toJson checked.ip.packet.ttl.toNat),
  ("tos", Lean.toJson checked.ip.packet.tos.toNat),
  ("identification", Lean.toJson checked.ip.packet.identification.val),
  ("kind", Lean.toJson (match checked.icmp.message.kind with
    | .timeExceeded => "timeExceeded" | .fragmentationNeeded _ => "fragmentationNeeded")),
  ("mtu", Lean.toJson (match checked.icmp.message.kind with
    | .timeExceeded => none | .fragmentationNeeded mtu => some mtu.val)),
  ("quoteHeader", Import.PacketFields.headerJson (IPv4Quote.header checked.quote)),
  ("quoteLength", Lean.toJson (IPv4Quote.bytes checked.quote).length),
  ("declaredLength", Lean.toJson checked.quote.declaredLength.val),
  ("quotePayloadHex", Lean.toJson (Import.EAPOL.bytesToHex checked.quote.packet.payload)),
  ("quotedUDPComplete", Lean.toJson checked.complete),
  ("quotedUDPChecksumVerified", Lean.toJson
    (checked.complete && ICMPNAT.quotedChecksum checked.quote.packet.payload != 0)),
  ("rawEthernet", Lean.toJson (Import.EAPOL.bytesToHex bytes))]

end Netlib.Check.ICMPError
