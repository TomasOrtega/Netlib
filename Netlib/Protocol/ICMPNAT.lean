import Netlib.Protocol.IPv4Quote
import Netlib.Protocol.ChecksumRewrite

namespace Netlib.Protocol.ICMPNAT

open InternetChecksum

/-- Only words changed by tuple translation enter the UDP checksum delta. -/
def tupleTotal (header : Packet.Header) : Nat :=
  total (IPv4.addressBytes header.source ++ IPv4.addressBytes header.destination ++
    wordBytes header.sourcePort ++ wordBytes header.destinationPort)

def patchPayload (old target : Packet.Header) : List UInt8 → List UInt8
  | _ :: _ :: _ :: _ :: l0 :: l1 :: c0 :: c1 :: rest =>
    wordBytes target.sourcePort ++ wordBytes target.destinationPort ++ [l0, l1] ++
      wordBytes (ChecksumRewrite.update (read16 c0 c1) (tupleTotal old) (tupleTotal target)) ++ rest
  | payload => payload

def recompute (quote : IPv4Quote.Decoded) : IPv4Quote.Decoded :=
  { quote with checksum := checksum (IPv4Quote.headerBytes { quote with checksum := 0 }) }

def patch (quote : IPv4Quote.Decoded) (target : Packet.Header) : IPv4Quote.Decoded :=
  recompute { quote with packet := { quote.packet with
    source := target.source, destination := target.destination, protocol := target.protocol,
    payload := patchPayload (IPv4Quote.header quote) target quote.packet.payload } }

@[simp] theorem recompute_packet (quote : IPv4Quote.Decoded) : (recompute quote).packet = quote.packet := rfl
@[simp] theorem recompute_declaredLength (quote : IPv4Quote.Decoded) :
    (recompute quote).declaredLength = quote.declaredLength := rfl

@[simp] theorem patch_declaredLength (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).declaredLength = quote.declaredLength := rfl

@[simp] theorem patch_source (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.source = target.source := rfl

@[simp] theorem patch_destination (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.destination = target.destination := rfl

@[simp] theorem patch_protocol (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.protocol = target.protocol := rfl

@[simp] theorem patch_payload (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.payload = patchPayload (IPv4Quote.header quote) target quote.packet.payload := rfl

theorem patch_metadata (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.tos = quote.packet.tos ∧
    (patch quote target).packet.identification = quote.packet.identification ∧
    (patch quote target).packet.dontFragment = quote.packet.dontFragment ∧
    (patch quote target).packet.ttl = quote.packet.ttl := ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem patchPayload_length (old target : Packet.Header) (payload : List UInt8) :
    (patchPayload old target payload).length = payload.length := by
  unfold patchPayload
  split <;> simp [wordBytes]

@[simp] theorem patchPayload_udpLength (old target : Packet.Header) (payload : List UInt8) :
    IPv4Quote.udpLength? (patchPayload old target payload) = IPv4Quote.udpLength? payload := by
  unfold patchPayload
  split
  · simp [wordBytes, IPv4Quote.udpLength?]
  · rfl

theorem patchPayload_appPrefix (old target : Packet.Header) (payload : List UInt8) :
    (patchPayload old target payload).drop 8 = payload.drop 8 := by
  unfold patchPayload
  split <;> simp [wordBytes]

theorem patch_appPrefix (quote : IPv4Quote.Decoded) (target : Packet.Header) :
    (patch quote target).packet.payload.drop 8 = quote.packet.payload.drop 8 :=
  patchPayload_appPrefix _ _ _

private theorem payload_header (quote : IPv4Quote.Decoded) (valid : quote.Valid) :
    ∃ s0 s1 d0 d1 l0 l1 c0 c1 rest,
      quote.packet.payload = s0 :: s1 :: d0 :: d1 :: l0 :: l1 :: c0 :: c1 :: rest := by
  have length := valid.2.2.2.1
  unfold IPv4Quote.udpLength? at length
  split at length
  · exact ⟨_, _, _, _, _, _, _, _, _, by assumption⟩
  · cases length

theorem patch_header (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    IPv4Quote.header (patch quote target) = target := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
  simp [IPv4Quote.header, patch, recompute, patchPayload, shape, wordBytes, read16_bytes]

private theorem headerBytes_checksum (quote : IPv4Quote.Decoded) (value : Word) :
    IPv4Quote.headerBytes { quote with checksum := value } =
      IPv4Quote.headerPrefix quote ++ wordBytes value ++ IPv4.headerSuffix quote.packet := by
  simp only [IPv4Quote.headerBytes, IPv4Quote.headerPrefix]

private theorem recompute_checksum (quote : IPv4Quote.Decoded) :
    (recompute quote).checksum = checksum (IPv4Quote.headerBytes { quote with checksum := 0 }) := rfl

theorem recompute_checked (quote : IPv4Quote.Decoded) :
    valid (IPv4Quote.headerBytes (recompute quote)) = true := by
  have samePrefix : IPv4Quote.headerPrefix (recompute quote) = IPv4Quote.headerPrefix quote := by
    simp only [IPv4Quote.headerPrefix, recompute_packet, recompute_declaredLength]
    rfl
  rw [IPv4Quote.headerBytes, samePrefix, recompute_checksum, recompute_packet, headerBytes_checksum, wordBytes_zero]
  exact synthesize_valid (IPv4Quote.headerPrefix quote) (IPv4.headerSuffix quote.packet)
    (by simp [IPv4Quote.headerPrefix])

theorem patch_valid (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header)
    (protocol : target.protocol = Packet.Protocol.udp) : (patch quote target).Valid := by
  refine ⟨valid.1, ?_, protocol, ?_, recompute_checked _⟩
  · simpa only [patch_payload, patchPayload_length, patch_declaredLength] using valid.2.1
  · simpa only [patch_payload, patchPayload_udpLength, patch_declaredLength] using valid.2.2.2.1

/-- The UDP checksum field remains meaningful even when the quoted payload is incomplete. -/
def quotedChecksum : List UInt8 → Word
  | _ :: _ :: _ :: _ :: _ :: _ :: c0 :: c1 :: _ => read16 c0 c1
  | _ => 0

theorem patch_checksum (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    quotedChecksum (patch quote target).packet.payload =
      ChecksumRewrite.update (quotedChecksum quote.packet.payload)
        (tupleTotal (IPv4Quote.header quote)) (tupleTotal target) := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
  simp [patch_payload, patchPayload, quotedChecksum, shape, wordBytes, read16_bytes]

theorem patch_omission (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    quotedChecksum (patch quote target).packet.payload = 0 ↔ quotedChecksum quote.packet.payload = 0 := by
  rw [patch_checksum quote valid target]
  exact ChecksumRewrite.update_omitted_iff _ _ _

private theorem payload_roundtrip (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    patchPayload target (IPv4Quote.header quote)
      (patchPayload (IPv4Quote.header quote) target quote.packet.payload) = quote.packet.payload := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
  simp only [shape, patchPayload, wordBytes, List.cons_append, List.nil_append,
    read16_bytes, ChecksumRewrite.update_inverse, IPv4Quote.header,
    highByte_read16, lowByte_read16]

theorem patch_roundtrip_packet (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header)
    :
    (patch (patch quote target) (IPv4Quote.header quote)).packet = quote.packet := by
  have headers := patch_header quote valid target
  have payload := payload_roundtrip quote valid target
  have originalProtocol : (IPv4Quote.header quote).protocol = quote.packet.protocol := by
    obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
    simp [IPv4Quote.header, shape]
  have originalSource : (IPv4Quote.header quote).source = quote.packet.source := by
    obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
    simp [IPv4Quote.header, shape]
  have originalDestination : (IPv4Quote.header quote).destination = quote.packet.destination := by
    obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, shape⟩ := payload_header quote valid
    simp [IPv4Quote.header, shape]
  change { (patch quote target).packet with
      source := (IPv4Quote.header quote).source, destination := (IPv4Quote.header quote).destination,
      protocol := (IPv4Quote.header quote).protocol,
      payload := patchPayload (IPv4Quote.header (patch quote target)) (IPv4Quote.header quote)
        (patch quote target).packet.payload } = quote.packet
  rw [headers, patch_payload, payload, originalProtocol, originalSource, originalDestination]
  rfl

private theorem recompute_eq (left right : IPv4Quote.Decoded) (packets : left.packet = right.packet)
    (declared : left.declaredLength = right.declaredLength) : recompute left = recompute right := by
  cases left
  cases right
  cases packets
  cases declared
  simp only [recompute, IPv4Quote.headerBytes, IPv4Quote.headerPrefix, IPv4.headerSuffix]

theorem patch_roundtrip (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    patch (patch quote target) (IPv4Quote.header quote) = recompute quote := by
  apply recompute_eq
  · exact patch_roundtrip_packet quote valid target
  · exact patch_declaredLength (patch quote target) (IPv4Quote.header quote)

end Netlib.Protocol.ICMPNAT
