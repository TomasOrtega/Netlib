import Netlib.Protocol.IPv4QuotePrefix
import Netlib.Protocol.ICMPNAT
import Netlib.Protocol.ChecksumRewriteRaw

/-!
# NAT of untrusted transport quotations

Tuple changes adjust checksum residues without validating or repairing quoted packets.
Flags, lengths, protocol, and bytes beyond the transport header remain unchanged.
-/

namespace Netlib.Protocol.ICMPPrefixNAT

open InternetChecksum

abbrev tupleTotal := ICMPNAT.tupleTotal
abbrev patchPayload := ICMPNAT.patchPayload
abbrev quotedChecksum := ICMPNAT.quotedChecksum

def addressTotal (source destination : Packet.Address) : Nat :=
  total (IPv4.addressBytes source ++ IPv4.addressBytes destination)

def patch (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) : IPv4QuotePrefix.Decoded :=
  { quote with
    packet := { quote.packet with
      source := target.source
      destination := target.destination
      payload := patchPayload (IPv4QuotePrefix.header quote) target quote.packet.payload }
    checksum := ChecksumRewriteRaw.update quote.checksum
      (addressTotal quote.packet.source quote.packet.destination)
      (addressTotal target.source target.destination) }

@[simp] theorem patch_source (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.source = target.source := rfl

@[simp] theorem patch_destination (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.destination = target.destination := rfl

@[simp] theorem patch_protocol (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.protocol = quote.packet.protocol := rfl

@[simp] theorem patch_payload (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.payload = patchPayload (IPv4QuotePrefix.header quote) target quote.packet.payload := rfl

@[simp] theorem patch_payload_length (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.payload.length = quote.packet.payload.length := ICMPNAT.patchPayload_length _ _ _

@[simp] theorem patch_declaredLength (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).declaredLength = quote.declaredLength := rfl

@[simp] theorem patch_flags (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).flags = quote.flags := rfl

theorem patch_metadata (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.tos = quote.packet.tos ∧
    (patch quote target).packet.identification = quote.packet.identification ∧
    (patch quote target).packet.dontFragment = quote.packet.dontFragment ∧
    (patch quote target).packet.ttl = quote.packet.ttl ∧
    (patch quote target).packet.protocol = quote.packet.protocol := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem patch_shape (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header) :
    (patch quote target).Shape := by
  exact ⟨by simpa using shape.1, shape.2⟩

theorem patch_appPrefix (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).packet.payload.drop 8 = quote.packet.payload.drop 8 :=
  ICMPNAT.patchPayload_appPrefix _ _ _

theorem patch_udpLength (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    IPv4Quote.udpLength? (patch quote target).packet.payload = IPv4Quote.udpLength? quote.packet.payload :=
  ICMPNAT.patchPayload_udpLength _ _ _

private theorem payload_header (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) :
    ∃ s0 s1 d0 d1 l0 l1 c0 c1 rest,
      quote.packet.payload = s0 :: s1 :: d0 :: d1 :: l0 :: l1 :: c0 :: c1 :: rest := by
  have enough := shape.1
  match equality : quote.packet.payload with
  | s0 :: s1 :: d0 :: d1 :: l0 :: l1 :: c0 :: c1 :: rest => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] |
      [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => simp [equality] at enough

theorem header_protocol (quote : IPv4QuotePrefix.Decoded) :
    (IPv4QuotePrefix.header quote).protocol = quote.packet.protocol := by
  simp only [IPv4QuotePrefix.header, IPv4Quote.header]
  split <;> rfl

theorem patch_header (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header)
    (sameProtocol : target.protocol = quote.packet.protocol) :
    IPv4QuotePrefix.header (patch quote target) = target := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, fields⟩ := payload_header quote shape
  simp [IPv4QuotePrefix.header, IPv4Quote.header, patch, patchPayload, ICMPNAT.patchPayload,
    fields, wordBytes, read16_bytes]
  rw [← sameProtocol]

theorem patch_checksum (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header) :
    quotedChecksum (patch quote target).packet.payload =
      ChecksumRewrite.update (quotedChecksum quote.packet.payload)
        (tupleTotal (IPv4QuotePrefix.header quote)) (tupleTotal target) := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, fields⟩ := payload_header quote shape
  simp [patch_payload, patchPayload, ICMPNAT.patchPayload, quotedChecksum, ICMPNAT.quotedChecksum,
    fields, wordBytes, read16_bytes]

theorem patch_omission (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header) :
    quotedChecksum (patch quote target).packet.payload = 0 ↔ quotedChecksum quote.packet.payload = 0 := by
  rw [patch_checksum quote shape target]
  exact ChecksumRewrite.update_omitted_iff _ _ _

@[simp] theorem patch_ip_checksum (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch quote target).checksum = ChecksumRewriteRaw.update quote.checksum
      (addressTotal quote.packet.source quote.packet.destination)
      (addressTotal target.source target.destination) := rfl

@[simp] theorem patch_headerPrefix (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    IPv4QuotePrefix.headerPrefix (patch quote target) = IPv4QuotePrefix.headerPrefix quote := rfl

private theorem header_context_positive (quote : IPv4QuotePrefix.Decoded) (suffix : List UInt8) :
    0 < total (IPv4QuotePrefix.headerPrefix quote ++ suffix) := by
  simp only [IPv4QuotePrefix.headerPrefix, List.append_assoc, List.cons_append, List.nil_append, total]
  change 0 < (17664 + quote.packet.tos.toNat) + _
  omega

theorem patch_ip_checksum_valid_iff (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    valid (IPv4QuotePrefix.headerBytes (patch quote target)) = true ↔
      valid (IPv4QuotePrefix.headerBytes quote) = true := by
  have oldEven : (IPv4QuotePrefix.headerPrefix quote).length % 2 = 0 := by simp
  have newEven : (IPv4QuotePrefix.headerPrefix (patch quote target)).length % 2 = 0 := by simp
  have changed : addressTotal quote.packet.source quote.packet.destination +
      total (IPv4QuotePrefix.headerPrefix (patch quote target) ++ IPv4.headerSuffix (patch quote target).packet) =
      addressTotal target.source target.destination +
        total (IPv4QuotePrefix.headerPrefix quote ++ IPv4.headerSuffix quote.packet) := by
    rw [patch_headerPrefix, total_append_even _ _ oldEven, total_append_even _ _ oldEven]
    change addressTotal quote.packet.source quote.packet.destination +
      (total (IPv4QuotePrefix.headerPrefix quote) + addressTotal target.source target.destination) =
      addressTotal target.source target.destination +
        (total (IPv4QuotePrefix.headerPrefix quote) + addressTotal quote.packet.source quote.packet.destination)
    omega
  exact ChecksumRewriteRaw.update_valid_bytes_iff quote.checksum
    (IPv4QuotePrefix.headerPrefix quote) (IPv4.headerSuffix quote.packet)
    (IPv4QuotePrefix.headerPrefix (patch quote target)) (IPv4.headerSuffix (patch quote target).packet)
    (addressTotal quote.packet.source quote.packet.destination) (addressTotal target.source target.destination)
    oldEven newEven (header_context_positive _ _) (header_context_positive _ _) changed

theorem patch_ip_checksum_valid_eq (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    valid (IPv4QuotePrefix.headerBytes (patch quote target)) = valid (IPv4QuotePrefix.headerBytes quote) := by
  have equivalent := patch_ip_checksum_valid_iff quote target
  cases old : valid (IPv4QuotePrefix.headerBytes quote) <;>
    cases new : valid (IPv4QuotePrefix.headerBytes (patch quote target)) <;> simp_all

private theorem payload_roundtrip (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header) :
    patchPayload target (IPv4QuotePrefix.header quote)
      (patchPayload (IPv4QuotePrefix.header quote) target quote.packet.payload) = quote.packet.payload := by
  obtain ⟨s0, s1, d0, d1, l0, l1, c0, c1, rest, fields⟩ := payload_header quote shape
  simp only [fields, patchPayload, ICMPNAT.patchPayload, wordBytes, List.cons_append, List.nil_append,
    read16_bytes, ChecksumRewrite.update_inverse, IPv4QuotePrefix.header, IPv4Quote.header,
    highByte_read16, lowByte_read16]

theorem patch_roundtrip_packet (quote : IPv4QuotePrefix.Decoded) (shape : quote.Shape) (target : Packet.Header)
    (sameProtocol : target.protocol = quote.packet.protocol) :
    (patch (patch quote target) (IPv4QuotePrefix.header quote)).packet = quote.packet := by
  have headers := patch_header quote shape target sameProtocol
  have payload := payload_roundtrip quote shape target
  have originalSource : (IPv4QuotePrefix.header quote).source = quote.packet.source := by
    simp only [IPv4QuotePrefix.header, IPv4Quote.header]
    split <;> rfl
  have originalDestination : (IPv4QuotePrefix.header quote).destination = quote.packet.destination := by
    simp only [IPv4QuotePrefix.header, IPv4Quote.header]
    split <;> rfl
  change { (patch quote target).packet with
      source := (IPv4QuotePrefix.header quote).source
      destination := (IPv4QuotePrefix.header quote).destination
      payload := patchPayload (IPv4QuotePrefix.header (patch quote target)) (IPv4QuotePrefix.header quote)
        (patch quote target).packet.payload } = quote.packet
  rw [headers, patch_payload, payload, originalSource, originalDestination]
  rfl

theorem patch_roundtrip_checksum_mod (quote : IPv4QuotePrefix.Decoded) (target : Packet.Header) :
    (patch (patch quote target) (IPv4QuotePrefix.header quote)).checksum.val % 65535 = quote.checksum.val % 65535 := by
  have originalSource : (IPv4QuotePrefix.header quote).source = quote.packet.source := by
    simp only [IPv4QuotePrefix.header, IPv4Quote.header]
    split <;> rfl
  have originalDestination : (IPv4QuotePrefix.header quote).destination = quote.packet.destination := by
    simp only [IPv4QuotePrefix.header, IPv4Quote.header]
    split <;> rfl
  simp only [patch_ip_checksum, patch_source, patch_destination, originalSource, originalDestination]
  exact ChecksumRewriteRaw.update_inverse_mod _ _ _

end Netlib.Protocol.ICMPPrefixNAT
