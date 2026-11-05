import Netlib.Protocol.UDP

namespace Netlib.Protocol.IPv4Quote

open InternetChecksum

structure Decoded where
  packet : IPv4.Packet
  checksum : Word
  declaredLength : Word
  deriving Repr, BEq, DecidableEq

def headerPrefix (value : Decoded) : List UInt8 :=
  [69, value.packet.tos] ++ wordBytes value.declaredLength ++ wordBytes value.packet.identification ++
    [if value.packet.dontFragment then 64 else 0, 0, value.packet.ttl, UInt8.ofNat value.packet.protocol.val]

def headerBytes (value : Decoded) : List UInt8 :=
  headerPrefix value ++ wordBytes value.checksum ++ IPv4.headerSuffix value.packet

@[simp] theorem headerBytes_length (value : Decoded) : (headerBytes value).length = 20 := by
  simp [headerBytes, headerPrefix]

def bytes (value : Decoded) : List UInt8 := headerBytes value ++ value.packet.payload

def udpLength? : List UInt8 → Option Nat
  | _ :: _ :: _ :: _ :: l0 :: l1 :: _ :: _ :: _ => some (read16 l0 l1).val
  | _ => none

def Decoded.Valid (value : Decoded) : Prop :=
  28 ≤ value.declaredLength.val ∧ value.packet.payload.length + 20 ≤ value.declaredLength.val ∧
    value.packet.protocol = Packet.Protocol.udp ∧
    udpLength? value.packet.payload = some (value.declaredLength.val - 20) ∧
    InternetChecksum.valid (headerBytes value) = true

instance (value : Decoded) : Decidable value.Valid := by unfold Decoded.Valid; infer_instance

def header (value : Decoded) : Packet.Header :=
  match value.packet.payload with
  | s0 :: s1 :: d0 :: d1 :: _ =>
    ⟨value.packet.source, value.packet.destination, value.packet.protocol, read16 s0 s1, read16 d0 d1⟩
  | _ => ⟨value.packet.source, value.packet.destination, value.packet.protocol, 0, 0⟩

def encodeDecoded (value : Decoded) : Except String (List UInt8) :=
  if value.Valid then .ok (bytes value)
  else .error "Require a checked IPv4 UDP quotation within its original declared length."

def decode : List UInt8 → Except String Decoded
  | version :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: payload => do
    if version != 69 then throw "Require quoted IPv4 version 4 and IHL 5."
    if fl != 0 || (fh != 0 && fh != 64) then throw "Quoted IPv4 fragmentation and reserved flags are unsupported."
    let value : Decoded := ⟨⟨tos, read16 ih il, fh == 64, ttl, IPv4.protocolFromByte protocol,
      IPv4.readAddress sa sb sc sd, IPv4.readAddress da db dc dd, payload⟩,
      read16 ch cl, read16 lh ll⟩
    if value.Valid then return value
    else throw "Require a checked IPv4 UDP quotation within its original declared length."
  | _ => .error "A quoted IPv4 header requires twenty bytes."

theorem decode_bytes (value : Decoded) (checked : value.Valid) : decode (bytes value) = .ok value := by
  simp only [bytes, headerBytes, headerPrefix, IPv4.headerSuffix, IPv4.addressBytes, wordBytes,
    List.cons_append, List.nil_append, decode, read16_bytes, IPv4.readAddress_bytes,
    IPv4.protocolFromByte_encode]
  cases fragment : value.packet.dontFragment
  all_goals
    have parsed : (Decoded.mk (IPv4.Packet.mk value.packet.tos value.packet.identification
      ((if value.packet.dontFragment then (64 : UInt8) else 0) == 64) value.packet.ttl value.packet.protocol
      value.packet.source value.packet.destination value.packet.payload) value.checksum value.declaredLength) = value := by
      cases value with
      | mk packet checksum length => cases packet; cases fragment; rfl
    simp only [Bool.false_eq_true, ite_false, beq_self_eq_true,
      bne_self_eq_false, Bool.false_or, Bool.false_and, ite_true, bind, Except.bind]
    simp only [fragment, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true] at parsed
    rw [parsed]
    simp [checked, pure, Except.pure]

theorem decode_encodeDecoded (value : Decoded) (wire : List UInt8)
    (encoded : encodeDecoded value = .ok wire) : decode wire = .ok value := by
  unfold encodeDecoded at encoded
  split at encoded
  · cases encoded
    exact decode_bytes value (by assumption)
  · cases encoded

theorem decode_fields (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    value.Valid ∧ bytes value = wire := by
  unfold decode at accepted
  split at accepted
  · rename_i version tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd payload
    by_cases selected : version = 69
    · subst version
      by_cases flagLow : fl = 0
      · by_cases flagHigh : fh = 0 ∨ fh = 64
        · have flags : (if fh == 64 then (64 : UInt8) else 0) = fh := by rcases flagHigh with rfl | rfl <;> decide
          have guard : (fl != 0 || (fh != 0 && fh != 64)) = false := by
            rcases flagHigh with rfl | rfl <;> simp [flagLow]
          let parsed : Decoded := ⟨⟨tos, read16 ih il, fh == 64, ttl, IPv4.protocolFromByte protocol,
            IPv4.readAddress sa sb sc sd, IPv4.readAddress da db dc dd, payload⟩, read16 ch cl, read16 lh ll⟩
          by_cases checked : parsed.Valid
          · simp [guard, checked, parsed, pure] at accepted
            cases accepted
            refine ⟨checked, ?_⟩
            change bytes parsed = _
            simp only [bytes, headerBytes, headerPrefix, IPv4.headerSuffix, parsed, flags, flagLow,
              IPv4.addressBytes_readAddress, wordBytes, highByte_read16, lowByte_read16,
              IPv4.protocolFromByte_bytes]
            rfl
          · simp [guard, checked, parsed, throw] at accepted
        · have clear : fh ≠ 0 := fun h => flagHigh (.inl h)
          have df : fh ≠ 64 := fun h => flagHigh (.inr h)
          simp [flagLow, clear, df, bind, Except.bind, throw] at accepted
      · simp [flagLow, bind, Except.bind, throw] at accepted
    · simp [selected, bind, Except.bind, throw] at accepted
  · cases accepted

theorem encode_decode (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    encodeDecoded value = .ok wire := by
  obtain ⟨checked, exactBytes⟩ := decode_fields wire value accepted
  rw [encodeDecoded, ite_eq_left checked, exactBytes]

def SourceValid (source : UDP.DecodedIPv4) : Prop :=
  source.Valid ∧ source.ip.packet.Encodable ∧
    InternetChecksum.valid (IPv4.headerBytes source.ip.packet source.ip.checksum) = true

def make (source : UDP.DecodedIPv4) (quoteLength : Nat) : Decoded :=
  ⟨{ source.ip.packet with payload := source.ip.packet.payload.take (quoteLength - 20) },
    source.ip.checksum, IPv4.lengthWord source.ip.packet⟩

theorem make_headerBytes (source : UDP.DecodedIPv4) (quoteLength : Nat) :
    headerBytes (make source quoteLength) = IPv4.headerBytes source.ip.packet source.ip.checksum := by
  simp only [headerBytes, headerPrefix, make, IPv4.headerBytes, IPv4.headerPrefix, IPv4.headerSuffix]
  rfl

theorem make_metadata (source : UDP.DecodedIPv4) (quoteLength : Nat) :
    (make source quoteLength).packet.tos = source.ip.packet.tos ∧
    (make source quoteLength).packet.identification = source.ip.packet.identification ∧
    (make source quoteLength).packet.dontFragment = source.ip.packet.dontFragment ∧
    (make source quoteLength).packet.ttl = source.ip.packet.ttl ∧
    (make source quoteLength).packet.source = source.ip.packet.source ∧
    (make source quoteLength).packet.destination = source.ip.packet.destination ∧
    (make source quoteLength).checksum = source.ip.checksum ∧
    (make source quoteLength).declaredLength = IPv4.lengthWord source.ip.packet := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem make_prefix (source : UDP.DecodedIPv4) (quoteLength : Nat) (minimum : 20 ≤ quoteLength) :
    bytes (make source quoteLength) =
      (IPv4.headerBytes source.ip.packet source.ip.checksum ++ source.ip.packet.payload).take quoteLength := by
  rw [bytes, make_headerBytes, List.take_append]
  simp only [IPv4.headerBytes_length]
  rw [List.take_of_length_le (by simpa using minimum)]
  rfl

private theorem udpLength_take (datagram : UDP.Datagram) (length : Nat) (minimum : 8 ≤ length) :
    udpLength? (datagram.encodeBytes.take length) = some datagram.lengthWord.val := by
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_add_of_le minimum
  rw [Nat.add_comm 8 tail]
  simp [UDP.Datagram.encodeBytes, wordBytes, udpLength?, read16_bytes]

theorem make_valid (source : UDP.DecodedIPv4) (valid : SourceValid source) (quoteLength : Nat)
    (minimum : 28 ≤ quoteLength) (maximum : quoteLength ≤ source.ip.packet.wireLength) :
    (make source quoteLength).Valid := by
  have declared : (IPv4.lengthWord source.ip.packet).val = source.ip.packet.wireLength :=
    Nat.mod_eq_of_lt valid.2.1
  have udp := UDP.decode_fields _ _ _ _ valid.1.2
  have size : source.datagram.wireLength = source.ip.packet.payload.length := by
    rw [← UDP.Datagram.encodeBytes_length, udp.2.2]
  refine ⟨?_, ?_, valid.1.1, ?_, ?_⟩
  · change 28 ≤ (IPv4.lengthWord source.ip.packet).val
    rw [declared]
    omega
  · change (source.ip.packet.payload.take (quoteLength - 20)).length + 20 ≤
      (IPv4.lengthWord source.ip.packet).val
    rw [declared, List.length_take]
    unfold IPv4.Packet.wireLength at maximum ⊢
    omega
  · change udpLength? (source.ip.packet.payload.take (quoteLength - 20)) =
      some ((IPv4.lengthWord source.ip.packet).val - 20)
    rw [← udp.2.2, udpLength_take _ _ (by omega), UDP.Datagram.lengthWord_val _ udp.1, declared]
    congr 1
  · exact valid.2.2

theorem make_declaredLength (source : UDP.DecodedIPv4) (valid : SourceValid source) (quoteLength : Nat) :
    (make source quoteLength).declaredLength.val = source.ip.packet.wireLength :=
  Nat.mod_eq_of_lt valid.2.1

theorem make_udpLength (source : UDP.DecodedIPv4) (valid : SourceValid source) (quoteLength : Nat)
    (minimum : 28 ≤ quoteLength) (maximum : quoteLength ≤ source.ip.packet.wireLength) :
    udpLength? (make source quoteLength).packet.payload = some source.datagram.wireLength := by
  have checked := (make_valid source valid quoteLength minimum maximum).2.2.2.1
  rw [make_declaredLength source valid quoteLength] at checked
  have udp := UDP.decode_fields _ _ _ _ valid.1.2
  have size : source.ip.packet.wireLength - 20 = source.datagram.wireLength := by
    rw [IPv4.Packet.wireLength, ← udp.2.2, UDP.Datagram.encodeBytes_length]
    omega
  simpa only [size] using checked

theorem make_header (source : UDP.DecodedIPv4) (valid : SourceValid source) (quoteLength : Nat)
    (minimum : 28 ≤ quoteLength) : header (make source quoteLength) = source.header := by
  have udp := UDP.decode_fields _ _ _ _ valid.1.2
  unfold header make
  rw [← udp.2.2]
  obtain ⟨tail, length⟩ := Nat.exists_eq_add_of_le (show 8 ≤ quoteLength - 20 by omega)
  rw [length, Nat.add_comm 8 tail]
  simp [UDP.Datagram.encodeBytes, wordBytes, read16_bytes,
    UDP.DecodedIPv4.header, valid.1.1]

theorem make_fullPayload (source : UDP.DecodedIPv4) :
    (make source source.ip.packet.wireLength).packet.payload = source.ip.packet.payload := by
  simp [make, IPv4.Packet.wireLength]

end Netlib.Protocol.IPv4Quote
