import Netlib.Protocol.TCP.Options

/-!
TCP framing preserves received reserved bits, options, and the checksum word.
The IPv4 pseudoheader checksum is mandatory. This rule also applies when its word is zero.
https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1
-/

namespace Netlib.Protocol.TCP

open InternetChecksum

structure Segment where
  sourcePort : Word
  destinationPort : Word
  sequence : Seq
  acknowledgment : Seq
  reserved : Nibble
  flags : UInt8
  window : Word
  checksum : Word
  urgentPointer : Word
  options : List UInt8
  payload : List UInt8
  deriving Repr, BEq, DecidableEq

namespace Segment

def headerLength (segment : Segment) : Nat := 20 + segment.options.length
def wireLength (segment : Segment) : Nat := segment.headerLength + segment.payload.length
def dataOffset (segment : Segment) : Nat := 5 + segment.options.length / 4

def Encodable (segment : Segment) : Prop :=
  segment.options.length ≤ 40 ∧ segment.options.length % 4 = 0 ∧
    Options.valid segment.options = true ∧ segment.wireLength < 65536

instance (segment : Segment) : Decidable segment.Encodable :=
  inferInstanceAs (Decidable (segment.options.length ≤ 40 ∧ segment.options.length % 4 = 0 ∧
    Options.valid segment.options = true ∧ segment.wireLength < 65536))

def lengthWord (segment : Segment) : Word :=
  ⟨segment.wireLength % 65536, Nat.mod_lt _ (by decide)⟩

def offsetByte (segment : Segment) : UInt8 := UInt8.ofNat (segment.dataOffset * 16 + segment.reserved.val)

def headerPrefix (segment : Segment) : List UInt8 :=
  wordBytes segment.sourcePort ++ wordBytes segment.destinationPort ++ seqBytes segment.sequence ++
    seqBytes segment.acknowledgment ++ [segment.offsetByte, segment.flags] ++ wordBytes segment.window

def suffix (segment : Segment) : List UInt8 :=
  wordBytes segment.urgentPointer ++ segment.options ++ segment.payload

def encodeBytes (segment : Segment) : List UInt8 :=
  segment.headerPrefix ++ wordBytes segment.checksum ++ segment.suffix

@[simp] theorem headerPrefix_length (segment : Segment) : segment.headerPrefix.length = 16 := by simp [headerPrefix]

theorem encodeBytes_length (segment : Segment) : segment.encodeBytes.length = segment.wireLength := by
  simp [encodeBytes, suffix, wireLength, headerLength]
  omega

theorem lengthWord_val (segment : Segment) (bounded : segment.Encodable) :
    segment.lengthWord.val = segment.wireLength := Nat.mod_eq_of_lt bounded.2.2.2

theorem dataOffset_bounds (segment : Segment) (bounded : segment.Encodable) :
    5 ≤ segment.dataOffset ∧ segment.dataOffset ≤ 15 := by
  unfold dataOffset
  have := bounded.1
  omega

theorem optionCount (segment : Segment) (bounded : segment.Encodable) :
    (segment.dataOffset - 5) * 4 = segment.options.length := by
  unfold dataOffset
  have := bounded.2.1
  omega

theorem headerLength_offset (segment : Segment) (bounded : segment.Encodable) :
    segment.headerLength = segment.dataOffset * 4 := by
  unfold headerLength dataOffset
  have := bounded.2.1
  omega

theorem offsetByte_val (segment : Segment) (bounded : segment.Encodable) :
    segment.offsetByte.toNat = segment.dataOffset * 16 + segment.reserved.val := by
  have := segment.dataOffset_bounds bounded
  have := segment.reserved.isLt
  simp only [offsetByte, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem offsetByte_high (segment : Segment) (bounded : segment.Encodable) :
    segment.offsetByte.toNat / 16 = segment.dataOffset := by
  rw [segment.offsetByte_val bounded]
  have := segment.reserved.isLt
  omega

theorem offsetByte_low (segment : Segment) (bounded : segment.Encodable) :
    segment.offsetByte.toNat % 16 = segment.reserved.val := by
  rw [segment.offsetByte_val bounded]
  have := segment.reserved.isLt
  omega

end Segment

def pseudoHeader (source destination : Packet.Address) (length : Word) : List UInt8 :=
  IPv4.addressBytes source ++ IPv4.addressBytes destination ++ [0, 6] ++ wordBytes length

@[simp] theorem pseudoHeader_length (source destination : Packet.Address) (length : Word) :
    (pseudoHeader source destination length).length = 12 := by simp [pseudoHeader, IPv4.addressBytes]

def checksumPrefix (source destination : Packet.Address) (segment : Segment) : List UInt8 :=
  pseudoHeader source destination segment.lengthWord ++ segment.headerPrefix

@[simp] theorem checksumPrefix_length (source destination : Packet.Address) (segment : Segment) :
    (checksumPrefix source destination segment).length = 28 := by simp [checksumPrefix]

def checksumBytes (source destination : Packet.Address) (segment : Segment) : List UInt8 :=
  checksumPrefix source destination segment ++ wordBytes segment.checksum ++ segment.suffix

theorem checksumBytes_eq (source destination : Packet.Address) (segment : Segment) :
    checksumBytes source destination segment = pseudoHeader source destination segment.lengthWord ++ segment.encodeBytes := by
  simp [checksumBytes, checksumPrefix, Segment.encodeBytes, List.append_assoc]

def checksumAccepts (source destination : Packet.Address) (segment : Segment) : Bool :=
  InternetChecksum.valid (checksumBytes source destination segment)

def decode (source destination : Packet.Address) : List UInt8 → Except String Segment
  | s0 :: s1 :: d0 :: d1 :: q0 :: q1 :: q2 :: q3 :: a0 :: a1 :: a2 :: a3 :: control :: flags ::
      w0 :: w1 :: c0 :: c1 :: u0 :: u1 :: tail =>
    let offset := control.toNat / 16
    if 5 ≤ offset then
      let count := (offset - 5) * 4
      if count ≤ tail.length then
        let segment : Segment := ⟨read16 s0 s1, read16 d0 d1, readSeq q0 q1 q2 q3, readSeq a0 a1 a2 a3,
          ⟨control.toNat % 16, Nat.mod_lt _ (by decide)⟩, flags, read16 w0 w1, read16 c0 c1,
          read16 u0 u1, tail.take count, tail.drop count⟩
        if segment.Encodable then
          if checksumAccepts source destination segment = true then .ok segment
          else .error "The TCP pseudoheader checksum is invalid."
        else .error "The TCP header options or segment length is invalid."
      else .error "The TCP data offset exceeds the available header bytes."
    else .error "The TCP data offset must include its twenty-byte fixed header."
  | _ => .error "A TCP segment requires a twenty-byte fixed header."

def encode (source destination : Packet.Address) (segment : Segment) : Except String (List UInt8) :=
  if segment.Encodable then
    if checksumAccepts source destination segment = true then .ok segment.encodeBytes
    else .error "The TCP pseudoheader checksum is invalid."
  else .error "The TCP header options or segment length is invalid."

def rechecksum (source destination : Packet.Address) (segment : Segment) : Segment :=
  { segment with checksum := InternetChecksum.checksum (checksumPrefix source destination segment ++ [0, 0] ++ segment.suffix) }

def computed (source destination : Packet.Address) (segment : Segment) : Segment :=
  rechecksum source destination { segment with reserved := 0 }

theorem rechecksum_valid (source destination : Packet.Address) (segment : Segment) :
    InternetChecksum.valid (checksumBytes source destination (rechecksum source destination segment)) = true := by
  have synthesized := synthesize_valid (checksumPrefix source destination segment) segment.suffix
    (by rw [checksumPrefix_length])
  simpa only [rechecksum, checksumBytes, checksumPrefix, Segment.lengthWord, Segment.wireLength,
    Segment.headerLength, Segment.headerPrefix, Segment.offsetByte, Segment.dataOffset, Segment.suffix] using synthesized

theorem rechecksum_accepts (source destination : Packet.Address) (segment : Segment) :
    checksumAccepts source destination (rechecksum source destination segment) = true :=
  rechecksum_valid source destination segment

theorem rechecksum_encodable (source destination : Packet.Address) (segment : Segment) (bounded : segment.Encodable) :
    (rechecksum source destination segment).Encodable := by
  simpa only [Segment.Encodable, rechecksum, Segment.wireLength, Segment.headerLength] using bounded

theorem computed_valid (source destination : Packet.Address) (segment : Segment) :
    InternetChecksum.valid (checksumBytes source destination (computed source destination segment)) = true :=
  rechecksum_valid source destination _

theorem computed_accepts (source destination : Packet.Address) (segment : Segment) :
    checksumAccepts source destination (computed source destination segment) = true := computed_valid source destination segment

theorem computed_encodable (source destination : Packet.Address) (segment : Segment) (bounded : segment.Encodable) :
    (computed source destination segment).Encodable := by
  simpa only [Segment.Encodable, computed, rechecksum, Segment.wireLength, Segment.headerLength] using bounded

@[simp] theorem rechecksum_options (source destination : Packet.Address) (segment : Segment) :
    (rechecksum source destination segment).options = segment.options := by simp only [rechecksum]

@[simp] theorem rechecksum_payload (source destination : Packet.Address) (segment : Segment) :
    (rechecksum source destination segment).payload = segment.payload := by simp only [rechecksum]

@[simp] theorem rechecksum_reserved (source destination : Packet.Address) (segment : Segment) :
    (rechecksum source destination segment).reserved = segment.reserved := by simp only [rechecksum]

@[simp] theorem rechecksum_headerLength (source destination : Packet.Address) (segment : Segment) :
    (rechecksum source destination segment).headerLength = segment.headerLength := by simp only [rechecksum, Segment.headerLength]

@[simp] theorem rechecksum_wireLength (source destination : Packet.Address) (segment : Segment) :
    (rechecksum source destination segment).wireLength = segment.wireLength := by simp only [rechecksum, Segment.wireLength, Segment.headerLength]

@[simp] theorem computed_reserved (source destination : Packet.Address) (segment : Segment) :
    (computed source destination segment).reserved = 0 := rfl

theorem encode_conditions (source destination : Packet.Address) (segment : Segment) (bytes : List UInt8)
    (encoded : encode source destination segment = .ok bytes) :
    segment.Encodable ∧ checksumAccepts source destination segment = true ∧ bytes = segment.encodeBytes := by
  unfold encode at encoded
  split at encoded
  · split at encoded
    · cases encoded
      exact ⟨by assumption, by assumption, rfl⟩
    · cases encoded
  · cases encoded

private theorem readSeq_bytes (value : Seq) :
    readSeq (highByte (IPv4.highWord value.bits)) (lowByte (IPv4.highWord value.bits))
      (highByte (IPv4.lowWord value.bits)) (lowByte (IPv4.lowWord value.bits)) = value := by
  cases value
  apply Seq.ext
  exact congrArg Fin.val (read32_bytes _)

theorem decode_encodeBytes (source destination : Packet.Address) (segment : Segment)
    (bounded : segment.Encodable) (checked : checksumAccepts source destination segment = true) :
    decode source destination segment.encodeBytes = .ok segment := by
  have offset := segment.dataOffset_bounds bounded
  have count := segment.optionCount bounded
  simp only [Segment.encodeBytes, Segment.headerPrefix, Segment.suffix, seqBytes, word32Bytes,
    IPv4.addressBytes, wordBytes, List.cons_append, List.nil_append, decode, read16_bytes, readSeq_bytes]
  rw [segment.offsetByte_high bounded]
  simp only [offset.1, ↓reduceIte, count, List.length_append, Nat.le_add_right,
    List.take_left, List.drop_left, segment.offsetByte_low bounded]
  simp only [bounded, ↓reduceIte, checked]

theorem decode_encode (source destination : Packet.Address) (segment : Segment) (bytes : List UInt8)
    (encoded : encode source destination segment = .ok bytes) : decode source destination bytes = .ok segment := by
  obtain ⟨bounded, checked, rfl⟩ := encode_conditions source destination segment bytes encoded
  exact decode_encodeBytes source destination segment bounded checked

theorem decode_fields (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) :
    segment.Encodable ∧ checksumAccepts source destination segment = true ∧ segment.encodeBytes = bytes := by
  unfold decode at accepted
  split at accepted
  · rename_i s0 s1 d0 d1 q0 q1 q2 q3 a0 a1 a2 a3 control flags w0 w1 c0 c1 u0 u1 tail
    dsimp only at accepted
    split at accepted
    · rename_i offset
      split at accepted
      · rename_i fits
        split at accepted
        · rename_i bounded
          split at accepted
          · rename_i checked
            cases accepted
            refine ⟨bounded, checked, ?_⟩
            have count : (tail.take ((control.toNat / 16 - 5) * 4)).length = (control.toNat / 16 - 5) * 4 :=
              List.length_take_of_le fits
            have restored : UInt8.ofNat ((5 + ((control.toNat / 16 - 5) * 4) / 4) * 16 + control.toNat % 16) = control := by
              apply UInt8.toNat_inj.mp
              simp only [UInt8.toNat_ofNat']
              have := control.toNat_lt
              have := Nat.mod_add_div control.toNat 16
              omega
            simp only [Segment.encodeBytes, Segment.headerPrefix, Segment.suffix, wordBytes,
              seqBytes_readSeq, highByte_read16, lowByte_read16, Segment.offsetByte, Segment.dataOffset,
              count, List.cons_append, List.nil_append]
            rw [restored, List.take_append_drop]
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

theorem encode_decode (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) : encode source destination segment = .ok bytes := by
  obtain ⟨bounded, checked, exactBytes⟩ := decode_fields source destination bytes segment accepted
  simp [encode, bounded, checked, exactBytes]

theorem decode_checksum (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) :
    InternetChecksum.valid (pseudoHeader source destination segment.lengthWord ++ bytes) = true := by
  have checked := (decode_fields source destination bytes segment accepted).2.1
  rw [checksumAccepts, checksumBytes_eq, (decode_fields source destination bytes segment accepted).2.2] at checked
  exact checked

theorem decode_length (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) : bytes.length = segment.wireLength := by
  rw [← (decode_fields source destination bytes segment accepted).2.2]
  exact segment.encodeBytes_length

theorem decode_header_bounds (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) :
    20 ≤ segment.headerLength ∧ segment.headerLength ≤ 60 ∧ segment.headerLength = segment.dataOffset * 4 := by
  have bounded := (decode_fields source destination bytes segment accepted).1
  refine ⟨?_, ?_, segment.headerLength_offset bounded⟩
  · unfold Segment.headerLength; omega
  · unfold Segment.headerLength; have := bounded.1; omega

theorem decode_options (source destination : Packet.Address) (bytes : List UInt8) (segment : Segment)
    (accepted : decode source destination bytes = .ok segment) : Options.valid segment.options = true :=
  (decode_fields source destination bytes segment accepted).1.2.2.1

end Netlib.Protocol.TCP
