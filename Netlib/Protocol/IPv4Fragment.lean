import Netlib.Protocol.IPv4

/-!
# IHL-five IPv4 fragments

The codec preserves MF, the eight-byte offset, DF, checksum, and trailing padding.
DF cannot accompany fragmentation. Nonfinal fragments have positive aligned payloads.
Options, reassembly timers, and native overlap policies are outside this profile.
https://www.rfc-editor.org/rfc/rfc791.html
-/

namespace Netlib.Protocol.IPv4Fragment

open InternetChecksum

structure Packet extends IPv4.Packet where
  moreFragments : Bool
  offset : Fin 8192
  deriving Repr, BEq, DecidableEq

def Packet.wireLength (packet : Packet) : Nat := packet.toPacket.wireLength

def Packet.FlagsValid (packet : Packet) : Prop :=
  (packet.dontFragment = true → packet.moreFragments = false ∧ packet.offset.val = 0) ∧
    (packet.moreFragments = true → packet.payload ≠ [] ∧ packet.payload.length % 8 = 0) ∧
    (packet.offset.val ≠ 0 → packet.payload ≠ [])

def Packet.Encodable (packet : Packet) : Prop := packet.wireLength < 65536 ∧ packet.FlagsValid

instance (packet : Packet) : Decidable packet.FlagsValid := by unfold Packet.FlagsValid; infer_instance
instance (packet : Packet) : Decidable packet.Encodable := by unfold Packet.Encodable; infer_instance

structure Decoded where
  packet : Packet
  checksum : Word
  padding : List UInt8
  deriving Repr, BEq, DecidableEq

def lengthWord (packet : Packet) : Word := ⟨packet.wireLength % 65536, Nat.mod_lt _ (by decide)⟩

def flagsWord (packet : Packet) : Word :=
  ⟨(if packet.dontFragment then 16384 else 0) + (if packet.moreFragments then 8192 else 0) + packet.offset.val,
    by have := packet.offset.isLt; split <;> split <;> omega⟩

def flagsDF (word : Word) : Bool := decide (16384 ≤ word.val)
def flagsMF (word : Word) : Bool := decide (8192 ≤ word.val % 16384)
def flagsOffset (word : Word) : Fin 8192 := ⟨word.val % 8192, Nat.mod_lt _ (by decide)⟩

theorem flagsWord_bound (packet : Packet) : (flagsWord packet).val < 32768 := by
  change (if packet.dontFragment then 16384 else 0) +
    (if packet.moreFragments then 8192 else 0) + packet.offset.val < 32768
  have := packet.offset.isLt
  split <;> split <;> omega

theorem flags_roundtrip (packet : Packet) :
    flagsDF (flagsWord packet) = packet.dontFragment ∧ flagsMF (flagsWord packet) = packet.moreFragments ∧
      flagsOffset (flagsWord packet) = packet.offset := by
  have bound := packet.offset.isLt
  cases df : packet.dontFragment <;> cases mf : packet.moreFragments <;>
    simp [flagsDF, flagsMF, flagsOffset, flagsWord, df, mf, Nat.add_mod, Nat.mod_eq_of_lt bound]
  all_goals omega

theorem flags_reconstruct (word : Word) (reserved : word.val < 32768) (base : IPv4.Packet) :
    flagsWord ⟨{ base with dontFragment := flagsDF word }, flagsMF word, flagsOffset word⟩ = word := by
  apply Fin.ext
  unfold flagsWord flagsDF flagsMF flagsOffset
  dsimp only
  simp only [decide_eq_true_eq]
  split <;> split <;> omega

def headerPrefix (packet : Packet) : List UInt8 :=
  [69, packet.tos] ++ wordBytes (lengthWord packet) ++ wordBytes packet.identification ++ wordBytes (flagsWord packet) ++
    [packet.ttl, UInt8.ofNat packet.protocol.val]

def headerSuffix (packet : Packet) : List UInt8 := IPv4.headerSuffix packet.toPacket

def headerBytes (packet : Packet) (checksum : Word) : List UInt8 :=
  headerPrefix packet ++ wordBytes checksum ++ headerSuffix packet

@[simp] theorem headerPrefix_length (packet : Packet) : (headerPrefix packet).length = 10 := by simp [headerPrefix]
@[simp] theorem headerSuffix_length (packet : Packet) : (headerSuffix packet).length = 8 := by simp [headerSuffix]
@[simp] theorem headerBytes_length (packet : Packet) (checksum : Word) : (headerBytes packet checksum).length = 20 := by
  simp [headerBytes]

def computedChecksum (packet : Packet) : Word := InternetChecksum.checksum (headerBytes packet 0)

theorem computedChecksum_valid (packet : Packet) : valid (headerBytes packet (computedChecksum packet)) = true := by
  simpa only [computedChecksum, headerBytes, wordBytes_zero] using
    synthesize_valid (headerPrefix packet) (headerSuffix packet) (by simp)

def encode (packet : Packet) : Except String (List UInt8) :=
  if packet.Encodable then .ok (headerBytes packet (computedChecksum packet) ++ packet.payload)
  else .error "The fragment length, flags, or payload alignment is invalid."

def encodeDecoded (value : Decoded) : Except String (List UInt8) :=
  if value.packet.Encodable then
    if valid (headerBytes value.packet value.checksum) = true then
      .ok (headerBytes value.packet value.checksum ++ value.packet.payload ++ value.padding)
    else .error "The IPv4 fragment checksum is invalid."
  else .error "The fragment length, flags, or payload alignment is invalid."

def decode : List UInt8 → Except String Decoded
  | version :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest => do
    if version != 69 then throw "Require IPv4 version four and IHL five."
    let declared := (read16 lh ll).val
    if declared < 20 then throw "The IPv4 fragment length is shorter than its header."
    if rest.length < declared - 20 then throw "The IPv4 fragment is truncated."
    let flags := read16 fh fl
    if flags.val ≥ 32768 then throw "The reserved IPv4 flag must be clear."
    let packet : Packet :=
      ⟨⟨tos, read16 ih il, flagsDF flags, ttl, IPv4.protocolFromByte protocol,
        IPv4.readAddress sa sb sc sd, IPv4.readAddress da db dc dd, rest.take (declared - 20)⟩,
        flagsMF flags, flagsOffset flags⟩
    if !decide packet.FlagsValid then throw "Fragment flags and payload alignment are inconsistent."
    let header := [version, tos, lh, ll, ih, il, fh, fl, ttl, protocol, ch, cl, sa, sb, sc, sd, da, db, dc, dd]
    if !valid header then throw "The IPv4 fragment checksum is invalid."
    return ⟨packet, read16 ch cl, rest.drop (declared - 20)⟩
  | _ => .error "An IPv4 fragment header requires twenty bytes."

theorem decode_headerBytes (packet : Packet) (checksum : Word) (padding : List UInt8)
    (bounded : packet.Encodable) (checked : valid (headerBytes packet checksum) = true) :
    decode (headerBytes packet checksum ++ packet.payload ++ padding) = .ok ⟨packet, checksum, padding⟩ := by
  have length : (lengthWord packet).val = packet.wireLength := Nat.mod_eq_of_lt bounded.1
  have minimum : ¬packet.wireLength < 20 := by unfold Packet.wireLength IPv4.Packet.wireLength; omega
  have available : ¬(packet.payload ++ padding).length < packet.wireLength - 20 := by
    simp only [List.length_append, Packet.wireLength, IPv4.Packet.wireLength]
    omega
  have reserved : ¬(flagsWord packet).val ≥ 32768 := by have := flagsWord_bound packet; omega
  have flags := flags_roundtrip packet
  have parsed : (⟨⟨packet.tos, packet.identification, flagsDF (flagsWord packet), packet.ttl,
      packet.protocol, packet.source, packet.destination, packet.payload⟩,
      flagsMF (flagsWord packet), flagsOffset (flagsWord packet)⟩ : Packet) = packet := by
    rw [flags.1, flags.2.1, flags.2.2]
  have headerValid := checked
  simp only [headerBytes, headerPrefix, headerSuffix, IPv4.headerSuffix, IPv4.addressBytes,
    wordBytes, List.cons_append, List.nil_append] at headerValid
  simp only [headerBytes, headerPrefix, headerSuffix, IPv4.headerSuffix, IPv4.addressBytes, wordBytes,
    List.cons_append, List.nil_append, decode, read16_bytes, IPv4.readAddress_bytes,
    IPv4.protocolFromByte_encode, length]
  rw [ite_eq_right minimum, ite_eq_right available, ite_eq_right reserved]
  simp only [bind, Except.bind, Packet.wireLength, IPv4.Packet.wireLength, Nat.add_sub_cancel,
    List.take_left, List.drop_left, parsed, bounded.2, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, headerValid, pure]
  rfl

theorem decode_encode (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, computedChecksum packet, []⟩ := by
  unfold encode at encoded
  split at encoded
  · cases encoded
    simpa using decode_headerBytes packet (computedChecksum packet) [] (by assumption) (computedChecksum_valid packet)
  · cases encoded

theorem decode_encodeDecoded (value : Decoded) (bytes : List UInt8)
    (encoded : encodeDecoded value = .ok bytes) : decode bytes = .ok value := by
  unfold encodeDecoded at encoded
  split at encoded
  · split at encoded
    · cases encoded
      exact decode_headerBytes value.packet value.checksum value.padding (by assumption) (by assumption)
    · cases encoded
  · cases encoded

private theorem encode_decode_header (tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd : UInt8)
    (rest : List UInt8) (value : Decoded)
    (accepted : decode (69 :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest) = .ok value) :
    encodeDecoded value = .ok (69 :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest) := by
  by_cases short : (read16 lh ll).val < 20
  · simp [decode, short, bind, Except.bind, throw] at accepted
  · by_cases truncated : rest.length < (read16 lh ll).val - 20
    · simp [decode, short, truncated, bind, Except.bind, throw] at accepted
    · by_cases reserved : (read16 fh fl).val ≥ 32768
      · simp [decode, short, truncated, reserved, bind, Except.bind, throw] at accepted
      · let parsed : Packet :=
          ⟨⟨tos, read16 ih il, flagsDF (read16 fh fl), ttl, IPv4.protocolFromByte protocol,
            IPv4.readAddress sa sb sc sd, IPv4.readAddress da db dc dd, rest.take ((read16 lh ll).val - 20)⟩,
            flagsMF (read16 fh fl), flagsOffset (read16 fh fl)⟩
        have length : parsed.wireLength = (read16 lh ll).val := by
          simp only [parsed, Packet.wireLength, IPv4.Packet.wireLength, List.length_take]
          omega
        have lengthSame : lengthWord parsed = read16 lh ll := by
          apply Fin.ext
          change parsed.wireLength % 65536 = (read16 lh ll).val
          rw [length, Nat.mod_eq_of_lt (read16 lh ll).isLt]
        have flagsSame : flagsWord parsed = read16 fh fl := by
          exact flags_reconstruct (read16 fh fl) (by omega) parsed.toPacket
        have headerSame : headerBytes parsed (read16 ch cl) =
            [69, tos, lh, ll, ih, il, fh, fl, ttl, protocol, ch, cl, sa, sb, sc, sd, da, db, dc, dd] := by
          unfold headerBytes headerPrefix headerSuffix IPv4.headerSuffix
          rw [lengthSame, flagsSame]
          simp only [parsed, wordBytes, highByte_read16, lowByte_read16,
            IPv4.addressBytes_readAddress, IPv4.protocolFromByte_bytes]
          rfl
        by_cases consistent : parsed.FlagsValid
        · have bounded : parsed.Encodable := ⟨by rw [length]; exact (read16 lh ll).isLt, consistent⟩
          dsimp only [parsed] at consistent
          by_cases checked : valid (headerBytes parsed (read16 ch cl)) = true
          · have headerChecked := checked
            rw [headerSame] at headerChecked
            change decode (69 :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
              sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest) = _ at accepted
            simp only [decode, short, truncated, reserved, consistent, decide_true, Bool.not_true,
              Bool.false_eq_true, ite_false, headerChecked, bind, Except.bind, pure] at accepted
            cases accepted
            change encodeDecoded ⟨parsed, read16 ch cl, rest.drop ((read16 lh ll).val - 20)⟩ = _
            rw [encodeDecoded, ite_eq_left bounded, ite_eq_left checked]
            apply congrArg Except.ok
            rw [headerSame, List.append_assoc, List.take_append_drop]
            rfl
          · have rejected : valid [69, tos, lh, ll, ih, il, fh, fl, ttl, protocol, ch, cl,
                sa, sb, sc, sd, da, db, dc, dd] = false := by
              rw [← headerSame]
              exact Bool.eq_false_iff.mpr checked
            simp [decode, short, truncated, reserved, consistent, rejected, bind, Except.bind, throw] at accepted
        · dsimp only [parsed] at consistent
          simp [decode, short, truncated, reserved, consistent, bind, Except.bind, throw] at accepted

theorem encode_decode (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := by
  unfold decode at accepted
  split at accepted
  · rename_i version tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd rest
    by_cases selected : version = 69
    · subst version
      exact encode_decode_header tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd rest value accepted
    · simp [selected, bind, Except.bind, throw] at accepted
  · cases accepted

theorem encodeDecoded_valid (value : Decoded) (bytes : List UInt8) (encoded : encodeDecoded value = .ok bytes) :
    value.packet.Encodable ∧ valid (headerBytes value.packet value.checksum) = true := by
  unfold encodeDecoded at encoded
  split at encoded
  · split at encoded
    · exact ⟨by assumption, by assumption⟩
    · cases encoded
  · cases encoded

theorem decode_valid (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    value.packet.Encodable ∧ valid (headerBytes value.packet value.checksum) = true :=
  encodeDecoded_valid value bytes (encode_decode bytes value accepted)

end Netlib.Protocol.IPv4Fragment
